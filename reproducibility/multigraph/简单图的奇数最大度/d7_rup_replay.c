/* Replay ASCII LRAT restricted to positive RUP hints. */
#include "source_snapshot/reproducibility/verifiers/c_runtime.h"

#ifdef FGST_NO_C_HEADERS
extern void *realloc(void *, size_t);
#endif

enum { end_token = 256, integer_token, buffer_size = 1 << 20 };
static FILE *input;
static unsigned char buffer[buffer_size];
static SZ cursor, length;
static int lookahead;
static int number;
static unsigned proof_row;

typedef struct {
    int count;
    int literals[];
} Clause;

static Clause **database;
static SZ capacity;
static int *staged;
static SZ staged_capacity;
static unsigned *marks;
static signed char *assigned;
static unsigned generation;
static int variables;

static void reject(const char *description) {
    printf("LRAT check failed at proof row %u: %s\n", proof_row, description);
    exit(1);
}

static int byte(void) {
    if (cursor == length) {
        length = fread(buffer, 1, sizeof buffer, input);
        cursor = 0;
        if (!length) return -1;
    }
    return buffer[cursor++];
}

static void reset(FILE *stream) {
    input = stream;
    cursor = length = 0;
    lookahead = byte();
}

static int next_token(void) {
    while (lookahead >= 0 && lookahead <= 32) lookahead = byte();
    if (lookahead < 0) return end_token;
    int sign = 1;
    if (lookahead == '-') {
        sign = -1;
        lookahead = byte();
        if (lookahead < '0' || lookahead > '9') reject("invalid negative integer");
    }
    if (lookahead < '0' || lookahead > '9') {
        int token = lookahead;
        lookahead = byte();
        return token;
    }
    int value = 0;
    while (lookahead >= '0' && lookahead <= '9') {
        int digit = lookahead - '0';
        if (value > (2147483647 - digit) / 10) reject("integer too large");
        value = 10 * value + digit;
        lookahead = byte();
    }
    if (lookahead > 32) reject("missing integer delimiter");
    number = sign * value;
    return integer_token;
}

static int get_int(void) {
    if (next_token() != integer_token) reject("expected integer");
    return number;
}

static void *resize(void *old, SZ bytes) {
    void *new = realloc(old, bytes);
    if (!new) reject("allocation failed");
    return new;
}

static void ensure_id(int id) {
    SZ old = capacity;
    if ((SZ) id < capacity) return;
    while ((SZ) id >= capacity) capacity = capacity ? 2 * capacity : 1024;
    database = resize(database, capacity * sizeof *database);
    for (SZ i = old; i < capacity; i++) database[i] = 0;
}

static int read_clause(int first) {
    int count = 0;
    for (int literal = first; literal; literal = get_int()) {
        if (literal < -variables || literal > variables) reject("literal out of range");
        if ((SZ) count == staged_capacity) {
            staged_capacity = staged_capacity ? 2 * staged_capacity : 16;
            staged = resize(staged, staged_capacity * sizeof *staged);
        }
        staged[count++] = literal;
    }
    return count;
}

static void store_clause(int id, int count) {
    ensure_id(id);
    if (database[id]) reject("clause ID repeats");
    Clause *clause = malloc(sizeof *clause + (SZ) count * sizeof(int));
    if (!clause) reject("allocation failed");
    clause->count = count;
    for (int i = 0; i < count; i++) clause->literals[i] = staged[i];
    database[id] = clause;
}

static Clause *existing(int id) {
    if (id <= 0 || (SZ) id >= capacity || !database[id]) reject("invalid clause hint or deletion");
    return database[id];
}

/* Return 1 for true, -1 for false, 0 for unset in this RUP check. */
static int truth(int literal) {
    int index = literal > 0 ? literal : -literal;
    if (marks[index] != generation) return 0;
    return literal > 0 ? assigned[index] : -assigned[index];
}

static void assume(int literal) {
    int index = literal > 0 ? literal : -literal;
    marks[index] = generation;
    assigned[index] = literal > 0 ? 1 : -1;
}

static int propagate(Clause *clause) {
    int unit = 0;
    for (int i = 0; i < clause->count; i++) {
        int literal = clause->literals[i];
        int value = truth(literal);
        if (value > 0) return 0;
        if (value == 0) {
            if (unit && unit != literal) return 0;
            unit = literal;
        }
    }
    if (unit) {
        assume(unit);
        return 0;
    }
    return 1;
}

static int read_cnf(const char *path) {
    FILE *stream = fopen(path, "rb");
    if (!stream) reject("cannot open CNF");
    reset(stream);
    if (next_token() != 'p' || next_token() != 'c' ||
        next_token() != 'n' || next_token() != 'f') reject("invalid DIMACS header");
    variables = get_int();
    int count = get_int();
    if (variables < 1 || count < 1) reject("invalid CNF dimensions");
    for (int id = 1; id <= count; id++) {
        int size = read_clause(get_int());
        store_clause(id, size);
    }
    if (next_token() != end_token) reject("extra DIMACS data");
    fclose(stream);
    marks = calloc((SZ) variables + 1, sizeof *marks);
    assigned = malloc(((SZ) variables + 1) * sizeof *assigned);
    if (!marks || !assigned) reject("allocation failed");
    return count;
}

int main(int argc, char **argv) {
    if (argc != 3) reject("usage: rup_replay CNF LRAT");
    int last = read_cnf(argv[1]);
    FILE *proof = fopen(argv[2], "rb");
    if (!proof) reject("cannot open proof");
    reset(proof);
    unsigned added = 0, deleted = 0;
    int empty = 0, token;
    while ((token = next_token()) != end_token) {
        proof_row++;
        if (token != integer_token || number <= 0) reject("invalid line ID");
        int id = number;
        token = next_token();
        if (token == 'd') {
            for (int key = get_int(); key; key = get_int()) {
                free(existing(key));
                database[key] = 0;
                deleted++;
            }
            continue;
        }
        if (token != integer_token || id <= last) reject("invalid addition ID or literal");
        int size = read_clause(number);
        if (++generation == 0) reject("too many proof additions");
        int conflict = 0;
        for (int j = 0; j < size && !conflict; j++) {
            int literal = -staged[j];
            if (truth(literal) < 0) conflict = 1;
            else assume(literal);
        }
        for (int hint = get_int(); hint; hint = get_int()) {
            Clause *reason = existing(hint);
            if (!conflict) conflict = propagate(reason);
        }
        if (!conflict) reject("addition did not produce a RUP conflict");
        store_clause(id, size);
        last = id;
        added++;
        if (!size) empty = 1;
    }
    if (!empty) reject("proof contains no empty clause");
    fclose(proof);
    printf("{\"added\":%u,\"deleted\":%u}\n", added, deleted);
    return 0;
}

