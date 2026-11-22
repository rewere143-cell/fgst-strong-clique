"""Independently replay the positive LRAT unit-propagation certificates.

This checker does not call a SAT solver. All clause additions in the
supplied proofs use reverse unit propagation. RAT additions are rejected.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import json

from d5_exact_sat import instance, profiles


def read_cnf(path):
    with path.open(encoding='ascii') as file:
        header = next(file).split()
        if header[:2] != ['p', 'cnf'] or len(header) != 4:
            raise ValueError('Invalid DIMACS header')
        var_count, clause_count = map(int, header[2:])
        database = {}
        for i, line in enumerate(file, 1):
            row = tuple(map(int, line.split()))
            if not row or row[-1] != 0 or any(not 0 < abs(x) <= var_count for x in row[:-1]):
                raise ValueError('Invalid DIMACS clause')
            database[i] = row[:-1]
        if len(database) != clause_count:
            raise ValueError('DIMACS clause count differs')
        return database, var_count


def rup(clause, hints, database):
    assignments = set()
    for literal in clause:
        if literal in assignments:
            return True
        assignments.add(-literal)
    for hint in hints:
        used = database[hint]
        pending = set()
        for literal in used:
            if literal in assignments:
                # A satisfied clause does not contribute a propagation.
                break
            if -literal not in assignments:
                pending.add(literal)
        else:
            if not pending:
                return True
            if len(pending) == 1:
                assignments.update(pending)
    return False


def replay(cnf, proof):
    database, variables = read_cnf(cnf)
    last = len(database)
    added = deleted = 0
    empty_seen = False
    with proof.open(encoding='ascii') as file:
        for row, line in enumerate(file, 1):
            tokens = line.split()
            clause_id = int(tokens[0])
            if tokens[1] == 'd':
                if tokens[-1] != '0':
                    raise ValueError(f'Line {row}: invalid deletion')
                for key in map(int, tokens[2:-1]):
                    del database[key]
                    deleted += 1
                continue
            if not clause_id > last:
                raise ValueError(f'Line {row}: repeated or out-of-order ID')
            data = list(map(int, tokens[1:]))
            sep = data.index(0)
            clause, hints = tuple(data[:sep]), data[sep + 1:-1]
            if data[-1] != 0 or any(x <= 0 or x not in database for x in hints):
                raise ValueError(f'Line {row}: invalid or unsupported proof hints')
            if any(abs(x) > variables for x in clause) or not rup(clause, hints, database):
                raise ValueError(f'Line {row}: reverse unit propagation failed')
            database[clause_id] = clause
            last = clause_id
            added += 1
            if not clause:
                empty_seen = True
    if not empty_seen:
        raise ValueError('Missing empty clause')
    return dict(added=added, deleted=deleted)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    results = []
    for degrees, triangles in profiles():
        name = f'n{len(degrees):02d}_' + ''.join(map(str, [degrees.count(h) for h in range(1, 6)]))
        cnf, proof = (args.directory / (name + suffix) for suffix in ('.cnf', '.lrat'))
        # Recreate the model and compare it with the proof's exact input.
        generated = instance(degrees, triangles)
        raw = cnf.read_bytes()
        words = raw.decode('ascii').splitlines()
        expected_header = f'p cnf {generated.variables} {len(generated.clauses)}'
        if words[0] != expected_header:
            raise ValueError(f'{name}: generated header differs')
        actual = [tuple(map(int, line.split())) for line in words[1:]]
        if len(actual) != len(generated.clauses) or any(
            x != y + (0,) for x, y in zip(actual, generated.clauses)
        ):
            raise ValueError(f'{name}: CNF differs from its regenerated model')
        count = replay(cnf, proof)
        results.append(dict(name=name, **count, cnf_sha256=sha256(raw).hexdigest(),
                            lrat_sha256=sha256(proof.read_bytes()).hexdigest()))
    print(json.dumps(dict(verified=len(results), all_unsat=True, results=results), indent=2))


if __name__ == '__main__':
    main()
