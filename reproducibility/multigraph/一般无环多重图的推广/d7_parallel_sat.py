"""Finite CNFs for the degree-seven parallel-mark subcase.

See delta7_parallel_reduction.md for the support bound and encoding.
The only external executable used by --solver is a proof-logging SAT solver.
"""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import argparse
import gzip
import json
import shutil
import subprocess

from d5_exact_sat import CNF
from d7_bipartite_ore_coupled import bound, local_bound


def cases():
    for s, t in product(range(6), repeat=2):
        if s <= t and s + t >= 3:
            first = (1,) * s + (0,) * (5 - s)
            second = (1,) * t + (0,) * (5 - t)
            yield f'q10_l{s}_r{t}', first, second, None
    for s, t in product(range(5), range(6)):
        if s + t >= 6:
            first = (1,) * s + (0,) * (4 - s)
            second = (1,) * t + (0,) * (5 - t)
            yield f'q9a_l{s}_r{t}', first, second, None
    for s, t in product(range(4), range(6)):
        if s + t + 2 >= 7:
            first = (2,) + (1,) * s + (0,) * (3 - s)
            second = (1,) * t + (0,) * (5 - t)
            yield f'q9b_l{s}_r{t}', first, second, None
    for s, t, x, y in product(range(5), range(5), range(2), range(2)):
        if (x, s) <= (y, t) and s + t + x + y >= 7:
            first = (1,) * s + (0,) * (4 - s)
            second = (1,) * t + (0,) * (4 - t)
            yield f'q9c_l{s}{x}_r{t}{y}', first, second, (x, y)


class GraphCNF(CNF):
    def clause(self, *lits):
        if self.truth in lits:
            return
        unique = dict.fromkeys(lits)
        unique.pop(-self.truth, None)
        if any(-lit in unique for lit in unique):
            return
        self.add(*unique)

    def conjunction(self, a, b):
        if a == b or b == self.truth or a == -self.truth:
            return a
        if a == self.truth or b == -self.truth:
            return b
        if a == -b:
            return -self.truth
        z = self.variable()
        self.clause(-z, a)
        self.clause(-z, b)
        self.clause(z, -a, -b)
        return z

    def disjunction(self, a, b):
        return -self.conjunction(-a, -b)

    def any(self, literals):
        out = -self.truth
        for lit in literals:
            out = self.disjunction(out, lit)
        return out

    def count(self, literals, upper_threshold):
        ones = literals.count(self.truth)
        reduced = [x for x in literals if abs(x) != self.truth]
        extent = min(upper_threshold - ones, len(reduced))
        values = [self.truth] + [-self.truth] * max(0, extent)
        for i, x in enumerate(reduced, start=1):
            for j in range(min(i, extent), 0, -1):
                values[j] = self.disjunction(values[j], self.conjunction(values[j-1], x))
        return [self.truth if j <= ones else
                values[j - ones] if j - ones < len(values) else -self.truth
                for j in range(upper_threshold + 1)]

    def at_most(self, literals, upper):
        if upper < 0:
            self.add()
        elif upper < len(literals):
            self.clause(-self.count(literals, upper + 1)[upper + 1])

    def imply_at_most_one(self, condition, literals):
        has = -self.truth
        for lit in literals:
            self.clause(-condition, -has, -lit)
            has = self.disjunction(has, lit)


def instance(case, use_union=True, w_limit=None):
    name, first, second, shared = case
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    support = 2 + len(first) + len(second) + (shared is not None)
    q = support - 2
    A = range(2, support)
    spokes_marked = sum(first) + sum(second) + (sum(shared) if shared else 0)
    spokes = len(first) + len(second) + (len(shared) if shared else 0) + first.count(2)
    p = spokes - spokes_marked
    budget = 7*q - 57 - p
    lower_cross = 57 - spokes_marked - budget
    if w_limit is None:
        w_limit = 15 if lower_cross >= 49 else 16
    n = support + w_limit
    W = range(support, n)

    root_records = {}
    group = [-1, -2]
    for root, values, start in ((0, first, 2), (1, second, 2 + len(first))):
        for a, mark in enumerate(values, start=start):
            root_records[root, a] = (yes, yes if mark else no, yes if mark == 2 else no)
            group.append((root, mark))
    if shared is not None:
        for root, mark in enumerate(shared):
            root_records[root, support - 1] = (yes, yes if mark else no, no)
        group.append((2, 0))
    group.extend([(3, 0)] * w_limit)

    edge, mark, double = {}, {}, {}
    possible_marked = []
    for a, b in combinations(range(n), 2):
        if (a, b) == (0, 1):
            e, m, d = yes, yes, yes
        elif a < 2:
            e, m, d = root_records.get((a, b), (no, no, no))
        elif b < support or a < support:
            e, m, d = (f.variable() for _ in range(3))
            f.clause(-d, m)
            f.clause(-m, e)
        else:
            e, m, d = f.variable(), no, no
        edge[a,b], mark[a,b], double[a,b] = e, m, d
        if m != no:
            possible_marked.append((a,b))

    def get(table, u, v):
        if u == v:
            return no
        return table[min(u,v), max(u,v)]

    adjacency_thresholds = []
    defect = []
    for v in range(n):
        literals = [get(table, v, u) for u in range(n) if u != v
                    for table in (edge, double)]
        values = f.count(literals, 8)
        f.clause(-values[8])
        adjacency_thresholds.append(values)
        if v in A:
            defect.extend(-values[h] for h in range(1,8))
    for a,b in combinations(A,2):
        defect.extend((edge[a,b], double[a,b], f.conjunction(edge[a,b], -mark[a,b])))
    for a,w in product(A,W):
        defect.append(f.conjunction(edge[a,w], -mark[a,w]))
    f.at_most(defect, budget)

    for w in W:
        marked_incidence = [mark[a,w] for a in A]
        active = f.variable()
        f.clause(-active, *marked_incidence)
        for u in range(2,n):
            if u != w:
                f.clause(-get(edge,w,u), active)

    for (a,b), (c,d) in combinations(possible_marked,2):
        if a in (c,d) or b in (c,d):
            continue
        f.clause(-mark[a,b], -mark[c,d],
                 *(get(edge,u,v) for u in (a,b) for v in (c,d)))

    cross_mark = [table[a,w] for a,w in product(A,W) for table in (mark,double)]
    cross_count = f.count(cross_mark,49)
    f.clause(-cross_count[49])
    f.clause(cross_count[lower_cross])
    internal_mark = [table[a,b] for a,b in combinations(A,2) for table in (mark,double)]
    internal_lower = max(0,57-spokes_marked-48)
    f.clause(f.count(internal_mark,internal_lower)[internal_lower])

    root_incidence = {
        a: sum(int(get(table,i,a) == yes) for i in range(2) for table in (edge,double))
        for a in A
    }
    at_marked_degree, at_distinct_degree = {}, {}
    for v in range(2,n):
        opposite = W if v in A else A
        at_marked_degree[v] = f.count(
            [get(table,v,u) for u in opposite for table in (mark,double)], 8)
        at_distinct_degree[v] = f.count([get(mark,v,u) for u in opposite], 8)
    at_maximum = [
        f.any(at_marked_degree[v][h] for v in range(2,n)) for h in range(9)
    ]
    for D in range(1,8):
        limit = bound(6,7,13,D,q)
        f.clause(-at_maximum[D],at_maximum[D+1],-cross_count[limit+1])
        for v in range(2,n):
            side = int(v in W)
            fixed = root_incidence.get(v,0)
            for host in range(D,8-fixed):
                for distinct in range((D+1)//2,D+1):
                    local = local_bound(6,7,13,D,q,side,host,distinct)
                    if local >= limit:
                        continue
                    adj = adjacency_thresholds[v]
                    ds = at_distinct_degree[v]
                    f.clause(at_maximum[D+1],-at_marked_degree[v][D],
                             -adj[host+fixed],adj[host+fixed+1],
                             -ds[distinct],ds[distinct+1],-cross_count[local+1])
    ore_maximizers = [
        f.conjunction(mark[a,w],
                      f.conjunction(adjacency_thresholds[a][7],
                                    adjacency_thresholds[w][7]))
        for a,w in product(A,W) if root_incidence[a] == 1
    ]
    f.clause(-cross_count[42], *ore_maximizers)

    if use_union:
        for (u,v), is_double in double.items():
            if is_double == no:
                continue
            hu, hv = adjacency_thresholds[u], adjacency_thresholds[v]
            f.clause(-is_double, hu[6])
            f.clause(-is_double, hv[6])
            f.clause(-is_double, hu[7], hv[7])
            losses = []
            for z in range(n):
                if z in (u,v):
                    continue
                common = f.conjunction(get(edge,u,z), get(edge,v,z))
                losses.extend((common, get(double,u,z), get(double,v,z)))
            for loss in losses:
                f.clause(-is_double, -loss, hu[7])
                f.clause(-is_double, -loss, hv[7])
            f.imply_at_most_one(is_double, losses)

    # Choose a lexicographic maximum of the full pair-color sequence under
    # permutations within equal root profiles and among exterior vertices.
    for u in range(2,n-1):
        v = u+1
        if group[u] != group[v]:
            continue
        prefix = yes
        for z in range(n):
            if z in (u,v):
                continue
            for table in (mark,double,edge):
                a,b = get(table,u,z),get(table,v,z)
                if a == b:
                    continue
                f.clause(-prefix, a, -b)
                if a == -b:
                    prefix = no
                else:
                    eq = f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                    prefix = f.conjunction(prefix, eq)
    return f, dict(name=name, q=q, w=w_limit, p=p, budget=budget,
                   minimum_cross_marks=lower_cross,
                   marked_variables=[(u,v,m,double[u,v]) for (u,v),m in mark.items()
                                     if m != no],
                   host_variables=[(u,v,e,double[u,v]) for (u,v),e in edge.items()
                                   if e != no])


def solve(args, case):
    f,row = instance(case, not args.no_union, args.w_limit)
    name = case[0]
    path = args.out / (name + ".cnf")
    if args.w_limit is None and not args.no_union:
        cached = args.out / (name + ".result.json")
        if cached.exists():
            old = json.loads(cached.read_text())
            if old.get("result") == "VERIFIED_UNSAT":
                return old
    f.dump(path)
    row.update(variables=f.variables, clauses=len(f.clauses), sha256=sha256(path.read_bytes()).hexdigest())
    (args.out / (name + ".encoding.json")).write_text(json.dumps(row) + "\n")
    if args.solver is None:
        print(name, f.variables, len(f.clauses), flush=True)
        return row
    proof = args.out / (name + ".lrat")
    log = args.out / (name + ".log")
    with log.open("wb") as stream:
        try:
            code = subprocess.run(
                [str(args.solver), "--lrat", "--no-binary", str(path), str(proof)],
                stdout=stream, stderr=subprocess.STDOUT, timeout=args.timeout
            ).returncode
        except subprocess.TimeoutExpired:
            code = None
    result = dict(name=name, code=code, result="SAT" if code == 10 else
                  "UNSAT" if code == 20 else "UNKNOWN")
    if code == 20 and args.checker is not None:
        check = subprocess.run(
            [str(args.checker), path.name, proof.name],
            cwd=args.out, text=True, capture_output=True
        )
        result["replay_stdout"] = check.stdout
        result["replay_stderr"] = check.stderr
        if check.returncode == 0:
            result["result"] = "VERIFIED_UNSAT"
            result["cnf_sha256"] = row["sha256"]
            result["lrat_sha256"] = file_digest(proof)
        else:
            result["result"] = "CHECKER_FAILED"
    print(name, result["result"], flush=True)
    if args.gzip and result["result"] == "VERIFIED_UNSAT":
        for original in (path,proof):
            target = original.with_suffix(original.suffix+".gz")
            with original.open("rb") as source, target.open("wb") as dest:
                with gzip.GzipFile(filename="",fileobj=dest,mode="wb",compresslevel=1,mtime=0) as zipped:
                    shutil.copyfileobj(source,zipped)
            original.unlink()
    (args.out / (name + ".result.json")).write_text(json.dumps(result) + "\n")
    return result


def file_digest(path):
    with path.open("rb") as stream:
        digest = sha256()
        for block in iter(lambda: stream.read(1024*1024),b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--select", nargs="*")
    parser.add_argument("--family")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--w-limit", type=int)
    parser.add_argument("--no-union", action="store_true")
    parser.add_argument("--gzip", action="store_true")
    args = parser.parse_args()
    rows = list(cases())
    if args.list:
        for name, *_ in rows:
            print(name)
        return
    if args.select:
        rows = [row for row in rows if row[0] in args.select]
    if args.family:
        rows = [row for row in rows if row[0].startswith(args.family)]
    args.out.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda row: solve(args,row), rows))
    (args.out / "summary.json").write_text(json.dumps(results,indent=2) + "\n")


if __name__ == "__main__":
    main()

