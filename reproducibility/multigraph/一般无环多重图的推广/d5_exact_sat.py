"""Generate exact degree-five CNFs after the 9/20 local-defect bound.

One CNF per sorted marked-degree profile. See degree-five.md for the
equivalence and the local arithmetic that limits the profiles.
"""
from itertools import combinations, product
from pathlib import Path
from hashlib import sha256
from concurrent.futures import ThreadPoolExecutor
import argparse
import json
import subprocess


class CNF:
    def __init__(self):
        self.variables = 0
        self.clauses = []
        self.truth = self.variable()
        self.add(self.truth)

    def variable(self):
        self.variables += 1
        return self.variables

    def add(self, *literals):
        self.clauses.append(tuple(literals))

    def at_least_values(self, literals, k):
        """Represent thresholds 0, ..., k as Boolean literals."""
        previous = [self.truth] + [-self.truth] * k
        for x in literals:
            current = [self.truth]
            for j in range(1, k + 1):
                a, b = previous[j], previous[j - 1]
                z = self.variable()
                # z iff a or (b and x)
                self.add(-a, z)
                self.add(-b, -x, z)
                self.add(-z, a, b)
                self.add(-z, a, x)
                current.append(z)
            previous = current
        return previous

    def cardinality(self, literals, lower, upper):
        if lower > len(literals):
            self.add(-self.truth)
            return
        if not upper:
            for x in literals:
                self.add(-x)
            return
        k = max(lower, min(len(literals), upper + 1))
        values = self.at_least_values(literals, k)
        if lower:
            self.add(values[lower])
        if upper < len(literals):
            self.add(-values[upper + 1])

    def dump(self, path):
        body = ''.join(' '.join(map(str, c)) + ' 0\n' for c in self.clauses)
        path.write_text(f'p cnf {self.variables} {len(self.clauses)}\n' + body, encoding='ascii', newline='\n')


def profiles():
    # Every vertex contributes at least 5-h(v) to the defect, so n <= 18.
    for n in range(12, 19):
        for low in product(range(n + 1), repeat=4):
            n5 = n - sum(low)
            if n5 < 0:
                continue
            counts = low + (n5,)
            if sum((h + 1) * counts[h] for h in range(5)) != 60:
                continue
            defect = sum((h + 1) * (4 - h) * counts[h] for h in range(5))
            if defect > 32:
                continue
            yield tuple(h + 1 for h in range(5) for _ in range(counts[h])), (32 - defect) // 6


def instance(degrees, triangle_bound, degree_limit=5, extra_cuts=False):
    n = len(degrees)
    f = CNF()
    pairs = tuple(combinations(range(n), 2))
    mark = {e: f.variable() for e in pairs}
    # Edges at saturated marked vertices cannot additionally act as unmarked
    # edges. For the other pairs we use a separate host-presence variable.
    host = {
        (u, v): mark[u, v] if max(degrees[u], degrees[v]) == degree_limit else f.variable()
        for u, v in pairs
    }
    for e in pairs:
        if host[e] != mark[e]:
            f.add(-mark[e], host[e])

    def lookup(table, u, v):
        return table[min(u, v), max(u, v)]

    for i, h in enumerate(degrees):
        incident = [e for e in pairs if i in e]
        f.cardinality([mark[e] for e in incident], h, h)
        f.cardinality([host[e] for e in incident], 0, degree_limit)

    for u, v, x, y in combinations(range(n), 4):
        for (a, b), (c, d) in (
            ((u, v), (x, y)), ((u, x), (v, y)), ((u, y), (v, x))
        ):
            f.add(
                -mark[a, b], -mark[c, d],
                *(lookup(host, i, j) for i in (a, b) for j in (c, d))
            )

    triangles = []
    for u, v, w in combinations(range(n), 3):
        triangle = (mark[u, v], mark[u, w], mark[v, w])
        if not triangle_bound:
            f.add(*(-x for x in triangle))
        else:
            t = f.variable()
            # Only the forward implication is needed for an upper bound.
            f.add(*(-x for x in triangle), t)
            triangles.append(t)
    if triangle_bound:
        f.cardinality(triangles, 0, triangle_bound)

    if extra_cuts:
        add_known_cuts(f, degrees, degree_limit, triangle_bound, mark, host, lookup)

    # Among labels with the prescribed marked degrees, take a lexicographic
    # maximum of the upper triangular marked adjacency vector. Swapping
    # consecutive equal-degree vertices shows these comparisons are necessary
    # for that maximum. Hence at least one representative survives.
    for i in range(n - 1):
        j = i + 1
        if degrees[i] != degrees[j]:
            continue
        prefix = f.truth
        for k in range(n):
            if k in (i, j):
                continue
            a, b = lookup(mark, i, k), lookup(mark, j, k)
            f.add(-prefix, a, -b)
            next_prefix = f.variable()
            f.add(-prefix, -a, -b, next_prefix)
            f.add(-prefix, a, b, next_prefix)
            f.add(-next_prefix, prefix)
            f.add(-next_prefix, -a, b)
            f.add(-next_prefix, a, -b)
            prefix = next_prefix
    return f


def add_known_cuts(f, degrees, degree_limit, triangle_bound, mark, host, lookup):
    n = len(degrees)
    largest = []
    for i, h in enumerate(degrees):
        if h == degree_limit:
            largest.append(f.truth)
        else:
            edges = [lookup(host, i, j) for j in range(n) if i != j]
            largest.append(f.at_least_values(edges, degree_limit)[degree_limit])

    # If removing a vertex or an adjacent pair left no vertex of degree
    # degree_limit, the even uniform result at degree_limit - 1 would apply.
    # The removal costs at most 2*degree_limit-1 marks for the allowed pairs.
    for i in range(n):
        nonneighbors = []
        for j in range(n):
            if i == j:
                continue
            z = f.variable()
            f.add(-z, largest[j])
            f.add(-z, -lookup(host, i, j))
            nonneighbors.append(z)
        f.add(*nonneighbors)
    for i, j in combinations(range(n), 2):
        nonneighbors = []
        for k in range(n):
            if k == i or k == j:
                continue
            z = f.variable()
            f.add(-z, largest[k])
            f.add(-z, -lookup(host, i, k))
            f.add(-z, -lookup(host, j, k))
            nonneighbors.append(z)
        if degrees[i] + degrees[j] <= 2 * degree_limit - 1:
            f.add(*nonneighbors)
        else:
            f.add(-host[i, j], *nonneighbors)

    target = (5 * degree_limit**2 - 2 * degree_limit + 1) // 4 + 1
    for r in range(4, min(degree_limit+1, n)+1):
        if (r-1) * (r*degree_limit - r*(r-1)//2 - target) + r*(degree_limit-r+1)*(degree_limit-1) < 0:
            for clique in combinations(range(n), r):
                f.add(*(-mark[e] for e in combinations(clique, 2)))
            break

    # A triangle-free saturated induced strong graph is bipartite for odd
    # degree. Otherwise its shortest odd cycle is C5 (2K2-free), and the
    # saturated-cycle lemma would force an even maximum degree.
    if triangle_bound == 0:
        side = {i: f.variable() for i, h in enumerate(degrees) if h == degree_limit}
        for u, v in combinations(side, 2):
            f.add(-mark[u, v], side[u], side[v])
            f.add(-mark[u, v], -side[u], -side[v])


def solve(solver, out, name):
    cnf, proof = out / (name + '.cnf'), out / (name + '.lrat')
    logfile = out / (name + '.log')
    with logfile.open('wb') as log:
        code = subprocess.call(
            [str(solver), '--lrat', '--no-binary', '--check', '--checkproof=2', str(cnf), str(proof)],
            stdout=log, stderr=subprocess.STDOUT,
        )
    print(f'{name}: {code}', flush=True)
    return name, code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--solver', type=Path)
    parser.add_argument('--jobs', type=int, default=3)
    parser.add_argument('--select', nargs='*')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    for degrees, triangle_bound in profiles():
        name = f'n{len(degrees):02d}_' + ''.join(map(str, [degrees.count(h) for h in range(1, 6)]))
        if args.select and name not in args.select:
            continue
        cnf = args.out / (name + '.cnf')
        f = instance(degrees, triangle_bound)
        f.dump(cnf)
        rows.append(dict(name=name, degrees=degrees, triangle_bound=triangle_bound,
                         variables=f.variables, clauses=len(f.clauses), sha256=sha256(cnf.read_bytes()).hexdigest()))
    (args.out / 'instances.json').write_text(json.dumps(rows, indent=2) + '\n', encoding='utf-8')
    if args.solver:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            result = dict(pool.map(lambda row: solve(args.solver, args.out, row['name']), rows))
        (args.out / 'status.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
