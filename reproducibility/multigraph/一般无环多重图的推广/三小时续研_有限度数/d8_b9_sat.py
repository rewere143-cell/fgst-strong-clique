"""Generate and independently replay D=8, b=9 exterior profile CNFs."""

import argparse
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
import json
from math import comb
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from d8_b9_exterior import exterior_shapes
from d8_b9_large_exterior import profiles
from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_parallel_sat import bounded_solve, gzip_file
from d8_repeat_core_sat import require_at_least, require_exactly


def lex_maximum(formula, left, right):
    """Require the first bit vector to be lexicographically at least the second."""
    equal = formula.truth
    for a, b in zip(left, right):
        if a == b:
            continue
        formula.clause(-equal, a, -b)
        same = formula.disjunction(formula.conjunction(a, b), formula.conjunction(-a, -b))
        equal = formula.conjunction(equal, same)


WITNESS_STRUCTURES = {
    "p0": (),
    "p1": ((0,1),),
    "p2path": ((0,1),(1,2)),
    "p2disjoint": ((0,1),(2,3)),
}


def fixed_symmetries(structure, b):
    if structure == "p0":
        return [((2*i, 2*i+1),) for i in range(b)] + [
            ((2*i, 2*i+2), (2*i+1, 2*i+3)) for i in range(b-1)
        ]
    if structure == "p1":
        near, flips, relabel = 2, ((0,1),), [((0,1),)]
    elif structure == "p2path":
        near, flips, relabel = 3, ((0,1,2),), [((0,2),)]
    elif structure == "p2disjoint":
        near, flips, relabel = 4, ((0,1),(2,3)), [((0,1),),((2,3),),((0,2),(1,3))]
    else:
        raise ValueError(f"unsupported witness structure {structure!r}")
    return [tuple((2*i,2*i+1) for i in comp) for comp in flips] + [
        ((2*i,2*i+1),) for i in range(near,b)
    ] + [
        tuple((2*i+s,2*j+s) for i,j in group for s in range(2)) for group in relabel
    ] + [
        ((2*i,2*i+2),(2*i+1,2*i+3)) for i in range(near,b-1)
    ]


def instance(exterior_edges, exterior_hits, improve=False, b=9, structure=None,
             tighten=False, budget_cut=False, compact=False):
    projected = 81-b
    core = 2 * b
    order = core + len(exterior_hits)
    outside = set(range(core, order))
    flexible = exterior_edges is None
    ext_edge = {(x + core, y + core) for x, y in (exterior_edges or ())}
    ext_degree = {
        x: 8 if flexible else exterior_hits[x - core] + sum(x in edge for edge in ext_edge)
        for x in outside
    }
    degree = {**{x: 7 for x in range(core)}, **ext_degree}
    full = {x for x in outside if ext_degree[x] == 8}
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    pairs = tuple(combinations(range(order), 2))
    host, mark = {}, {}
    blues, possible = [], []
    doubled = None if structure is None else set(WITNESS_STRUCTURES[structure])
    if compact:
        assert doubled is not None
        terminals = {(i,j): tuple(f.variable() for _ in range(3))
                     for i,j in combinations(range(b),2) if (i,j) not in doubled}
        mark_flags = [yes]*b + [flat[2] for flat in terminals.values()]
    for u, v in pairs:
        if v < core and u // 2 == v // 2:
            h = m = yes
        elif compact and v < core and (u//2,v//2) in terminals:
            first, second, selected = terminals[u//2,v//2]
            h = f.conjunction(first if u%2 else -first,second if v%2 else -second)
            m = f.conjunction(h,selected)
        else:
            if doubled and v<core and (u//2,v//2) in doubled:
                h = yes if u%2 == v%2 else no
            else:
                h = (yes if (u, v) in ext_edge else no) if u in outside and not flexible else f.variable()
            can_mark = h != no and degree[u] + degree[v] - 2 >= 11
            if u in outside and exterior_hits[u - core] + exterior_hits[v - core] < b:
                can_mark = False
            if u < core <= v and exterior_hits[v - core] < b - 5:
                can_mark = False
            m = f.variable() if can_mark else no
            f.clause(-m, h)
            if compact and m != no:
                mark_flags.append(m)
        if m != no:
            possible.append((u, v))
        if not compact:
            blue = f.conjunction(h, -m)
            if blue != no:
                blues.append(blue)
        host[u, v], mark[u, v] = h, m

    def get(table, u, v):
        if u == v:
            return no
        return table[min(u, v), max(u, v)]

    def edge(u, v):
        return get(host, u, v)

    def red(u, v):
        return get(mark, u, v)

    # A third vertex cannot see both ends of any doubled bundle.
    for i in range(b):
        u, v = 2 * i, 2 * i + 1
        for w in range(order):
            if w not in (u, v):
                f.clause(-edge(u, w), -edge(v, w))
    # All bundles witness each other. Total degrees and cut sizes fix p.
    for i, j in combinations(range(b), 2):
        witnesses = [edge(u, v) for u in (2*i, 2*i+1) for v in (2*j, 2*j+1)]
        if doubled is not None and (i,j) not in doubled:
            if not compact:
                require_exactly(f, witnesses, 1)
        else:
            f.clause(*witnesses)
    red_degree = {}
    host_defect = []
    full_test = {}
    for u in range(order):
        adjacency = [edge(u, v) for v in range(order) if u != v]
        if flexible and u in outside:
            require_exactly(f, [edge(u, v) for v in range(core)], exterior_hits[u-core])
            values = f.count(adjacency, 9)
            f.clause(-values[9])
            host_defect.extend(-lit for lit in values[exterior_hits[u-core]+1:9])
            full_test[u] = values[8]
        else:
            require_exactly(f, adjacency, degree[u])
        red_degree[u] = f.count([red(u, v) for v in range(order) if u != v], degree[u]+1)
    if flexible:
        require_at_least(f, list(full_test.values()), 3)
        if not compact:
            require_exactly(f, blues+blues+host_defect, sum(degree.values()) - 2*projected)
        for u in range(order):
            f.clause(*(f.conjunction(full_test[v], -edge(u, v)) for v in sorted(outside) if u != v))
        if tighten:
            total = sum(exterior_hits)
            if b == 9:
                candidates = next(eligible for hits, eligible, _ in profiles(len(exterior_hits), total)
                                  if hits == tuple(exterior_hits))
            else:
                from d8_b8_exterior import profiles as eight_profiles
                candidates = next(eligible for hits, eligible in eight_profiles(len(exterior_hits),(40-total)//2)
                                  if hits == tuple(exterior_hits))
            for v in sorted(outside):
                if v-core not in candidates:
                    f.clause(-full_test[v])
    elif not compact:
        require_exactly(f, blues, sum(degree.values())//2 - projected)
    if compact:
        require_exactly(f, mark_flags, projected)
    if doubled is not None:
        for i in range(b):
            cut = [edge(u,v) for u in (2*i,2*i+1) for v in sorted(outside)]
            require_exactly(f, cut, 13-b-sum(i in e for e in doubled))
    for u in outside:
        f.clause(red_degree[u][1])
    for (u, v), (x, y) in combinations(possible, 2):
        if u not in (x, y) and v not in (x, y):
            f.clause(-red(u, v), -red(x, y), edge(u, x), edge(u, y), edge(v, x), edge(v, y))
    for u, v, w in combinations(range(order), 3):
        f.clause(-red(u, v), -red(u, w), -red(v, w))
    for u, v in possible:
        if red(u, v) == yes:
            continue
        common = [f.conjunction(edge(u, w), edge(v, w)) for w in range(order) if w not in (u, v)]
        bound = degree[u] + degree[v] - 13
        f.clause(-red(u, v), -f.count(common, bound + 1)[bound + 1])
        if flexible and v in outside:
            union = [f.disjunction(edge(u, w), edge(v, w)) for w in range(order) if w not in (u, v)]
            f.clause(-red(u, v), f.count(union, 11)[11])

    # Deleting two vertices that hit all simple eight-degree vertices
    # must lose at least 72-58=14 projected marked edges.
    for u, v in pairs:
        if flexible:
            avoids = f.any(f.conjunction(full_test[w], f.conjunction(-edge(u, w), -edge(v, w)))
                           for w in sorted(outside) if w not in (u, v))
        else:
            avoids = f.any(f.conjunction(-edge(u, w), -edge(v, w)) for w in sorted(full) if w not in (u, v))
        for left in range(degree[u]+1):
            more_left = red_degree[u][left+1]
            right = projected - 58 - left
            if right >= 1:
                f.clause(avoids, more_left, red_degree[v][right] if right <= degree[v] else no)
            if right >= 0:
                f.clause(avoids, -red(u, v), more_left, red_degree[v][right+1] if right < degree[v] else no)

    # Number exterior incidences on each bundle endpoint. A marking
    # joining a T endpoint to exterior x must see all other bundles.
    external_count = {}
    for u in range(core):
        external_count[u] = f.count([edge(u, x) for x in sorted(outside)], len(outside))
        if tighten and len(outside) > 13-b:
            f.clause(-external_count[u][14-b])
    if budget_cut:
        from collections import Counter
        from d8_core_cut_budget import necessary_patterns
        patterns = tuple(necessary_patterns(b,exterior_hits))
        if not patterns:
            f.clause()
            return f
        types = tuple(sorted({pair for pattern in patterns for pair in pattern}))
        type_occurrences = {pair: [] for pair in types}
        count_upper = min(13-b,len(outside))
        exact = {
            (u,i): f.conjunction(external_count[u][i],-external_count[u][i+1])
                if i < len(outside) else external_count[u][i]
            for u in range(core)
            for i in range(count_upper+1)
        }
        for i in range(b):
            for a,c in types:
                typ = f.conjunction(exact[2*i,a],exact[2*i+1,c])
                if a != c:
                    typ = f.disjunction(typ,f.conjunction(exact[2*i,c],exact[2*i+1,a]))
                type_occurrences[a,c].append(typ)
        by_type = {pair: f.count(lst,b+1) for pair,lst in type_occurrences.items()}
        exact_counts = {
            (pair,i): f.conjunction(counts[i],-counts[i+1])
            for pair,counts in by_type.items() for i in range(b+1)
        }
        valid_patterns = []
        for pattern in patterns:
            count = Counter(pattern)
            valid = yes
            for pair in types:
                valid = f.conjunction(valid,exact_counts[pair,count[pair]])
            valid_patterns.append(valid)
        f.clause(*valid_patterns)
    for u, v in possible:
        if u < core <= v:
            limit = exterior_hits[v-core] + 6 - b
            if limit < len(outside):
                f.clause(-red(u, v), -external_count[u][limit+1])
            if tighten and limit == 1:
                for w in sorted(outside-{v}):
                    f.clause(-red(u, v), -edge(u, w))
        if v < core and u//2 != v//2:
            if tighten:
                for i in range(14-b):
                    j = 13-b-i
                    if max(i,j) <= len(outside):
                        f.clause(-red(u,v), -external_count[u][i], -external_count[v][j])
            else:
                cut = [edge(x, y) for x in (u, v) for y in sorted(outside)]
                f.clause(-red(u, v), -f.count(cut, 13-b)[13-b])
    if improve:
        if not flexible:
            full_test = {u: yes if u in full else no for u in sorted(outside)}
        # Maximizing the number of doubled bundles makes the repeated
        # matching maximum in the graph of degree-at-most-seven vertices.
        for u, v in combinations(sorted(outside), 2):
            f.clause(-red(u, v), full_test[u], full_test[v])
        for i in range(b):
            exposed = [f.any(f.conjunction(red(u, v), -full_test[v]) for v in sorted(outside))
                       for u in (2*i, 2*i+1)]
            f.clause(-exposed[0], -exposed[1])
    if tighten and b == 9:
        if not flexible:
            full_test = {u: yes if u in full else no for u in sorted(outside)}
        p = (36-sum(exterior_hits))//2
        for u in range(order):
            for z in sorted(outside):
                if z == u:
                    continue
                r_z = exterior_hits[z-core]
                if r_z < 6:
                    continue
                other_miss = f.any(f.conjunction(full_test[w], -edge(u,w))
                                   for w in sorted(outside) if w not in (u,z))
                exceptions = [-full_test[z], edge(u,z), other_miss]
                if u < core:
                    if r_z >= 7:
                        f.clause(*exceptions)
                    else:
                        f.clause(*exceptions, -external_count[u^1][1])
                else:
                    r_u = exterior_hits[u-core]
                    maximum = min(8-r_u,sum(r_u+r>=b for j,r in enumerate(exterior_hits)
                                            if j != u-core))
                    minimum = 7-maximum
                    if minimum > 0 and (r_z>=7 or comb(minimum,2)>p):
                        f.clause(*exceptions,red_degree[u][8] if degree[u]>=8 else no)
    if tighten and b == 8:
        if not flexible:
            full_test = {u: yes if u in full else no for u in sorted(outside)}
        p = (40-sum(exterior_hits))//2
        for u in range(order):
            misses = [f.conjunction(full_test[v],-edge(u,v))
                      for v in sorted(outside) if v != u]
            two = f.count(misses,2)[2]
            if u < core:
                f.clause(two)
                continue
            f.clause(two,red_degree[u][8] if degree[u]>=8 else no)
            for z in sorted(outside-{u}):
                r_z = exterior_hits[z-core]
                if r_z>=7 or (r_z==6 and comb(exterior_hits[u-core],2)>p):
                    f.clause(-full_test[z],edge(u,z),two)

    # Symmetries fixing every exterior vertex. A lexicographic maximum
    # over each orbit satisfies all these comparisons at once.
    layout = [(u, v) for u in range(core) for v in sorted(outside)]
    layout += [(u, v) for u, v in pairs if u < v < core or core <= u < v]
    word = [(edge(u, v), red(u, v)) for u, v in layout]
    flat = [lit for record in word for lit in record]
    if structure is None:
        swaps = [((2*i, 2*i+1),) for i in range(b)]
        swaps += [((2*i, 2*i+2), (2*i+1, 2*i+3)) for i in range(b-1)]
    else:
        swaps = fixed_symmetries(structure,b)
    if flexible:
        swaps += [((u, u+1),) for u in range(core, order-1) if exterior_hits[u-core] == exterior_hits[u-core+1]]
    for generator in swaps:
        p = list(range(order))
        for u, v in generator:
            p[u], p[v] = p[v], p[u]
        rival = [lit for u, v in layout for lit in (edge(p[u], p[v]), red(p[u], p[v]))]
        lex_maximum(f, flat, rival)
    return f


def cases(p, flexible=False, minimum_order=None, bundles=9):
    if bundles == 8:
        from d8_b8_exterior import profiles as eight_profiles
        for order in range(minimum_order or 6, (40-2*p)//3+1):
            for i, (hits, _) in enumerate(eight_profiles(order,p)):
                yield f"b8p{p}_n{order}_{i:04d}", None, hits
        return
    if flexible:
        slots = 36 - 2*p
        for order in range(minimum_order or 7, slots//4+1):
            for i, (hits, _, _) in enumerate(profiles(order, slots)):
                yield f"p{p}_largen{order}_{i:02d}", None, hits
        return
    for order in range(minimum_order or 4, min((36-2*p)//4, 6) + 1):
        for i, (edges, hits) in enumerate(exterior_shapes(p, order)):
            yield f"p{p}_n{order}_{i:02d}", edges, hits


def check_replay(directory, cnf, proof, checker):
    progress = subprocess.run(
        [str(checker), cnf.name, proof.name], cwd=directory,
        capture_output=True, text=True, check=True,
    )
    return json.loads(progress.stdout)


def initial_conflict(clauses):
    """Return RUP antecedents if the input itself has a unit conflict."""
    occurrence = defaultdict(list)
    remaining = []
    queue = deque()
    for i, clause in enumerate(clauses):
        remaining.append(len(clause))
        for literal in clause:
            occurrence[literal].append(i)
        if len(clause) <= 1:
            queue.append(i)
    selected = set()
    hints = []
    while queue:
        i = queue.popleft()
        live = [x for x in clauses[i] if -x not in selected]
        if any(x in selected for x in live):
            continue
        hints.append(i + 1)
        if not live:
            return hints
        assert len(live) == 1
        unit = live[0]
        selected.add(unit)
        for j in occurrence[-unit]:
            remaining[j] -= 1
            if remaining[j] == 1:
                queue.append(j)
    return None


def run_case(args, case):
    name, edges, hits = case
    cnf, proof, log, status = (args.out / (name + s) for s in
                                (".cnf", ".lrat", ".log", ".json"))
    if args.verify:
        row = json.loads(status.read_text())
        if row["result"] != "VERIFIED_UNSAT":
            raise ValueError(f"{name} has no verified certificate")
        with TemporaryDirectory(dir=args.out) as path:
            tmp = Path(path)
            regenerated = tmp / "regenerated.cnf"
            fixed, replay = tmp / "fixed.cnf", tmp / "fixed.lrat"
            instance(edges, hits, args.improve, args.bundles,
                     args.witness_structure, args.tighten, args.budget_cut,
                     args.compact).dump(regenerated)
            if file_digest(regenerated) != row["cnf_sha256"]:
                raise ValueError(f"{name} disagrees with the regenerated formula")
            if unpack(cnf.with_suffix(".cnf.gz"), fixed) != row["cnf_sha256"]:
                raise ValueError(f"{name} disagrees with the archived formula")
            if unpack(proof.with_suffix(".lrat.gz"), replay) != row["lrat_sha256"]:
                raise ValueError(f"{name} disagrees with the archived proof")
            if check_replay(tmp, fixed, replay, args.checker) != row["replay"]:
                raise ValueError(f"{name} disagrees with the stored replay counts")
    else:
        if status.exists():
            prior = json.loads(status.read_text())
            if prior["result"] == "VERIFIED_UNSAT":
                return prior
        f = instance(edges, hits, args.improve, args.bundles,
                     args.witness_structure, args.tighten, args.budget_cut,
                     args.compact)
        f.dump(cnf)
        hints = initial_conflict(f.clauses)
        if hints:
            proof.write_text(f"{len(f.clauses)+1} 0 " + " ".join(map(str, hints)) + " 0\n")
            log.write_text("The input has a unit contradiction.\n")
            code, limit = 20, None
        else:
            code, limit = bounded_solve(args.solver, cnf, proof, log,
                                        args.timeout, args.proof_mib * 1024**2)
        row = dict(name=name, edges=edges, hits=hits, variables=f.variables,
                   clauses=len(f.clauses), limit=limit,
                   result="SAT" if code == 10 else "UNKNOWN")
        if args.witness_structure:
            row["witness_structure"] = args.witness_structure
        if args.tighten:
            row["tighten"] = True
        if args.budget_cut:
            row["budget_cut"] = True
        if args.compact:
            row["compact"] = True
        if code == 20:
            row.update(result="VERIFIED_UNSAT",
                       cnf_sha256=file_digest(cnf), lrat_sha256=file_digest(proof),
                       replay=check_replay(args.out, cnf, proof, args.checker))
            gzip_file(cnf)
            gzip_file(proof)
        elif code != 10 and proof.exists():
            proof.unlink()
        status.write_text(json.dumps(row, indent=2) + "\n")
    print(name, row["result"], row.get("limit") or "", flush=True)
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", nargs="+", type=int, default=[5])
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--select", nargs="+")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--proof-mib", type=int, default=80)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--checker", type=Path,
                        default=Path(__file__).resolve().parent.parent / "d7_rup_replay.exe")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--improve", action="store_true")
    parser.add_argument("--flexible", action="store_true")
    parser.add_argument("--minimum-order", type=int)
    parser.add_argument("--bundles", type=int, choices=(8,9), default=9)
    parser.add_argument("--witness-structure", choices=tuple(WITNESS_STRUCTURES))
    parser.add_argument("--tighten", action="store_true")
    parser.add_argument("--budget-cut", action="store_true")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    if args.witness_structure is not None and args.p != [len(WITNESS_STRUCTURES[args.witness_structure])]:
        parser.error("the witness structure must match the selected number of pairs")
    if args.compact and args.witness_structure is None:
        parser.error("--compact requires --witness-structure")
    if args.solver is None and not args.verify:
        parser.error("supply --solver to search or --verify to replay")
    args.out = args.out.resolve()
    args.out.mkdir(exist_ok=True, parents=True)
    selected = [c for p in args.p for c in cases(p,args.flexible,args.minimum_order,args.bundles)
                if not args.select or c[0] in args.select]
    with ThreadPoolExecutor(args.jobs) as pool:
        rows = list(pool.map(lambda case: run_case(args, case), selected))
    if args.verify:
        print(len(rows), "regenerated and replayed")
    else:
        print(sum(r["result"] == "VERIFIED_UNSAT" for r in rows), "verified of", len(rows))


if __name__ == "__main__":
    main()
