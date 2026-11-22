"""Fixed pentagon-anchor formulas for triangle-free marked supports at degree nine."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path[:0] = [str(ROOT), str(ROOT / "三小时续研_九度矩")]

import d9_anchor_cases as prior
from d7_parallel_sat import file_digest
from d7_verify_parallel import unpack
from d8_anchored_sat import add_anchor_swap_cuts
from d8_parallel_sat import bounded_solve, gzip_file


def part_sizes(slack, degree):
    half = (degree-sum(slack))//2
    return tuple(half + slack[(i+2)%5] + slack[(i+3)%5] for i in range(5))


def shape_bounds(slack, degree):
    sizes = part_sizes(slack,degree)
    marks = degree**2+(degree//2)**2+1
    for i in range(5):
        j,opposite = (i+1)%5,(i+3)%5
        required = marks-(degree**2+sizes[(i+2)%5]*sizes[(i+4)%5]-slack[i]*slack[j])
        yield i,j,opposite,required


def arithmetic_excluded(slack, degree):
    return any(slack[i]+slack[j] == 0 or degree*(slack[i]+slack[j]) < required
               for i,j,_,required in shape_bounds(slack,degree))


def instance(slack, bundles, min_order, max_order, strengthen=False,
             degree=9, triangles="forbid", capacity_cuts=False,
             minimal_support=False, maximal_host=False):
    DEGREE = degree
    MARKS = degree**2 + (degree//2)**2 + 1
    total = sum(slack)
    core_sizes = part_sizes(slack, degree)
    n_core = sum(core_sizes)
    parts = list(range(5))
    for i, size in enumerate(core_sizes):
        parts.extend([i] * (size - 1))
    outside = total + (degree-5) * (total // 3)
    if max_order is not None:
        outside = min(outside, max_order - n_core)
    parts.extend([-1] * outside)
    n = len(parts)
    vertices = range(n)
    pairs = tuple(combinations(vertices, 2))
    f = prior.BalancedCountCNF()
    yes, no = f.truth, -f.truth
    host, red, extra, blue = {}, {}, {}, {}
    max_bundle = (2*degree**2-MARKS)//(2*degree-1) if degree>9 and not bundles else 2
    if degree==15:
        max_bundle = min(max_bundle,5)
    higher = tuple({} for _ in range(max_bundle-2))
    extras = (extra,*higher)

    def entry(table, u, v):
        return no if u == v else table[min(u, v), max(u, v)]

    def incident(table, u):
        return [entry(table, u, v) for v in vertices if v != u]

    for u, v in pairs:
        a, b = parts[u], parts[v]
        base = a >= 0 and b >= 0 and (a-b)%5 in (1,4)
        if base:
            e = yes
            m = yes if u < 5 else f.variable()
            j = f.variable() if slack[a] and slack[b] else no
        elif (u < 5 and b >= 0) or (a >= 0 and not slack[a]) or (b >= 0 and not slack[b]):
            e = m = j = no
        else:
            e, m, j = (f.variable() for _ in range(3))
        host[u, v], red[u, v], extra[u, v] = e, m, j
        blue[u, v] = f.conjunction(e, -m)
        f.clause(-m, e)
        f.clause(-j, m)
        if higher:
            spare = min((slack[i] for i in (a,b) if i>=0), default=degree)
            previous = j
            for k,table in enumerate(higher,start=2):
                allowed = previous != no and spare >= k+(not base)
                current = f.variable() if allowed else no
                table[u,v] = current
                f.clause(-current,previous)
                previous = current

    # All vertices in the old parts see exactly their prescribed anchors.
    # The selected pentagon has minimum slack among all induced marked pentagons.
    add_anchor_swap_cuts(f, parts, n_core, n, lambda u,v: entry(host,u,v),
                        lambda u,v: entry(red,u,v))
    active, h_full, s_full, colored, clean = [], [], [], [], []
    two_repeats = []
    weighted_host, weighted_marks = [], []
    for u in vertices:
        e, m = (incident(table, u) for table in (host, red))
        j = [entry(table,u,v) for table in extras for v in vertices if v!=u]
        h = f.count(e + j, DEGREE + 1)
        h_full.append(h[DEGREE])
        s_full.append(f.count(e, DEGREE)[DEGREE])
        colored.append(f.count(m, DEGREE))
        clean.append(-f.any(incident(blue, u)))
        f.clause(-h[DEGREE + 1])
        if minimal_support:
            weighted_host.append(h)
            weighted_marks.append(f.count(m+j,DEGREE))
        if strengthen and (degree == 9 or bundles):
            repeat_count = f.count(j, 3)
            two_repeats.append(repeat_count[2])
            f.clause(-repeat_count[3])
        if u < n_core:
            continue
        present = f.any(m)
        active.append(present)
        for edge in e:
            f.clause(-edge, present)
        for i in range(5):
            prescribed = ((i - 1) % 5, (i + 1) % 5)
            f.clause(*(-entry(red, u, v) for v in prescribed),
                     *(entry(host, u, v) for v in range(5) if v not in prescribed))

    def require_count(literals, k):
        values = f.count(literals, k + 1)
        f.clause(values[k])
        f.clause(-values[k + 1])

    needed = max(0, min_order - n_core)
    f.clause(f.count(active, needed)[needed])
    copies = [literal for table in extras for literal in table.values()]
    if bundles:
        require_count(list(red.values()), MARKS - bundles)
        require_count(copies, bundles)
    else:
        # All degree-nine branches at once, using the exact number of
        # weighted marks, and retaining every outstanding repeat count.
        require_count(list(red.values())+copies, MARKS)
        bound = 18 if degree==9 else degree*(degree-1)//2+1
        counts = f.count(copies,bound)
        f.clause(counts[2])
        f.clause(-counts[bound])
        if triangles == "forbid":
            minimum = min(min_order-2*degree+1,(degree+5)//2)
            f.clause(f.count([-flag for flag in clean],minimum)[minimum])

    possible = [pair for pair in pairs if red[pair] != no]
    for (u, v), (x, y) in combinations(possible, 2):
        if u not in (x, y) and v not in (x, y):
            f.clause(-red[u,v], -red[x,y],
                     *(entry(host, a, b) for a in (u, v) for b in (x, y)))
    if triangles == "forbid":
        for u, v, x in combinations(vertices, 3):
            f.clause(-red[u,v], -red[u,x], -red[v,x])
    if triangles == "require":
        f.clause(*(f.conjunction(red[u,v], f.conjunction(red[u,x], red[v,x]))
                   for u,v,x in combinations(vertices, 3)
                   if no not in (red[u,v], red[u,x], red[v,x])))
    if triangles != "forbid" and degree>9 and not bundles:
        assert degree<=23
        for four in combinations(vertices,4):
            edges = [red[pair] for pair in combinations(four,2)]
            if no not in edges:
                f.clause(*(-edge for edge in edges))

    # A marked pentagon with no incident blue pair implies the sharp bound.
    # The graph on such clean vertices consequently has no induced 2K2, no
    # triangle and no pentagon. A shortest odd cycle would violate one of these.
    if triangles == "forbid":
        side = [f.variable() for _ in vertices]
        for u, v in possible:
            f.clause(-clean[u], -clean[v], -red[u,v], side[u], side[v])
            f.clause(-clean[u], -clean[v], -red[u,v], -side[u], -side[v])

    for u, v in possible:
        twice = extra[u, v]
        union = [f.disjunction(entry(host,u,x), entry(host,v,x))
                 for x in vertices if x not in (u, v)]
        if degree==9:
            required = 11
        elif degree==15 and not bundles:
            required = 19
        elif not bundles:
            required = (MARKS-degree-1)//(degree-1)
        else:
            required = (MARKS+degree-2-bundles)//degree
        cap = f.count(union, 13 if twice != no and degree == 9 else required)
        f.clause(-red[u,v], cap[required])
        if twice != no and degree == 9:
            f.clause(-twice, cap[13])
            f.clause(-twice, -clean[u], -clean[v])
            if triangles != "forbid":
                for x in vertices:
                    if x not in (u, v):
                        f.clause(-twice, -entry(red,u,x), -entry(red,v,x))
            if strengthen:
                path = f.disjunction(two_repeats[u], two_repeats[v])
                f.clause(-twice, -path, h_full[u])
                f.clause(-twice, -path, h_full[v])
                for x in vertices:
                    if x not in (u, v):
                        f.clause(-twice, -path, -entry(host,u,x), -entry(host,v,x))

    # The even equality structure forbids *every* pair of deleted vertices
    # from reducing the original weighted maximum degree to eight.
    # In the simple projection with 96 marks, a pair which loses at most 16
    # projected marks cannot reduce the simple maximum degree to eight either.
    for u, v in pairs:
        avoid = {
            x: f.conjunction(-entry(host,u,x), -entry(host,v,x))
            for x in vertices if x not in (u, v) and h_full[x] != no
        }
        f.clause(*(f.conjunction(h_full[x], z) for x,z in avoid.items()))
        if strengthen and bundles:
            threshold = 2*degree + 1 - bundles
            lost = f.disjunction(f.any(
                f.conjunction(colored[u][i], colored[v][j])
                for i in range(DEGREE + 1) for j in range(DEGREE + 1) if i + j == threshold + 1
            ), f.conjunction(-red[u,v], f.any(
                f.conjunction(colored[u][i], colored[v][j])
                for i in range(DEGREE + 1) for j in range(DEGREE + 1) if i + j == threshold
            )))
            f.clause(lost, *(f.conjunction(s_full[x], z) for x,z in avoid.items()
                             if s_full[x] != no))
        elif bundles == 2:
            a, b = colored[u], colored[v]
            lose17 = f.disjunction(f.conjunction(a[9], b[9]), f.conjunction(
                -red[u,v], f.disjunction(f.conjunction(a[8], b[9]), f.conjunction(a[9], b[8]))))
            f.clause(lose17, *(f.conjunction(s_full[x], z) for x,z in avoid.items()
                               if s_full[x] != no))

    for i, j, opposite, required in shape_bounds(slack,degree):
        if required <= 0:
            continue
        outer = [f.disjunction(entry(host, i, v), entry(host, j, v))
                 for v in range(n_core, n)]
        needed = (required + DEGREE - 1) // DEGREE
        f.clause(f.count(outer, needed)[needed])
        remaining = [table[u,v] for table in (red,*extras) for u,v in pairs
                     if parts[u] in (-1, opposite) and parts[v] in (-1, opposite)]
        f.clause(f.count(remaining, required)[required])

    charge = max(Fraction(DEGREE, 2), total - 2 * min(slack))
    missing = [-red[u,v] for u,v in pairs if v < n_core and (parts[u] - parts[v]) % 5 in (1, 4)]
    signatures = [host[u,v] for u,v in pairs if u < 5 and v >= n_core]
    budget = (charge - Fraction(DEGREE, 2)) * total + degree - Fraction(5, 2)
    sig_counts = f.count(signatures, total)
    for misses, value in enumerate(f.count(missing, budget // 2 + 1)):
        need = total - (budget - 2 * misses) // charge
        f.clause(-value, yes if need <= 0 else sig_counts[need] if need <= total else no)

    if capacity_cuts:
        # Charge each non-base internal mark twice in the extra core degree
        # budget, and each crossing blue pair once.
        core = range(n_core)
        exterior = range(n_core,n)
        base_edges = sum(core_sizes[i]*core_sizes[(i+1)%5] for i in range(5))
        extra_capacity = sum(s*a for s,a in zip(slack,core_sizes))
        external = [table[u,v] for u,v in combinations(exterior, 2) for table in (red,*extras)]
        external_cap = total*(DEGREE-1)//3
        external_count = f.count(external,external_cap+1)
        f.clause(-external_count[external_cap+1])
        penalty = missing + [blue[u,v] for u in core for v in exterior]
        penalty += [table[u,v] for u,v in combinations(core, 2) for table in extras]
        penalty += [red[u,v] for u,v in combinations(core, 2)
                    if (parts[u]-parts[v])%5 not in (1,4)]
        offset = MARKS-base_edges-extra_capacity
        for loss, threshold in enumerate(f.count(penalty,max(0,external_cap-offset+1))):
            need = offset+loss
            if need > 0:
                f.clause(-threshold, external_count[need] if need <= external_cap else no)

        # An exterior marked pair covers all core marks. An independent
        # subset of the core with the specified class sizes consumes at
        # least the indicated number of missing base marks.
        limit = min(len(missing),external_cap-offset)
        if limit >= 0:
            independent = [0]*(limit+1)
            for sizes in product(*(range(a+1) for a in core_sizes)):
                cost = sum(sizes[i]*sizes[(i+1)%5] for i in range(5))
                if cost <= limit:
                    independent[cost] = max(independent[cost],sum(sizes))
            for j in range(1,limit+1):
                independent[j] = max(independent[j],independent[j-1])
            holes = f.count(missing,limit+1)
            f.clause(-holes[limit+1])
            relevant = [(k,n_core-v) for k,v in enumerate(independent)
                        if k==limit or v<independent[k+1]]
            for u,v in combinations(exterior,2):
                reach = [f.disjunction(entry(host,u,c),entry(host,v,c)) for c in core]
                cover = f.count(reach,relevant[0][1])
                for k,need in relevant:
                    f.clause(-red[u,v], holes[k+1], cover[need])

    if minimal_support:
        # If an outside mark neighborhood is contained in another one,
        # redirecting its marked copies uses no new host pair. A graph
        # with the minimum number of active vertices forbids such a merge.
        for v in range(n_core,n):
            for u in vertices:
                if v == u:
                    continue
                missing_neighbor = f.any(
                    f.conjunction(entry(red,v,x),-entry(red,u,x))
                    for x in vertices if x!=v
                )
                can_merge = f.any(
                    f.conjunction(-weighted_marks[v][m+1],-weighted_host[u][DEGREE-m+1])
                    for m in range(1,DEGREE)
                )
                f.clause(-active[v-n_core],missing_neighbor,-can_merge)

    if maximal_host:
        # Adding a blue nonedge between two active nonanchors preserves the
        # selected old core and cannot enlarge any competing old core.
        for u,v in combinations(range(5,n),2):
            present_u = yes if u < n_core else active[u-n_core]
            present_v = yes if v < n_core else active[v-n_core]
            f.clause(-present_u,-present_v,h_full[u],h_full[v],host[u,v])

    # Equivalent permutations inside each part, including padded exterior
    # positions, leave all of the constraints above invariant.
    for u in range(5, n - 1):
        v = u + 1
        if parts[u] != parts[v]:
            continue
        tied = yes
        if capacity_cuts and u >= n_core:
            keys = [(active[u-n_core],active[v-n_core])]
            keys += [(entry(host,u,x),entry(host,v,x)) for x in range(5)]
            for lo,hi in keys:
                f.clause(-tied,lo,-hi)
                same = f.disjunction(f.conjunction(lo,hi), f.conjunction(-lo,-hi))
                tied = f.conjunction(tied,same)
        for x in vertices:
            if x in (u, v):
                continue
            for table in (red,*extras,host):
                lo, hi = entry(table, u, x), entry(table, v, x)
                if lo == hi:
                    continue
                f.clause(-tied, lo, -hi)
                same = f.disjunction(f.conjunction(lo,hi), f.conjunction(-lo,-hi))
                tied = f.conjunction(tied, same)
    return f


def process(slack, args):
    name = prior.case_name(slack)
    metadata = args.out / f"{name}.json"
    fixed = json.loads(metadata.read_bytes()) if metadata.is_file() else None
    settings = {"slack": list(slack), "bundles": args.bundles,
                "min_order": args.min_order, "max_order": args.max_order}
    if args.strengthen:
        settings["strengthen"] = True
    if args.degree != 9:
        settings["degree"] = args.degree
    if args.triangles != "forbid":
        settings["triangles"] = args.triangles
    if args.capacity_cuts:
        settings["capacity_cuts"] = True
    if args.minimal_support:
        settings["minimal_support"] = True
    if args.maximal_host:
        settings["maximal_host"] = True
    if fixed is not None and fixed["result"] == "VERIFIED_UNSAT":
        assert fixed["settings"] == settings
        if not args.verify:
            return fixed
        with TemporaryDirectory(prefix="pentagon_", dir=args.out) as place:
            place = Path(place)
            cnf, proof, regenerated = (place/name for name in ("fixed.cnf","fixed.lrat","fresh.cnf"))
            instance(slack, args.bundles, args.min_order, args.max_order,
                     args.strengthen, args.degree, args.triangles, args.capacity_cuts,
                     args.minimal_support, args.maximal_host).dump(regenerated)
            assert unpack(args.out / f"{name}.cnf.gz", cnf) == fixed["cnf_sha256"] == file_digest(regenerated)
            assert unpack(args.out / f"{name}.lrat.gz", proof) == fixed["lrat_sha256"]
            check = subprocess.run([str(args.checker), cnf.name, proof.name], cwd=place,
                                   capture_output=True, text=True, check=True)
            assert json.loads(check.stdout) == fixed["replay"]
        print(name, "REPLAY_PASS", flush=True)
        return fixed
    if args.verify:
        return dict(name=name, settings=settings, result="UNRESOLVED")

    cnf, proof, log = (args.out / f"{name}.{suffix}" for suffix in ("cnf","lrat","log"))
    formula = instance(slack, args.bundles, args.min_order, args.max_order,
                       args.strengthen, args.degree, args.triangles, args.capacity_cuts,
                       args.minimal_support, args.maximal_host)
    formula.dump(cnf)
    code, limit = bounded_solve(args.solver, cnf, proof, log, args.timeout, args.proof_mib * 1024**2)
    result = dict(name=name, settings=settings, result="SAT" if code == 10 else "UNRESOLVED",
                  code=code, limit=limit, variables=formula.variables, clauses=len(formula.clauses))
    if code == 20:
        check = subprocess.run([str(args.checker), cnf.name, proof.name], cwd=args.out,
                               capture_output=True, text=True, check=True)
        result.update(result="VERIFIED_UNSAT", replay=json.loads(check.stdout),
                      cnf_sha256=file_digest(cnf), lrat_sha256=file_digest(proof))
        gzip_file(cnf)
        gzip_file(proof)
    elif proof.exists():
        proof.unlink()
    metadata.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(name, result["result"], limit or "", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundles", type=int, default=2)
    parser.add_argument("--degree", type=int, default=9)
    parser.add_argument("--triangles", choices=("allow","require","forbid"), default="forbid")
    parser.add_argument("--min-order", type=int, default=24)
    parser.add_argument("--max-order", type=int)
    parser.add_argument("--select", nargs="+", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument("--proof-mib", type=int, default=250)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--checker", type=Path, default=ROOT / "d7_rup_replay.exe")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--strengthen", action="store_true")
    parser.add_argument("--capacity-cuts", action="store_true")
    parser.add_argument("--minimal-support", action="store_true")
    parser.add_argument("--maximal-host", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    assert args.min_order >= 23 and 0 <= args.bundles <= 18
    assert args.bundles != 0 or args.min_order >= 24
    assert not args.minimal_support or args.bundles == 0
    assert args.degree == 9 or (11<=args.degree<=23 and args.degree%2 and args.bundles in (0,1))
    assert args.max_order is None or args.max_order >= args.min_order
    cases = [tuple(map(int, word[1:])) for word in args.select]
    assert all(word.startswith("s") and len(word) == 6 for word in args.select)
    assert all(sum(s) % 2 and min(part_sizes(s,args.degree)) >= 1 for s in cases)
    args.out = args.out.resolve()
    args.checker = args.checker.resolve()
    if not args.verify:
        if not args.solver:
            parser.error("Supply --solver or --verify")
        args.solver = args.solver.resolve()
        args.out.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda s: process(s, args), cases))
    left = [record["name"] for record in results if record["result"] != "VERIFIED_UNSAT"]
    print(json.dumps({"cases": len(results), "verified": len(results)-len(left),
                      "unresolved": left}), flush=True)


if __name__ == "__main__":
    main()
