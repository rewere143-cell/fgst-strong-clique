"""Exact finite D=9 CNFs anchored on a marked triangle in a multigraph."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from itertools import combinations, product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from d7_parallel_sat import GraphCNF, file_digest
from d7_bipartite_ore_coupled import bound
from d7_verify_parallel import unpack
from d8_b9_sat import check_replay, initial_conflict, lex_maximum
from d8_parallel_sat import bounded_solve, gzip_file
from d8_repeat_core_sat import require_at_least, require_exactly


@dataclass(frozen=True)
class Anchor:
    name: str
    order: int
    omissions: tuple = ()
    root_loss: str = ""


ANCHORS = (
    Anchor("n23_slack", 23, (), "slack"),
    Anchor("n23_repeat", 23, (), "repeat"),
    Anchor("n23_t1", 23, (2,)),
    Anchor("n23_t2_same", 23, (2, 2)),
    Anchor("n23_t2_distinct", 23, (1, 2)),
    Anchor("n24_t0", 24),
    Anchor("n24_t1", 24, (2,)),
    Anchor("n25_t1", 25, (2,)),
)


def model(anchor, *, full_lex=False, triangle_cuts=True, strengthened=False,
          reduced=False, pin_root_blue=None, pin_zero_marks=None,
          pin_zero_blue=None, cover_cuts=False):
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    n = anchor.order
    vertices = range(n)
    roots = range(3)
    shared = range(3, 3 + len(anchor.omissions))
    zeros = range(shared.stop, shared.stop + n - 24
                  + len(anchor.omissions) + bool(anchor.root_loss))
    root_sets = {u: set(roots) - {u} for u in roots}
    for v, omitted in zip(shared, anchor.omissions):
        root_sets[v] = set(roots) - {omitted}
    for v in zeros:
        root_sets[v] = set()
    groups = []
    start = zeros.stop
    for u in roots:
        length = 7 - sum(u in root_sets[v] for v in shared)
        if u == 0 and anchor.root_loss:
            length -= 1
        group = range(start, start + length)
        groups.append(group)
        root_sets.update((v, {u}) for v in group)
        start += length
    assert start == n

    pairs = tuple(combinations(vertices, 2))
    host, mark, double, blue = {}, {}, {}, {}
    possible = []
    for uv in pairs:
        u, v = uv
        if v < 3:
            h = r = yes
        elif u < 3:
            h = yes if u in root_sets[v] else no
            r = f.variable() if h == yes else no
        else:
            h = f.variable()
            # An outside marked edge must collectively see two triangle roots.
            r = f.variable() if len(root_sets[u] | root_sets[v]) >= 2 else no
        can_double = r != no and v >= 3 and (u >= 3 or
                     (anchor.root_loss == "repeat" and u == 0))
        d = f.variable() if can_double else no
        host[uv], mark[uv], double[uv] = h, r, d
        blue[uv] = f.conjunction(h, -r)
        f.clause(-d, r)
        f.clause(-r, h)
        if r != no:
            possible.append(uv)

    def lit(table, u, v):
        return no if u == v else table[min(u, v), max(u, v)]

    degree, support_degree, marked_degree, repeat_degree = {}, {}, {}, {}
    deficits = []
    reds_from_anchor = []
    for uv in possible:
        if uv[0] in roots or any(x in zeros for x in uv):
            reds_from_anchor.extend((mark[uv], double[uv]))
    require_at_least(f, reds_from_anchor, 18)
    blue_spokes = [lit(blue,u,v) for u in roots for v in range(3,n)
                   if u in root_sets[v]]
    if pin_root_blue is not None:
        require_exactly(f, blue_spokes, pin_root_blue)
    if pin_zero_marks is not None:
        require_exactly(f, [lit(table,x,w) for x in zeros for w in shared
                           for table in (mark,double)], pin_zero_marks)
    if pin_zero_blue is not None:
        require_exactly(f, [lit(blue,x,v) for x in zeros for v in range(3,n)
                           if v not in zeros], pin_zero_blue)

    for u in vertices:
        host_inc = [lit(host, u, v) for v in vertices if u != v]
        mark_inc = [lit(mark, u, v) for v in vertices if u != v]
        double_inc = [lit(double, u, v) for v in vertices if u != v]
        degree[u] = f.count(host_inc + double_inc, 10)
        support_degree[u] = f.count(host_inc, 9)
        marked_degree[u] = f.count(mark_inc + double_inc, 9)
        repeat_degree[u] = f.count(double_inc, 3)
        f.clause(-degree[u][10])
        f.clause(marked_degree[u][1])
        f.clause(-repeat_degree[u][3])
        deficits.extend(-d for d in marked_degree[u][2:])
    require_exactly(f, deficits, 9 * n - 196)
    f.at_most(list(blue.values()), (9 * n - 196) // 2)
    require_at_least(f, list(double.values()), 1)
    f.at_most(list(double.values()), 18)
    if anchor.root_loss == "repeat":
        f.clause(repeat_degree[0][1])

    for x in zeros:
        # The marked spokes to Y2 are its only marks, and the Y1 neighbors
        # must be blue. A Y2 point with r zero marks forces r+4-t of these.
        to_single = [lit(blue, x, y) for group in groups for y in group]
        need = f.count(to_single, 8)
        for w in shared:
            marks_to_zero = [lit(table, w, z) for table in (mark, double) for z in zeros]
            amounts = f.count(marks_to_zero, 4)
            for r in range(1, 2 * len(zeros) + 1):
                f.clause(-lit(mark, x, w), -amounts[r], need[r + 4 - len(shared)])
    if n >= 24:
        for w in shared:
            a, b = sorted(root_sets[w])
            f.clause(-lit(mark, a, w), -lit(mark, b, w))

    if strengthened:
        root_spokes = [lit(table,u,v) for table in (mark,double)
                       for u in roots for v in range(3,n)
                       if u in root_sets[v]]
        zero_marks = [lit(table,x,w) for table in (mark,double)
                      for x in zeros for w in shared]
        zero_blues = [lit(blue,x,v) for x in zeros for v in range(3,n)
                      if v not in zeros]
        # Removing C and Y0 leaves at most eight degree units per
        # vertex, less one per extra triangle and zero adjacency.
        eligible = 8 * (n - 3 - len(zeros))
        root_repeat = int(anchor.root_loss == "repeat")
        require_at_least(f, root_spokes*2 + zero_marks + [-b for b in zero_blues],
                         190 + len(shared) + root_repeat - eligible + len(zero_blues))
        if n == 23 and not zeros:
            require_at_least(f, root_spokes, 16)
        if n == 23 and len(shared) == 2:
            for u in roots:
                for v in range(3,n):
                    if u in root_sets[v]:
                        f.clause(lit(mark,u,v))
            for x in zeros:
                for w in shared:
                    f.clause(-lit(double,x,w))
            # At most one remaining loss after the blue edges at Y0.
            for uv in combinations([u for u in vertices if u not in zeros],2):
                f.clause(-blue[uv])
        if n == 25:
            require_exactly(f, root_spokes, 20)
            require_at_least(f, zero_marks, 2)
            f.at_most(zero_marks, 3)
            for u, group in enumerate(groups):
                for v in group:
                    f.clause(lit(mark,u,v))
            w, = shared
            f.clause(lit(mark,0,w))
            f.clause(-lit(mark,1,w))
            outside = [v for v in range(3,n) if v not in zeros]
            residual_blues = [blue[uv] for uv in combinations(outside,2)]
            f.at_most(residual_blues, 1)
            three = f.count(zero_marks,3)[3]
            for b in residual_blues:
                f.clause(-three,-b)

        for i, j in combinations(roots,2):
            k = 3 - i - j
            cross = [lit(table,u,v) for table in (mark,double)
                     for u, v in product(groups[i],groups[j])]
            s = min(len(groups[i]),len(groups[j]))
            bounds = {
                r: min(2989 * (16-r)**2 // 10000,
                       max(bound(8,8,16-r,d,s) for d in range(1,9)))
                for r in range(len(groups[k])+1)
            }
            cross_values = f.count(cross,max(bounds.values())+1)
            spokes = f.count([lit(mark,k,v) for v in groups[k]],len(groups[k]))
            group_pair = list(groups[i]) + list(groups[j])
            two_blues = f.count([blue[uv] for uv in combinations(group_pair,2)],2)[2]
            for r, upper in bounds.items():
                f.clause(-spokes[r], -cross_values[upper+1])
                sq = (16-r)**2//4
                if sq < upper:
                    f.clause(-spokes[r], two_blues, -cross_values[sq+1])

    if reduced:
        if n == 23 and not shared:
            require_at_least(f, blue_spokes,1)
        if n == 24 and not shared:
            require_at_least(f, blue_spokes,2)
        if n == 24 and shared:
            f.at_most(blue_spokes,2)
            x, = zeros
            w, = shared
            blues_at_x = [lit(blue,x,v) for group in groups for v in group]
            wx = lit(double,w,x)
            bx = f.count(blues_at_x,7)
            two_blue_spokes = f.count(blue_spokes,2)[2]
            # With two blue spokes, a ten-point cover would need at
            # least 68 cross marks, exceeding the Ore-15 bound of 67.
            f.clause(-two_blue_spokes, bx[5])
            f.clause(-wx, bx[6])
            if cover_cuts:
                f.clause(-two_blue_spokes, bx[6])
                f.clause(-two_blue_spokes, -wx, bx[7])
            if pin_root_blue == 1:
                for u, group in enumerate(groups):
                    for v in group:
                        f.clause(lit(mark,u,v))
                # The sole root blue is one of the two shared spokes.
                f.clause(lit(mark,0,w))
                f.clause(-lit(mark,1,w))

    for index, uv in enumerate(possible):
        u, v = uv
        for xy in possible[index+1:]:
            if len(set(uv + xy)) == 4:
                f.clause(-mark[uv], -mark[xy],
                         *(lit(host, a, b) for a, b in product(uv, xy)))
        if double[uv] == no:
            continue
        remaining = [x for x in vertices if x not in uv]
        union = [f.disjunction(lit(host,u,x), lit(host,v,x)) for x in remaining]
        require_union = f.count(union, 13)[13]
        f.clause(-double[uv], require_union)
        f.clause(-double[uv], -repeat_degree[u][2], -repeat_degree[v][2])
        spokes = [lit(blue, a, x) for a in uv for x in remaining]
        f.clause(-double[uv], *spokes)

    # Removing one or two vertices dominating all degree-nine vertices gives
    # an eight-degree host, with at most eighty remaining marked instances.
    for u, v in pairs:
        misses = [f.conjunction(degree[x][9], f.conjunction(-lit(host,u,x),
                                                            -lit(host,v,x)))
                  for x in vertices if x not in (u, v)]
        escape = tuple(misses)
        f.clause(marked_degree[u][9], *escape)
        f.clause(marked_degree[v][9], *escape)
        f.clause(-host[u,v], *escape)

    if triangle_cuts:
        for triple in combinations(vertices, 3):
            a, b, c = triple
            if any(lit(mark,u,v) == no for u,v in combinations(triple,2)):
                continue
            absent = tuple(-lit(mark,u,v) for u,v in combinations(triple,2))
            for u in triple:
                f.clause(*absent, support_degree[u][9 if n >= 24 else 8])
            if n == 23:
                for u, v in combinations(triple, 2):
                    f.clause(*absent, support_degree[u][9], support_degree[v][9])
            multi_touch = []
            non_touch = []
            for x in vertices:
                if x in triple:
                    continue
                h = [lit(host,u,x) for u in triple]
                f.clause(*absent, *(-t for t in h))
                if reduced and n == 23:
                    # All n=23 templates with a zero have exact proofs.
                    f.clause(*absent, *h)
                multi_touch.append(f.count(h, 2)[2])
                non_touch.append(-f.any(h))
                if n >= 24:
                    for u, v in combinations(triple, 2):
                        f.clause(*absent, -lit(mark,u,x), -lit(mark,v,x))
            hi_multi = 3 if n == 23 and not reduced else 2
            f.clause(*absent, -f.count(multi_touch,hi_multi)[hi_multi])
            f.clause(*absent, -f.count(non_touch, max(1, n-23)+1)[max(1, n-23)+1])
            if reduced:
                max_deficit = 5 if n == 23 else 6
                for i in range(max_deficit+2):
                    for j in range(max_deficit+2-i):
                        k = max_deficit+1-i-j
                        degrees = [marked_degree[v][10-d] for v,d in zip(triple,(i,j,k)) if d]
                        f.clause(*absent, *degrees)

    # Put the root-spoke mark bits first. Remaining ties allow a canonical
    # vertex order within each prescribed type without dropping any orbit.
    if full_lex:
        layout = [(u,v) for u,v in pairs if u in roots]
        layout += [(u,v) for u,v in pairs if u not in roots]
        tables = (mark, double, host)
        word = [lit(table,u,v) for u,v in layout for table in tables]
        parts = list(groups)
        if len(shared) == 2 and len(set(anchor.omissions)) == 1:
            parts.append(shared)
        if len(zeros) == 2:
            parts.append(zeros)
        for part in parts:
            for x,y in zip(part, list(part)[1:]):
                swap = {x:y, y:x}
                rival = [lit(table,swap.get(u,u),swap.get(v,v))
                         for u,v in layout for table in tables]
                lex_maximum(f, word, rival)
    else:
        for u, group in enumerate(groups):
            for x,y in zip(group, list(group)[1:]):
                first = [lit(table,u,x) for table in (mark, double)]
                second = [lit(table,u,y) for table in (mark, double)]
                if reduced:
                    first.extend(lit(table,v,x) for v in (*shared,*zeros)
                                 for table in (mark,double,host))
                    second.extend(lit(table,v,y) for v in (*shared,*zeros)
                                  for table in (mark,double,host))
                lex_maximum(f, first, second)
    return f


def run(args, anchor):
    name = anchor.name
    cnf, proof, log, status = (args.out / (name + s) for s in
                                (".cnf", ".lrat", ".log", ".json"))
    f = model(anchor, full_lex=args.full_lex, triangle_cuts=not args.anchor_only,
              strengthened=args.strengthened, reduced=args.reduced,
              pin_root_blue=args.pin_root_blue, pin_zero_marks=args.pin_zero_marks,
              pin_zero_blue=args.pin_zero_blue, cover_cuts=args.cover_cuts)
    if args.verify:
        row = json.loads(status.read_text())
        if row["result"] != "VERIFIED_UNSAT":
            raise ValueError(f"{name} has no verified certificate")
        with TemporaryDirectory(dir=args.out) as path:
            tmp = Path(path)
            regen, fixed, replay = (tmp / filename for filename in
                                    ("regenerated.cnf", "fixed.cnf", "fixed.lrat"))
            f.dump(regen)
            if file_digest(regen) != row["cnf_sha256"]:
                raise ValueError(f"{name} formula digest mismatch")
            if unpack(cnf.with_suffix(".cnf.gz"), fixed) != row["cnf_sha256"]:
                raise ValueError(f"{name} archived formula digest mismatch")
            if unpack(proof.with_suffix(".lrat.gz"), replay) != row["lrat_sha256"]:
                raise ValueError(f"{name} archived proof digest mismatch")
            if check_replay(tmp, fixed, replay, args.checker) != row["replay"]:
                raise ValueError(f"{name} replay count mismatch")
    else:
        if status.exists():
            prior = json.loads(status.read_text())
            if prior["result"] == "VERIFIED_UNSAT":
                return prior
        f.dump(cnf)
        hints = initial_conflict(f.clauses)
        if hints:
            proof.write_text(f"{len(f.clauses)+1} 0 " + " ".join(map(str,hints)) + " 0\n")
            log.write_text("The input has a unit contradiction.\n")
            code, limit = 20, None
        elif args.solver is None:
            code, limit = None, "generate"
        else:
            code, limit = bounded_solve(args.solver, cnf, proof, log, args.timeout,
                                        args.proof_mib * 1024**2)
        row = dict(name=name, variables=f.variables, clauses=len(f.clauses), limit=limit,
                   result="SAT" if code == 10 else "UNKNOWN")
        if code == 20:
            row.update(result="VERIFIED_UNSAT", cnf_sha256=file_digest(cnf),
                       lrat_sha256=file_digest(proof),
                       replay=check_replay(args.out,cnf,proof,args.checker))
            gzip_file(cnf)
            gzip_file(proof)
        elif code != 10 and proof.exists():
            proof.unlink()
        status.write_text(json.dumps(row,indent=2) + "\n")
    print(name, row["result"], row["variables"], row["clauses"], row.get("limit") or "",
          flush=True)
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--select", nargs="+", choices=tuple(x.name for x in ANCHORS))
    p.add_argument("--timeout", type=int, default=150)
    p.add_argument("--proof-mib", type=int, default=100)
    p.add_argument("--jobs", type=int, default=2)
    p.add_argument("--solver", type=Path)
    p.add_argument("--checker", type=Path,
                   default=Path(__file__).resolve().parent.parent / "d7_rup_replay.exe")
    p.add_argument("--verify", action="store_true")
    p.add_argument("--full-lex", action="store_true")
    p.add_argument("--anchor-only", action="store_true")
    p.add_argument("--strengthened", action="store_true")
    p.add_argument("--reduced", action="store_true")
    p.add_argument("--pin-root-blue", type=int)
    p.add_argument("--pin-zero-marks", type=int)
    p.add_argument("--pin-zero-blue", type=int)
    p.add_argument("--cover-cuts", action="store_true")
    args = p.parse_args()
    args.out = args.out.resolve()
    args.out.mkdir(parents=True,exist_ok=True)
    cases = [x for x in ANCHORS if not args.select or x.name in args.select]
    if args.reduced and (not args.strengthened or any(c.order==25 or len(c.omissions)==2 for c in cases)):
        p.error("--reduced requires --strengthened and one of the five unresolved templates")
    with ThreadPoolExecutor(args.jobs) as pool:
        rows = list(pool.map(lambda x: run(args,x),cases))
    print(json.dumps({x["name"]:x["result"] for x in rows},indent=2))


if __name__ == "__main__":
    main()
