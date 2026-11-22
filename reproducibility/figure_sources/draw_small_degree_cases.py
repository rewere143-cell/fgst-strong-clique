"""Draw the finite simple-support and degree-five/seven cases in the paper.

Run with Python 3 from any directory. The archived vertex orders, spoke
colors, multiplicities, and bounds are read from the proof files.
"""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import importlib.util
from itertools import combinations
from math import floor
from pathlib import Path
import json
import sys


def load_module(path):
    sys.path.insert(0, str(path.parent))
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fmt(value):
    return f"{value:.3f}".rstrip("0").rstrip(".") or "0"


def graph_panel(vertices, edges, label):
    """Each entry gives the two endpoint keys, marking, and multiplicity."""
    lines = [
        rf"\coordinate ({v}) at ({fmt(x)},{fmt(y)});"
        for v, (x, y) in vertices.items()
    ]
    for first, second, marked, multiplicity in edges:
        style = "sc marked" if marked else "sc unmarked"
        if multiplicity == 2:
            for bend in ("left", "right"):
                lines.append(
                    rf"\draw[{style}] ({first}) to[bend {bend}=13] ({second});"
                )
        else:
            assert multiplicity == 1
            lines.append(rf"\draw[{style}] ({first}) -- ({second});")
    for v in vertices:
        radius = "1.5pt" if v in ("u", "v") else "1.15pt"
        lines.append(rf"\fill ({v}) circle[radius={radius}];")
    lines.append(rf"\node[anchor=north,inner sep=1pt] at (0,-.85) {{\({label}\)}};")
    return lines


def d5_panels(archive):
    script = load_module(archive / "d5_parallel_spoke_bound.py")
    archived = json.loads(
        next(archive.rglob("d5_parallel_final_replay.json")).read_text("utf-8")
    )
    verified = {
        (tuple(case["unmarked_spokes"]), tuple(map(tuple, case["internal_edges"]))):
        case["upper_bound"] for case in archived["all_templates"]
    }
    fixed = list(script.partial_templates())
    assert len(fixed) == 21 and set(fixed) == set(verified)
    coordinates = [(-1.15, -.06), (-.78, -.53), (-.36, -.76),
                   (.36, -.76), (.78, -.53), (1.15, -.06)]
    vertices = {"u": (-.62, .35), "v": (.62, .35)}
    vertices.update({f"a{i}": point for i, point in enumerate(coordinates)})
    panels = []
    for unmarked, within in fixed:
        edges = [("u", "v", True, 2)]
        edges.extend(("u" if i < 3 else "v", f"a{i}", i not in unmarked, 1)
                     for i in range(6))
        edges.extend((f"a{i}", f"a{j}", marked, mult)
                     for (i, j, marked), mult in Counter(within).items())
        panels.append(graph_panel(vertices, edges, rf"m\leq {verified[unmarked, within]}"))
    return panels


def d7_panels(archive):
    script = load_module(archive / "d7_parallel_sat.py")
    variants = list(script.cases())
    archived_names = {
        path.name.removesuffix(".encoding.json")
        for q in (9, 10)
        for path in (archive / f"d7_parallel_sat_cuts_q{q}").glob("*.encoding.json")
    }
    assert len(variants) == 51 and {case[0] for case in variants} == archived_names
    result = defaultdict(list)
    for name, left, right, shared in variants:
        key = name.split("_")[0]
        vertices = {"u": (-.61, .03), "v": (.61, .03)}
        edges = [("u", "v", True, 2)]
        for root, signs, center in (("u", left, -.68), ("v", right, .68)):
            for i, value in enumerate(signs):
                t = 2 * i / (len(signs)-1) - 1
                v = f"{root}{i}"
                vertices[v] = (center + .47*t, -.73 + .23*t*t)
                edges.append((root, v, value != 0, max(1, value)))
        l, r = left.count(1), right.count(1)
        label = f"({l},{r})"
        if shared is not None:
            vertices["w"] = (0, .54)
            edges.extend((root, "w", mark != 0, 1)
                         for root, mark in zip(("u", "v"), shared))
            label = rf"({l},{r}\mid {shared[0]},{shared[1]})"
        result[key].append(graph_panel(vertices, edges, label))
    assert {k:len(v) for k,v in result.items()} == {"q10":17,"q9a":10,"q9b":10,"q9c":14}
    return result


def simple_panels(archive):
    script = load_module(next(archive.rglob("check_anchored_odd_small.py")))
    f = Fraction
    degrees = defaultdict(list)
    for d in (3, 5, 7, 9):
        deficit = f(2*d-1, 4)-1
        cycle = f(1,8)-(deficit/d**2+f(2,10**9))/f(99999,100000)
        max_slack = floor((deficit/d+f(1,10**9)*d)/(f(56425,100000)*cycle))
        for total in range(1,max_slack+1,2):
            for vec in script.compositions(total,5):
                if vec == script.dihedral_representative(vec) and min(script.parts(d,vec))>0:
                    degrees[vec].append(d)
    assert Counter(map(sum,degrees)) == {1:1,3:5,5:16,7:38}
    result = defaultdict(list)
    for vec, ds in degrees.items():
        panel = [
            rf"\coordinate (c{i}) at ({90-72*i}:.53);" for i in range(5)
        ]
        panel.append(r"\draw[black!70,line width=.55pt] (c0)--(c1)--(c2)--(c3)--(c4)--cycle;")
        panel.extend(rf"\node[fill=white,inner sep=.65pt] at (c{i}) {{\({v}\)}};"
                     for i,v in enumerate(vec))
        result[sum(vec),tuple(ds)].append((vec,panel))
    return result


def signature_panels():
    result = []
    for size in range(6):
        for signature in combinations(range(5),size):
            images = [tuple(sorted((shift+sign*i)%5 for i in signature))
                      for sign in (-1,1) for shift in range(5)]
            if signature != min(images):
                continue
            lines = [rf"\coordinate (c{i}) at ({90-72*i}:.59);" for i in range(5)]
            lines.append(r"\draw[sc marked] (c0)--(c1)--(c2)--(c3)--(c4)--cycle;")
            lines.extend(rf"\draw[black,line width=.45pt] (0,0)--(c{i});" for i in signature)
            lines.extend(rf"\fill (c{i}) circle[radius=1.3pt];" for i in range(5))
            lines.append(r"\draw[fill=white] (0,0) circle[radius=1.65pt];")
            label=(r"\{"+",".join(map(str,signature))+r"\}" if signature else r"\varnothing")
            lines.append(rf"\node at (0,-.76) {{\({label}\)}};")
            result.append(lines)
    assert len(result)==8
    return result


def write_figure(directory, name, sections, columns, dx, dy, caption, label,
                 headings=True):
    lines = [r"\begin{figure}[htbp]",r"\centering",
             r"\begin{tikzpicture}[font=\scriptsize,",
             r"sc marked/.style={draw=red!65!black,line width=.75pt},",
             r"sc unmarked/.style={draw=blue!65!black,line width=.68pt,dash pattern=on 1.5pt off 1.35pt}]"]
    y = 0
    for title, panels in sections:
        if headings:
            lines.append(rf"\node[inner sep=0pt] at (0,{fmt(y)}) {{{title}}};")
            y -= .89
        for start in range(0,len(panels),columns):
            row=panels[start:start+columns]
            for col,panel in enumerate(row):
                x=(col-(len(row)-1)/2)*dx
                lines.append(rf"\begin{{scope}}[shift={{({fmt(x)},{fmt(y)})}}]")
                lines.extend(panel)
                lines.append(r"\end{scope}")
            y -= dy
        y -= .15
    lines += [r"\end{tikzpicture}",rf"\caption{{{caption}}}",rf"\label{{{label}}}",r"\end{figure}"]
    (directory/name).write_text("\n".join(lines)+"\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    archive=Path(__file__).resolve().parents[1] / "multigraph"
    parser.add_argument("--output",type=Path,
                        default=archive.parents[1] / "source" / "figures")
    out=parser.parse_args().output
    out.mkdir(exist_ok=True,parents=True)
    multi=next(archive.rglob("d5_parallel_spoke_bound.py")).parent
    five=d5_panels(multi)
    seven=d7_panels(multi)
    shapes=simple_panels(archive)
    write_figure(out,"finite_simple_signatures.tex",[("",signature_panels())],4,2.45,1.65,
        "The eight possible neighborhoods of one exterior vertex on the cycle, up to rotation and reflection. "
        "The open vertex is $x$. The cycle vertices are indexed clockwise from the top. "
        "A spoke indicates adjacency to $x$ and can be marked or unmarked.",
        "fig:finite-simple-signatures",False)
    write_figure(out,"finite_five_spokes.tex",[("",five)],4,2.72,1.65,
        "The 21 root configurations at degree five and their upper bounds on $m$. "
        "The two upper vertices are the roots. Solid edges are marked and dashed edges are unmarked. "
        "Two arcs between a pair of vertices denote two copies.",
        "fig:finite-five-spokes",False)
    write_figure(out,"finite_seven_disjoint.tex",[("",seven["q10"])],5,2.55,1.40,
        "The 17 degree-seven configurations with $q=10$. The label gives the numbers "
        "of marked spokes at the left and right roots. Solid edges are marked and dashed edges are unmarked.",
        "fig:finite-seven-disjoint",False)
    write_figure(out,"finite_seven_nine_separate.tex",[
        ("Nine single spokes",seven["q9a"]),("One double spoke and eight single spokes",seven["q9b"])],
        5,2.55,1.40,
        "The 20 degree-seven configurations with $q=9$ and disjoint root neighborhoods "
        "outside the root pair. Each label counts only the marked single spokes at the two roots.",
        "fig:finite-seven-separate")
    write_figure(out,"finite_seven_shared.tex",[("",seven["q9c"])],5,2.55,1.75,
        "The 14 degree-seven configurations with a common neighbor of the roots. "
        "The first two entries count the marked spokes to private neighbors of the two roots. "
        "The last two entries indicate which spokes to the common neighbor are marked.",
        "fig:finite-seven-shared",False)
    for levels,file,label in [((1,3,5),"low","low"),((7,),"seven","seven")]:
        groups=[(rf"\(R={r},\quad D\in\{{{','.join(map(str,ds))}\}}\)",
                 [p for _,p in sorted(entries)])
                for (r,ds),entries in sorted(shapes.items()) if r in levels]
        sums="$R=1,3,5$" if len(levels)>1 else "$R=7$"
        caption=(f"Five-cycle slack vectors with {sums}. "
                 "The five entries are read clockwise from the top. "
                 "Each heading lists the degrees for which the vector satisfies "
                 "the slack bound and all five parts are nonempty.")
        write_figure(out,f"finite_simple_slack_{file}.tex",groups,8,1.50,1.28,caption,
                     f"fig:finite-simple-slack-{label}")


if __name__=="__main__":
    main()
