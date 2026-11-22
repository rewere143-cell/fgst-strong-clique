"""Render the order-23 templates from the two archived input lists."""

import ast
from collections import Counter, defaultdict
from itertools import permutations, product
import json
from math import cos, pi, sin
from pathlib import Path
import re
import runpy


PROJECT = Path(__file__).resolve().parents[2]
FIGURES = PROJECT / "source" / "figures"
ARCHIVE = PROJECT / "reproducibility" / "multigraph"


def canonical(edges):
    """Order the connected components and canonicalize each separately."""
    adj = defaultdict(set)
    for x,y in edges:
        adj[x].add(y)
        adj[y].add(x)
    pending = set(adj)
    components = []
    while pending:
        nodes = {min(pending)}
        queue = list(nodes)
        for x in queue:
            new = adj[x] - nodes
            queue.extend(sorted(new))
            nodes.update(new)
        classes = [sorted(v for v in nodes if len(adj[v]) == d)
                   for d in sorted({len(adj[v]) for v in nodes},reverse=True)]
        forms = []
        for parts in product(*(permutations(part) for part in classes)):
            order = [v for part in parts for v in part]
            forms.append(tuple(sorted(tuple(sorted((order.index(x),order.index(y))))
                                      for x in nodes for y in adj[x] if x<y)))
        components.append(min(forms))
        pending -= nodes
    return tuple(sorted(components,key=lambda e:(-len(e),e)))


def read_instances():
    broad_dir, = ARCHIVE.rglob("chain_n23_broad")
    free_dir, = ARCHIVE.rglob("d9_order23_blue_chain")
    source = (free_dir.parent / "d9_order23_blue_chain_sat.py").read_text(encoding="utf-8")
    shapes, = [ast.literal_eval(s.value) for s in ast.parse(source).body
               if isinstance(s,ast.Assign) and isinstance(s.targets[0],ast.Name)
               and s.targets[0].id == "BLUE_SHAPES"]
    records = {}
    for path in sorted(broad_dir.glob("*.json")):
        report = json.loads(path.read_text())
        assert report["result"] == "VERIFIED_UNSAT"
        case = report["case"]
        assert not case.get("rows") and case["order"] == 23
        key = (canonical(case["blue"]),case["left"],case["right"],case["isolates"])
        assert key not in records
        records[key] = [case["beta"],case["blue_id"],False]
    assert Counter(data[0] for data in records.values()) == {3:4,4:21,5:87}
    for path in sorted(free_dir.glob("*.json")):
        report = json.loads(path.read_text())
        assert report["result"] == "VERIFIED_UNSAT"
        shape,left,isolates = re.fullmatch(r"([a-z0-9]+)_a(\d+)(?:_i(\d+))?",
                                           report["name"]).groups()
        es = shapes[shape]
        k = len({x for edge in es for x in edge})
        left,isolates = int(left),int(isolates or 0)
        key = (canonical(es),left,23-k-left-isolates,isolates)
        assert key in records and not records[key][2]
        records[key][2] = True
    assert sum(data[2] for data in records.values()) == 18
    return sorted(records.items(),key=lambda pair:(pair[1][:2],pair[0][1:]))


def draw_component(edges):
    n = max(max(edge) for edge in edges)+1
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if n == 2:
        return [(0,0),(2.4,0)],2.4
    if len(edges) == n-1:
        if max(map(len,adj)) == 2:
            x = min(v for v in range(n) if len(adj[v]) == 1)
            walk = [x]
            while len(walk)<n:
                x, = adj[x]-set(walk)
                walk.append(x)
            coords = {v:(j*1.45,(j%2)*1.4) for j,v in enumerate(walk)}
        else:
            root = max(range(n),key=lambda x:len(adj[x]))
            coords = {}
            leaf = 0
            def place(v,parent,depth):
                nonlocal leaf
                children = sorted(adj[v]-{parent})
                if children:
                    x = sum(place(w,v,depth+1) for w in children)/len(children)
                else:
                    x = 1.65*leaf
                    leaf += 1
                coords[v] = (x,1.9*depth)
                return x
            place(root,None,0)
    else:
        def score(order):
            pos = {v:i for i,v in enumerate(order)}
            intervals = [sorted((pos[u],pos[v])) for u,v in edges]
            crosses = sum(a<c<b<d or c<a<d<b for a,b in intervals for c,d in intervals)
            length = sum(min(b-a,n-b+a)**2 for a,b in intervals)
            return crosses,length,order
        order = min(((0,)+tail for tail in permutations(range(1,n))),key=score)
        coords = {v:(1.9*cos(2*pi*i/n+pi/2),1.9*sin(2*pi*i/n+pi/2))
                  for i,v in enumerate(order)}
    xmin,xmax = min(x for x,y in coords.values()),max(x for x,y in coords.values())
    ymid = (min(y for x,y in coords.values())+max(y for x,y in coords.values()))/2
    return [(coords[v][0]-xmin,coords[v][1]-ymid) for v in range(n)],xmax-xmin


def draw_shape(shape):
    rows = [[]]
    for edges in shape:
        coords,width = draw_component(edges)
        if rows[-1] and sum(part[2]+1.6 for part in rows[-1])+width>12.3:
            rows.append([])
        rows[-1].append((edges,coords,width))
    out = []
    for j,row in enumerate(rows):
        width = sum(part[2] for part in row)+1.6*(len(row)-1)
        x0 = (14.8-width)/2
        y0 = 6.4+((len(rows)-1)/2-j)*4.3
        for edges,coords,width in row:
            coords = [(x0+x,y0+y) for x,y in coords]
            segments = " ".join(f"({coords[u][0]:.2f},{coords[u][1]:.2f})--"
                                f"({coords[v][0]:.2f},{coords[v][1]:.2f})" for u,v in edges)
            out.append(r"\draw[black!78,line width=.43pt] "+segments+";")
            out.extend(fr"\fill ({x:.2f},{y:.2f}) circle[radius=.38mm];" for x,y in coords)
            x0 += width+1.6
    return "\n".join(out)


def panel(key,free):
    shape,a,c,i = key
    star = r"^{*}" if free else ""
    cell = .83
    mx,my = 21-cell*c/2,6.5-cell*a/2
    output = [r"\begin{tikzpicture}[x=1mm,y=1mm,baseline=0mm]",
              r"\path[use as bounding box] (0,-1) rectangle (27,11);",
              draw_shape(shape),
              fr"\begin{{scope}}[shift={{({mx:.3f},{my:.3f})}},x={cell}mm,y={cell}mm]",
              fr"\fill[blue!65!black] (0,0) rectangle (1,{a}) (0,{a-1}) rectangle ({c},{a});"]
    lines = [f"({x},0)--({x},{a})" for x in range(c+1)]
    lines += [f"(0,{y})--({c},{y})" for y in range(a+1)]
    output += [r"\draw[black!48,line width=.16pt] "+" ".join(lines)+";",
               r"\end{scope}",
               fr"\node[font=\scriptsize,inner sep=0pt] at (13,.35) {{$({a},{c},{i}){star}$}};",
               r"\end{tikzpicture}"]
    return "\n".join(output)


def matrix_cell(rows, label, size=.97):
    """A seven-by-seven marked array, written explicitly for the editable TeX."""
    lines = [r"\begin{tikzpicture}[x=1mm,y=1mm,baseline=0mm]",
             r"\path[use as bounding box] (0,-.7) rectangle (21.5,11.9);",
             fr"\begin{{scope}}[shift={{(7.0,3.4)}},x={size}mm,y={size}mm]"]
    cells = [f"({j},{6-i}) rectangle ({j+1},{7-i})"
             for i,row in enumerate(rows) for j in range(7) if row & (1<<j)]
    if cells:
        lines.append(r"\fill[black!72] "+" ".join(cells)+";")
    grid = [f"({j},0)--({j},7) (0,{j})--(7,{j})" for j in range(8)]
    lines.extend([r"\draw[black!47,line width=.16pt] "+" ".join(grid)+";",
                  r"\end{scope}",r"\node[inner sep=0pt,font=\scriptsize] at (10.5,1.1) {$"
                  +label+r"$};",r"\end{tikzpicture}"])
    return "\n".join(lines)


def q14_figures():
    connected = runpy.run_path(str(next(ARCHIVE.rglob("d9_q14_connected_spokes.py"))))
    # Independent permutations of the two seven-vertex sides and their interchange.
    tables = [bytes(sum(1<<p[j] for j in range(7) if mask>>j&1)
                    for mask in range(128)) for p in permutations(range(7))]
    by_shape = defaultdict(Counter)
    for budget in range(1,31):
        inputs = {rows for args in connected["first_rows"](budget)
                  for rows in connected["graphs"](*args)}
        for rows in inputs:
            transpose = tuple(sum((row>>j&1)<<i for i,row in enumerate(rows))
                              for j in range(7))
            form = min(tuple(sorted(tab[row] for row in matrix))
                       for tab in tables for matrix in (rows,transpose))
            by_shape[form][budget] += 1
    assert sum(sum(profile.values()) for profile in by_shape.values()) == 102
    connected_cells = []
    for rows,counts in sorted(by_shape.items(),key=lambda a:(sum(x.bit_count() for x in a[0]),a[0])):
        label = ",".join(str(b)+(f"^{{[{n}]}}" if n>1 else "") for b,n in sorted(counts.items()))
        connected_cells.append(matrix_cell(rows,label))
    split = runpy.run_path(str(next(ARCHIVE.rglob("d9_q14_split_spokes.py"))))
    parts = defaultdict(int)
    for sides in split["blocks"](7,7):
        count = 49-sum(x*y for x,y in sides)
        if count<=30:
            oriented = tuple(sorted(sides,reverse=True))
            flipped = tuple(sorted(((y,x) for x,y in sides),reverse=True))
            parts[min(oriented,flipped)] += 1
    assert len(parts) == 33 and sum(parts.values()) == 58
    split_cells = []
    total = 0
    for blocks,n in sorted(parts.items(),key=lambda pair:(len(pair[0]),pair[0])):
        cut = 49-sum(x*y for x,y in blocks)
        # Every off-component pair is adjacent in the host.
        left = [j for j,(x,y) in enumerate(blocks) for _ in range(x)]
        right = [j for j,(x,y) in enumerate(blocks) for _ in range(y)]
        rows = tuple(sum(1<<j for j,c in enumerate(right) if c!=r) for r in left)
        bound = 30-cut
        label = "0" if not bound else fr"0\!-\!{bound}"
        if n>1:
            label += fr"^{{[{n}]}}"
        total += n*(bound+1)
        split_cells.append(matrix_cell(rows,label))
    assert total == 174
    groups = [("connected", connected_cells[:35],
               "Cross adjacencies tested in the connected case, part 1 of 2."),
              ("connected-last", connected_cells[35:],
               "Cross adjacencies tested in the connected case, part 2 of 2."),
              ("split", split_cells,
               "Forced cross adjacencies when each component of the graph of nonadjacent pairs has order at most nine.")]
    out = ["% Generated from d9_q14_connected_spokes.py and d9_q14_split_spokes.py."]
    for kind,cells,caption in groups:
        out += [r"\begin{figure}[!htbp]",r"\centering",
                r"\begin{tabular}{@{}c@{\hspace{1.6mm}}c@{\hspace{1.6mm}}c@{\hspace{1.6mm}}c@{\hspace{1.6mm}}c@{}}"]
        for i in range(0,len(cells),5):
            out.append(" &\n".join(cells[i:i+5])+r" \\[.4mm]")
        out += [r"\end{tabular}",r"\caption{"+caption+r"}",
                r"\label{fig:nine-qfourteen-"+kind+"}",r"\end{figure}",""]
    (FIGURES/"nine_qfourteen_templates.tex").write_text("\n".join(out),encoding="utf-8")
    print(len(connected_cells),"distinct connected-branch matrices for 102 inputs;",
          len(split_cells),"component profiles for 174 inputs.")


def main():
    records = read_instances()
    groups = [records[:4],records[4:25],records[25:47],records[47:69],
              records[69:91],records[91:]]
    output = ["% Generated by generate_nine_templates.py from the archived order-23 instances."]
    for index,group in enumerate(groups,1):
        beta = group[0][1][0]
        assert all(data[0] == beta for key,data in group)
        placement = "[!htbp]"
        if index == len(groups):
            output.append(r"\FloatBarrier")
            placement = "[H]"
        output += [r"\begin{figure}" + placement,r"\centering",
                   r"\begin{tabular}{@{}c@{\hspace{2.5mm}}c@{\hspace{2.5mm}}c@{\hspace{2.5mm}}c@{}}"]
        for i in range(0,len(group),4):
            row = [panel(key,data[2]) for key,data in group[i:i+4]]
            output.append(" &\n".join(row)+r" \\[.5mm]")
        output.append(r"\end{tabular}")
        part = f", part {index-2} of 4" if beta == 5 else ""
        caption = "Order-23 templates with "+str(beta)+" unmarked edges"+part+"."
        if index == 1:
            caption += r" Each panel gives the unmarked graph, the chain matrix and $(a,c,i)$."
        if any(data[2] for key,data in group):
            caption += r" Starred templates also occur in the triangle-free list."
        output += [r"\caption{"+caption+"}",fr"\label{{fig:nine-chain-{index}}}",r"\end{figure}",""]
    (FIGURES/"nine_chain_templates.tex").write_text("\n".join(output),encoding="utf-8")
    print("112 templates,",sum(data[2] for key,data in records),"shared.")
    q14_figures()


if __name__ == "__main__":
    main()
