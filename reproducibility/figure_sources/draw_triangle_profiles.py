"""Draw the triangle profiles from the archived exact enumeration."""

from pathlib import Path
import sys

project = Path(__file__).resolve().parents[2]
profile_dir, = list((project / "reproducibility" / "multigraph").rglob("finite_triangle_profiles.py"))
sys.path[:0] = [str(profile_dir.parent), str(profile_dir.parent.parent)]
from finite_triangle_profiles import triangle_profiles

output = []
for degree in (13, 15):
    triples = set(triangle_profiles(degree))
    columns = 1 + max(t for _, t, _ in triples)
    rows = 1 + max(q for _, _, q in triples)
    output.append(r"\begin{tikzpicture}[x=.46cm,y=.41cm,baseline=(current bounding box.center)]")
    output.append(r"\node[anchor=east] at (-2.8,-1) {$D=" + str(degree) + r"$};")
    output.append(r"\node[anchor=east,font=\scriptsize] at (-.4,0) {$t$};")
    for t in range(columns):
        output.append(r"\node[font=\scriptsize] at (" + str(t) + r",0) {$" + str(t) + r"$};")
    for q in range(rows):
        output.append(r"\node[anchor=east,font=\scriptsize] at (-.45," + str(-q-1) + r") {$q=" + str(q) + r"$};")
        for t in range(columns):
            values = {e for e, x, y in triples if (x, y) == (t, q)}
            if values:
                top = max(values)
                assert set(range(top+1)) == values
                output.append(r"\node[font=\scriptsize,draw=black!45,minimum width=.46cm,minimum height=.41cm,inner sep=0pt] at ("
                              + str(t) + "," + str(-q-1) + r") {$" + str(top) + r"$};")
    output.extend([r"\end{tikzpicture}", r"\par\smallskip"])

destination = project / "source" / "figures" / "triangle-profile-values.tex"
destination.write_text("\n".join(output)+"\n", encoding="utf-8", newline="\n")
