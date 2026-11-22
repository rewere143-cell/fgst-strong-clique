"""Draw the slack vectors used in the degree-nine pentagon check.

Run from any directory with Python 3. The fixed triangle and triangle-free
JSON files in reproducibility/multigraph certify the list that remains
after the adjacent-anchor count. Use --check to compare the generated
LaTeX with source/figures/finite_nine_slack.tex, without overwriting it.
"""
import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MULTIGRAPH = ROOT / "reproducibility" / "multigraph"
OUTPUT = ROOT / "source" / "figures" / "finite_nine_slack.tex"

HEADER = r"""\begin{figure}[htbp]
\centering
\begingroup
\newcommand{\drawnineslack}[2]{%
  \begin{tikzpicture}[baseline=(current bounding box.center)]
    \foreach \i in {0,...,4}
      \coordinate (c\i) at ({90-72*\i}:0.53cm);
    \draw[black!75,line width=.55pt] (c0)--(c1)--(c2)--(c3)--(c4)--cycle;
    \foreach \digit [count=\i from 0] in {#1}
      \node[fill=white,inner sep=.55pt,font=\scriptsize] at (c\i) {$\digit$};
    \ifnum#2=1\relax
      \node[font=\scriptsize,inner sep=0pt] at (0,0) {$\times$};
    \fi
  \end{tikzpicture}}
\setlength{\tabcolsep}{4pt}
\begin{tabular}{@{}*{8}{c}@{}}
"""

FOOTER = r"""\end{tabular}
\endgroup
\caption{The 54 possible slack vectors for \(D=R=9\), up to rotation
and reflection. Read \(s_0,\ldots,s_4\) clockwise from the top.
The ten cycles marked \(\times\) are excluded by counting at
adjacent anchors. Each of the other 44 is checked both with and
without a marked triangle.}
\label{fig:finite-nine-slack-nine}
\end{figure}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    anchor_module, = MULTIGRAPH.rglob("d9_anchor_cases.py")
    sys.path.insert(0, str(anchor_module.parent))
    import d9_anchor_cases as anchors

    shapes = list(anchors.patterns(9))
    cut = {shape: anchors.counted_out(shape) for shape in shapes}
    assert len(shapes) == 54 and sum(cut.values()) == 10
    remaining = {anchors.case_name(shape) for shape in shapes if not cut[shape]}
    for name in ("d9_r9_triangle", "d9_r9_triangle_free"):
        directory, = MULTIGRAPH.rglob(name)
        records = sorted(directory.glob("s*.json"))
        assert {record.stem for record in records} == remaining
        for record in records:
            data = json.loads(record.read_bytes())
            assert data["result"] == "VERIFIED_UNSAT"
            assert anchors.case_name(data["settings"]["slack"]) == record.stem

    rows = []
    for start in range(0, len(shapes), 8):
        drawings = []
        for shape in shapes[start:start + 8]:
            digits = ",".join(map(str, shape))
            drawings.append(r"\drawnineslack{" + digits + "}{" + str(int(cut[shape])) + "}")
        rows.append(" &\n".join(drawings))
    result = HEADER + (r" \\[3pt]" + "\n").join(rows) + "\n" + FOOTER
    if args.check:
        if result != OUTPUT.read_text(encoding="utf-8"):
            raise SystemExit(f"The generated drawing differs from {OUTPUT}")
    else:
        OUTPUT.write_text(result, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
