"""Refresh links between the paper and supplement after compiling both documents."""

import argparse
from pathlib import Path
import re


SOURCE = Path(__file__).resolve().parent
IMPORT = re.compile(r"\\input\{([^{}]+)\}")
LABEL_FILES = {"main-supplement-labels", "supplementary-main-labels"}


def manuscript(name):
    content = (SOURCE / (name + ".tex")).read_text(encoding="utf-8-sig")
    content = re.sub(r"(?<!\\)%[^\n]*", "", content)
    return IMPORT.sub(lambda m: "" if m[1] in LABEL_FILES else manuscript(m[1]), content)


def external_labels(name, aux, pdf, destination):
    content = manuscript(name)
    local = set(re.findall(r"\\label\{([^{}]+)\}", content))
    wanted = set(re.findall(r"\\(?:ref|eqref|pageref)\{([^{}]+)\}", content)) - local
    labels = {}
    for line in aux.read_text(encoding="utf-8").splitlines():
        match = re.match(r"\\newlabel\{([^{}]+)\}\{\{([^{}]+)\}\{\d+\}", line)
        if match and match[1] in wanted:
            anchor = re.search(r"\{([^{}]+)\}\{\}\}$", line)
            if anchor is None:
                raise ValueError(f"Cannot read destination of {match[1]} in {aux}")
            labels[match[1]] = (match[2], anchor[1])
    missing = wanted - labels.keys()
    if missing:
        raise ValueError(f"Cross-references missing in {aux}: {', '.join(sorted(missing))}")
    rows = ["% References from this document to " + pdf + "."]
    for key, (number, anchor) in sorted(labels.items()):
        rows.append(r"\newlabel{"+key+"}{{"+number+"}{}{}{"+anchor+"}{"+pdf+"}}")
    target = SOURCE / (destination + ".tex")
    body = "\n".join(rows) + "\n"
    changed = not target.exists() or target.read_text(encoding="utf-8") != body
    if changed:
        target.write_text(body, encoding="utf-8", newline="\n")
    print(f"{name}: {len(labels)} links to {pdf}")
    return changed


def refresh(main_aux, supplement_aux):
    first = external_labels("main", supplement_aux, "supplementary.pdf", "main-supplement-labels")
    second = external_labels("supplementary", main_aux, "fgst_conjecture.pdf", "supplementary-main-labels")
    return first or second


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--main-aux", default=SOURCE/"main.aux", type=Path)
    parser.add_argument("--supplement-aux", default=SOURCE/"supplementary.aux", type=Path)
    args = parser.parse_args()
    refresh(args.main_aux, args.supplement_aux)
