#!/usr/bin/env python3
"""Check the output of the two bridge compiles and write BRIDGE.md. Called by 08_bridge.sh.

usage: bridge_check.py COND_SRC COND_OUT COND_RC UNCOND_SRC UNCOND_OUT UNCOND_RC EXPECTED REPORT
       bridge_check.py --statements UNCOND_OUT        (print the statement lines; used to make EXPECTED)

BRIDGE=OK requires
  - both compiles exited 0, with no error and no `sorry` anywhere in their output;
  - every `#print axioms` in both source files produced a report, and every report lists no axiom
    other than propext, Classical.choice, Quot.sound.

Recorded in the report but not part of the verdict: whether the statements Lean printed for the
unconditional theorems are, character for character, the ones recorded when the kit was written
(bridge/expected_statements.txt). The theorems themselves are fixed by the pinned source files;
only the printed form can vary with what else is imported.
"""
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AX_HEAD_RE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<rest>.*)$")
AX_NONE_RE = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")
DIAG_RE = re.compile(r"^\S.*?:\d+:\d+: (?P<kind>error|warning)\b")
STATEMENT_PREFIX = "MNF.Bridge78."


def parse(out):
    """Split lean's output into axiom reports, diagnostics, printed statements and the rest.

    Lean wraps long lines at 120 columns, so an axiom list can run over several lines:
        'Some.long.name' depends on axioms: [propext,
         Classical.choice,
         Quot.sound]
    and so can a printed statement (continuation lines are indented).
    """
    axioms, reports, broken, diags, statements, other = {}, {}, [], [], [], []
    lines = out.splitlines()
    i, mode = 0, None
    while i < len(lines):
        line = lines[i]
        head = AX_HEAD_RE.match(line)
        none = AX_NONE_RE.match(line)
        if head:
            buf, j = head.group("rest"), i
            while "]" not in buf and j + 1 < len(lines):
                j += 1
                buf += " " + lines[j].strip()
            if "]" in buf:
                body, tail = buf.split("]", 1)
                if tail.strip():
                    broken.append(head.group("name"))
                else:
                    axioms[head.group("name")] = sorted(a.strip() for a in body.split(",") if a.strip())
                    reports.setdefault(head.group("name"), []).append(axioms[head.group("name")])
            else:
                broken.append(head.group("name"))
            i, mode = j + 1, None
            continue
        if none:
            axioms[none.group("name")] = []
            reports.setdefault(none.group("name"), []).append([])
            mode = None
        elif DIAG_RE.match(line):
            diags.append([DIAG_RE.match(line).group("kind"), line.rstrip()])
            mode = "diag"
        elif line.startswith(STATEMENT_PREFIX):
            statements.append(line.rstrip())
            mode = "statement"
        elif mode == "statement" and line[:1] in (" ", "\t") and line.strip():
            statements.append(line.rstrip())
        elif mode == "diag":
            diags[-1][1] += "\n" + line.rstrip()
        elif line.strip():
            other.append(line.rstrip())
            mode = None
        else:
            mode = None  # a blank line ends a printed statement
        i += 1
    return {"axioms": axioms, "reports": reports, "broken": broken, "diags": diags, "statements": statements, "other": other}


def analyse(src_path, out_path, rc):
    src = Path(src_path).read_text()
    out = Path(out_path).read_text(errors="replace")
    wanted = re.findall(r"^#print axioms\s+(\S+)", src, re.M)
    p = parse(out)
    problems = []
    if int(rc) != 0:
        problems.append(f"lean exited with {rc}")
    for kind, text in p["diags"]:
        if kind == "error":
            problems.append("error: " + text.splitlines()[0][:200])
    if re.search(r"\bsorry", out):
        problems.append("the output mentions sorry")
    for name in p["broken"]:
        problems.append(f"the axiom report for {name} could not be read")
    for name in wanted:
        if name in p["broken"]:
            continue
        if name not in p["reports"]:
            problems.append(f"no axiom report for {name}")
        else:
            # every report printed for this name counts, not only the last one
            extra = sorted({a for r in p["reports"][name] for a in r} - ALLOWED)
            if extra:
                problems.append(f"{name} depends on {', '.join(extra)}")
            if len(p["reports"][name]) != 1:
                problems.append(f"{len(p['reports'][name])} axiom reports for {name}, expected exactly one")
    p["problems"] = problems
    p["wanted"] = wanted
    p["warnings"] = [text.splitlines()[0][:200] for kind, text in p["diags"] if kind == "warning"]
    return p


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--statements":
        print("\n".join(parse(Path(sys.argv[2]).read_text(errors="replace"))["statements"]))
        return
    cond_src, cond_out, cond_rc, un_src, un_out, un_rc, expected_path, report = sys.argv[1:9]
    cond = analyse(cond_src, cond_out, cond_rc)
    un = analyse(un_src, un_out, un_rc)
    problems = [f"conditional file: {p}" for p in cond["problems"]] + [f"unconditional file: {p}" for p in un["problems"]]
    expected = [l.rstrip() for l in Path(expected_path).read_text().splitlines() if l.strip()]
    same_form = un["statements"] == expected
    ok = not problems

    L = ["# MNF bridge on top of the checked 7/8 theorem", ""]
    L.append(f"**Result: {'BRIDGE-OK' if ok else 'BRIDGE-FAILED'}**")
    L.append("")
    if ok:
        L.append("Both bridge files compiled with OpenAI's Lean toolchain against the tree Comparator checked. "
                 f"All {len(cond['wanted']) + len(un['wanted'])} audited theorems depend on no axiom other than "
                 "propext, Classical.choice, Quot.sound.")
    else:
        L.append("Problems:")
        L.append("")
        L.extend(f"- {p}" for p in problems)
    L.append("")
    if ok:
        L.append("## Theorems that no longer carry the 7/8 hypothesis")
        L.append("")
        L.append("As printed by Lean (`#check`):")
    else:
        L.append("## Statements Lean printed")
        L.append("")
        L.append("NOT established by this run (see Problems above). A failed bridge check does not change the "
                 "Comparator verdict in RECEIPT.md.")
    L.append("")
    L.append("```lean")
    L.extend(un["statements"] or ["(none printed)"])
    L.append("```")
    L.append("")
    if same_form:
        L.append("These are, character for character, the statements recorded when the kit was written "
                 "(`bridge/expected_statements.txt`).")
    elif un["statements"]:
        L.append("Note: Lean printed these in a different form from the kit's record, shown below. The theorems are "
                 "fixed by the pinned source files, so this does not change what was proved; the printed form can vary "
                 "with what else is imported. Compare the two by eye and mention the difference in the report.")
        L.append("")
        L.append("```lean")
        L.extend(expected)
        L.append("```")
    L.append("")
    if ok:
        L.append("## How to read this")
        L.append("")
        L.append("- The Riemann Hypothesis is not among them. `riemannHypothesis_iff_remaining_strip_unconditional` "
                 "states what is left: no zeros with 1/2 < Re s <= 7/8. Nothing here closes that strip.")
        L.append("- `riemannHypothesis_iff_gap_unconditional` lowers the threshold at which the MNF gap hypothesis is "
                 "equivalent to RH from 1/2 to any value above 3/8. The gap hypothesis itself stays open.")
        L.append("- These statements rest on OpenAI's theorem, so they are exactly as reliable as the Comparator PASS "
                 "in RECEIPT.md.")
        L.append("- This step is an ordinary Lean compile with `#print axioms`, run inside the sandbox; it is not a "
                 "second Comparator run. The bridge's own proofs were also compiled when the kit was written (the "
                 "second file against a stand-in for OpenAI's theorem).")
        L.append("")
    L.append("## Axiom reports")
    L.append("")
    L.append("| theorem | axioms |")
    L.append("|---|---|")
    for part in (cond, un):
        for name in part["wanted"]:
            ax = part["axioms"].get(name)
            L.append(f"| `{name}` | {'(no report)' if ax is None else (', '.join(ax) if ax else 'none')} |")
    L.append("")
    w = cond["warnings"] + un["warnings"]
    if w:
        L.append("## Compiler warnings (not errors)")
        L.append("")
        L.extend(f"- `{x}`" for x in w[:40])
        L.append("")
    extra = cond["other"] + un["other"]
    if extra:
        L.append("## Other output")
        L.append("")
        L.append("```")
        L.extend(x[:200] for x in extra[:40])
        L.append("```")
        L.append("")
    Path(report).write_text("\n".join(L))
    print("\n".join(L))
    print(f"BRIDGE={'OK' if ok else 'FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
