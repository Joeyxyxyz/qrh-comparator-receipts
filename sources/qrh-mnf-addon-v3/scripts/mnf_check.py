#!/usr/bin/env python3
"""Write MNF_LIBRARY.md from the Comparator run on the MNF.RH library and the audit compile.
Called by mnf_report.sh.

MNF_LIBRARY=ACCEPTED requires
  - the Comparator job finished with exit 0 and its log ends in Comparator's acceptance line;
  - the audit compile exited 0 with no error and no `sorry` in its output;
  - every theorem named in the challenge config has exactly one axiom report, listing no axiom
    other than propext, Classical.choice, Quot.sound.
Otherwise REJECTED (Comparator said no, or the audit found a problem) or INCOMPLETE (the job
did not finish, or its log is missing).
"""
import argparse
import json
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AX_HEAD_RE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<rest>.*)$")
AX_NONE_RE = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")
DIAG_RE = re.compile(r"^\S.*?:\d+:\d+: (?P<kind>error|warning)\b")
STATEMENT_PREFIX = "MNF.RH."
# theorems of the challenge that live in the root namespace (the Sturm–Liouville file); filled from the config
ROOT_NAMES = []
ACCEPT_LINE = "Your solution is okay!"


def parse(out):
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
        elif line.startswith(STATEMENT_PREFIX) or any(line.startswith(n + " ") or line.startswith(n + ".") or line == n or line.startswith(n + " :") for n in ROOT_NAMES):
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
            mode = None
        i += 1
    return {"axioms": axioms, "reports": reports, "broken": broken, "diags": diags, "statements": statements, "other": other}


def read(p):
    try:
        return Path(p).read_text(errors="replace")
    except OSError:
        return None


def main():
    ap = argparse.ArgumentParser()
    for k in ("label", "logs", "mnfdir", "tree", "addon", "audit-rc", "receipt", "mnf-receipt"):
        ap.add_argument("--" + k, required=True)
    a = ap.parse_args()
    logs, mnfdir, addon = Path(a.logs), Path(a.mnfdir), Path(a.addon)
    cfg = json.loads((addon / "MNFChallenges" / "RH.json").read_text())
    wanted = cfg["theorem_names"]
    ROOT_NAMES.extend(n for n in wanted if not n.startswith(STATEMENT_PREFIX))
    holes = cfg.get("definition_names") or []
    challenge_src = "\n".join(f.read_text() for f in sorted((addon / "MNFChallenges").glob("*.lean")))
    defs = re.findall(r"^(?:noncomputable )?def (\S+)", challenge_src, re.M)

    # --- the Comparator job
    log = read(logs / f"{a.label}.log")
    exit_s = (read(logs / f"{a.label}.exit") or "").strip()
    start = (read(logs / f"{a.label}.start") or "").strip()
    end = (read(logs / f"{a.label}.end") or "").strip()
    problems, state = [], "INCOMPLETE"
    if log is None or not exit_s:
        problems.append("the Comparator job left no log or no exit code")
    else:
        loglines = [l.rstrip() for l in log.splitlines() if l.strip()]
        accepted = exit_s == "0" and bool(loglines) and loglines[-1].endswith(ACCEPT_LINE)
        if accepted:
            state = "ACCEPTED"
        else:
            state = "REJECTED"
            problems.append(f"Comparator exited with {exit_s}; last line: {loglines[-1][:200] if loglines else '(empty log)'}")
    # --- the audit compile
    audit = read(mnfdir / "audit.out") or ""
    p = parse(audit)
    if int(a.audit_rc) != 0:
        problems.append(f"the audit compile exited with {a.audit_rc}")
    for kind, text in p["diags"]:
        if kind == "error":
            problems.append("audit error: " + text.splitlines()[0][:200])
    if re.search(r"\bsorry", audit):
        problems.append("the audit output mentions sorry")
    for name in p["broken"]:
        problems.append(f"the axiom report for {name} could not be read")
    for name in wanted:
        if name in p["broken"]:
            continue
        if name not in p["reports"]:
            problems.append(f"no axiom report for {name}")
        else:
            extra = sorted({x for r in p["reports"][name] for x in r} - ALLOWED)
            if extra:
                problems.append(f"{name} depends on {', '.join(extra)}")
            if len(p["reports"][name]) != 1:
                problems.append(f"{len(p['reports'][name])} axiom reports for {name}, expected exactly one")
    mfacts = read(Path(a.mnf_receipt) / "facts.tsv") or ""
    launch = [l.split("\t")[2] for l in mfacts.splitlines() if len(l.split("\t")) == 3 and l.split("\t")[1] == f"launch_mode_{a.label}"]
    afu = [l.split("\t")[2] for l in mfacts.splitlines() if len(l.split("\t")) == 3 and l.split("\t")[1] == f"job_af_unix_{a.label}"]
    if afu and afu[-1] != "denied":
        problems.append(f"the job could open AF_UNIX sockets ({afu[-1]}): not launched in the restricted unit")
    if holes:
        problems.append(f"definition_names lists {len(holes)} holes: their bodies were not compared")
    if state == "ACCEPTED" and problems:
        state = "REJECTED"

    verdict_main = ""
    facts = read(Path(a.receipt) / "facts.tsv") or ""
    for line in facts.splitlines():
        parts = line.split("\t")
        if len(parts) == 3 and parts[1] == "verdict":
            verdict_main = parts[2]

    L = ["# MNF.RH library (v3) on top of the checked 7/8 theorem", ""]
    L.append(f"**Result: MNF_LIBRARY={state}**")
    L.append("")
    L.append(f"Main kit verdict for `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`: **{verdict_main or '(not recorded)'}** "
             "(RECEIPT.md). The library run below is a second, separate Comparator run: its challenge "
             "(`MNFChallenges/RH.lean`, every proof `sorry`) states the MNF theorems and the definitions they use; "
             "its solution (`MNF.RH.Unconditional`) proves them, using OpenAI's theorem where the 7/8 region is needed. "
             "Comparator built both in its sandbox, exported both, and checked that every theorem statement and every "
"definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, "
"Classical.choice.")
    L.append("")
    L.append(f"- Comparator job `{a.label}`: exit {exit_s or '?'}, started {start or '?'}, ended {end or '?'}")
    L.append(f"- launch: {launch[-1] if launch else '(not recorded)'}; AF_UNIX sockets in the job: {afu[-1] if afu else '(not recorded)'}")
    L.append(f"- {len(wanted)} theorems named in the challenge config; {len(defs)} definitions in the challenge, "
             f"{'all compared by name, type and body (definition_names is empty)' if not holes else str(len(holes)) + ' of them listed as holes'}")
    L.append(f"- tree: a copy of the verified tree at `{a.tree}`, plus `MNF/`, `SturmLiouville/`, `MNFChallenges/`, `MNF_Audit.lean` and three `lean_lib` lines appended to `lakefile.lean`")
    if problems:
        L.append("")
        L.append("Problems:")
        L.append("")
        L.extend(f"- {x}" for x in problems)
    L.append("")
    L.append("## What was proved" if state == "ACCEPTED" else "## Statements (NOT established by this run; see Problems)")
    L.append("")
    L.append("As printed by Lean (`#check`), from the audit compile:")
    L.append("")
    L.append("```lean")
    L.extend(p["statements"] or ["(none printed)"])
    L.append("```")
    L.append("")
    L.append("## How to read this")
    L.append("")
    L.append("- Everything in `MNF/RH/Core.lean`, `Gap.lean` and `Hypotheses.lean` is proved from Mathlib alone; "
             "the theorems whose names end in `_seven_eighths` / `_three_eighths` (`Unconditional.lean`) use OpenAI's "
             "theorem and are exactly as reliable as the main kit's PASS.")
    L.append("- The Riemann Hypothesis is not among the theorems. `riemannHypothesis_iff_gap_three_eighths` says the "
             "MNF gap hypothesis at any Δ > 3/8 *is* RH; `gap_below_bound_insufficient` says a gap at Δ ≤ 3/8 cannot "
             "give it. `riemannHypothesis_iff_remaining_strip_seven_eighths` says what is left: no zeros with "
             "1/2 < Re s ≤ 7/8.")
    L.append("- `SpeiserTheorem` and `DoubleZeroForcesLeftDerivZero` are hypotheses (explicit arguments), not axioms; "
             "nothing here asserts them.")
    L.append("- `spectralGapHyp_iff_zeroFree_strip` says the gap hypothesis at `Δ` is exactly a zero-free strip "
             "`1/2 < Re s < 1/2 + Δ`; `spectralGapHyp_three_eighths_iff` is the boundary case `Δ = 3/8` with the "
             "7/8 region (zeros on `Re s = 7/8` are not excluded by it, so this is not RH).")
    L.append("")
    L.append("## Axiom reports")
    L.append("")
    L.append("| theorem | axioms |")
    L.append("|---|---|")
    for name in wanted:
        ax = p["axioms"].get(name)
        L.append(f"| `{name}` | {'(no report)' if ax is None else (', '.join(ax) if ax else 'none')} |")
    L.append("")
    w = [t.splitlines()[0][:200] for k, t in p["diags"] if k == "warning"]
    if w:
        L.append("## Compiler warnings in the audit (not errors)")
        L.append("")
        L.extend(f"- `{x}`" for x in w[:40])
        L.append("")
    L.append("## Hashes")
    L.append("")
    L.append("```")
    L.append((read(mnfdir / "library_sha256.txt") or "(missing)").rstrip())
    L.append("lakefile.lean after the append: " + (read(mnfdir / "lakefile_after_sha256.txt") or "?").strip())
    L.append("```")
    L.append("")
    if log:
        tail = [l.rstrip() for l in log.splitlines() if l.strip()][-12:]
        L.append("## Last lines of Comparator's log")
        L.append("")
        L.append("```")
        L.extend(x[:200] for x in tail)
        L.append("```")
    (mnfdir / "MNF_LIBRARY.md").write_text("\n".join(L) + "\n")
    for x in problems:
        print("problem:", x)
    print(f"MNF_LIBRARY={state}")
    sys.exit(0 if state == "ACCEPTED" else 1)


if __name__ == "__main__":
    main()
