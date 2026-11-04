#!/usr/bin/env python3
"""Write MNF_DENSITY.md from the Comparator run on the density layer over the zeta23 tree and the audit
compile. Called by z23_density_report.sh (QRH zeta23 add-on v2, step B3).

MNF_DENSITY=ACCEPTED requires
  - the Comparator job finished with exit 0 and its log ends in Comparator's acceptance line, with
    NanoDa's acceptance line present (the pinned configuration enables it);
  - the job ran in the restricted unit (AF_UNIX denied), in the same boot as the sandbox probes;
  - the files the run used are unchanged afterwards;
  - the audit compile exited 0 with no error and no `sorry` in its output;
  - every theorem named in the challenge config has exactly one axiom report, listing no axiom
    other than propext, Classical.choice, Quot.sound.
Otherwise REJECTED (Comparator said no, or a condition failed) or INCOMPLETE.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AX_HEAD_RE = re.compile(r"^'(?P<name>.+)' depends on axioms: \[(?P<rest>.*)$")  # names may contain a prime (idempotent')
AX_NONE_RE = re.compile(r"^'(?P<name>.+)' does not depend on any axioms\s*$")
DIAG_RE = re.compile(r"^\S.*?:\d+:\d+: (?P<kind>error|warning)\b")
ACCEPT_LINE = "Your solution is okay!"
NANODA_OK = "Nanoda kernel accepts the solution"


def parse(out, wanted):
    axioms, reports, broken, diags, statements = {}, {}, [], [], []
    starts = tuple(n + " " for n in wanted) + tuple(n + ":" for n in wanted)
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
        elif line.startswith(starts):
            statements.append(line.rstrip())
            mode = "statement"
        elif mode == "statement" and line[:1] in (" ", "\t") and line.strip():
            statements.append(line.rstrip())
        elif mode == "diag":
            diags[-1][1] += "\n" + line.rstrip()
        else:
            mode = None
        i += 1
    return {"axioms": axioms, "reports": reports, "broken": broken, "diags": diags, "statements": statements}


def read(p):
    try:
        return Path(p).read_text(errors="replace")
    except OSError:
        return None


def facts_of(path):
    out = {}
    for line in (read(path) or "").splitlines():
        parts = line.split("\t")
        if len(parts) == 3:
            out[parts[1]] = parts[2]
    return out


def main():
    ap = argparse.ArgumentParser()
    for k in ("label", "logs", "ddir", "tree", "config", "audit-rc", "receipt"):
        ap.add_argument("--" + k, required=True)
    a = ap.parse_args()
    logs, mnfdir, tree = Path(a.logs), Path(a.ddir), Path(a.tree)
    facts = facts_of(Path(a.receipt) / "facts.tsv")
    cfg = json.loads((tree / a.config).read_text())
    wanted = cfg["theorem_names"]
    challenge_src = "\n".join(f.read_text() for f in sorted((tree / "MNFChallengesD").glob("*.lean")))
    defs = re.findall(r"^(?:noncomputable )?def (\S+)", challenge_src, re.M)

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
            if NANODA_OK not in log:
                problems.append("NanoDa's acceptance line is not in the log")
        else:
            state = "REJECTED"
            problems.append(f"Comparator exited with {exit_s}; last line: {loglines[-1][:200] if loglines else '(empty log)'}")
    if facts.get(f"job_af_unix_{a.label}") != "denied":
        problems.append("the job could open AF_UNIX sockets (or did not record it): not launched in the restricted unit")
    if not facts.get(f"launch_mode_{a.label}", "").startswith("systemd-user RestrictAddressFamilies=~AF_UNIX"):
        problems.append("the job was not launched in the restricted systemd unit")
    if facts.get(f"job_boot_id_{a.label}") != facts.get(f"probes_boot_id_{a.label}"):
        problems.append("the probes and the job ran in different boots")
    if facts.get("density_files_after") != "unchanged":
        problems.append(f"the files the run used changed afterwards: {facts.get('density_files_after')}")
    if cfg.get("definition_names"):
        problems.append(f"definition_names lists {len(cfg['definition_names'])} holes: their bodies were not compared")
    audit = read(mnfdir / "audit.out") or ""
    p = parse(audit, wanted)
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
    if state == "ACCEPTED" and problems:
        state = "REJECTED"

    L = ["# The density layer on the zeta23 tree (QRH zeta23 add-on v2, step B3)", ""]
    L.append(f"**Result: MNF_DENSITY={state}**")
    L.append("")
    L.append(f"zeta23 receipt (`RECEIPT-zeta23.md`): **{facts.get('verdict', '(not recorded)')}**. The run below is a second, separate "
             "Comparator run on the same tree: its challenge (`MNFChallengesD/*.lean`, every proof `sorry`, Mathlib only) states the "
             "theorems of the density layer and the definitions they use; its solution (`MNF.RH.DensityAll`) proves them, "
             "delegating to zeta23's theorems where it restates them. Comparator built both in its sandbox, exported both, and "
             "checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no "
             "axiom beyond propext, Quot.sound, Classical.choice; Lean's kernel and NanoDa replayed the solution.")
    L.append("")
    L.append(f"- Comparator job `{a.label}`: exit {exit_s or '?'}, started {start or '?'}, ended {end or '?'} "
             f"(warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; {facts.get('density_b2_files', '?')}; cold for every module this add-on introduces)")
    L.append(f"- launch: {facts.get(f'launch_mode_{a.label}', '(not recorded)')}; AF_UNIX sockets in the job: {facts.get(f'job_af_unix_{a.label}', '(not recorded)')}")
    L.append(f"- {len(wanted)} theorems named in the challenge config; {len(defs)} definitions in the challenge, all compared by name, type and body (definition_names is empty)")
    L.append(f"- tree: the zeta23 checkout at `{a.tree}` as checked by zeta23-main, plus the layer's files under `MNF/`, `Zeta23/` and `MNFChallengesD/`, `MNF_AuditDensity.lean`, and `lean_lib` stanzas appended to `lakefile.toml`")
    L.append(f"- layer files (sha256 listing): `{facts.get('density_files_sha256', '?')}`; lakefile.toml after the append: `{facts.get('density_lakefile_after_sha256', '?')}`")
    L.append(f"- sorries outside the claim set: {facts.get('density_sorries_outside_claims', '?')}")
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
    L.append("- `MNF/RH/GapDensity.lean` (add-on v3's file; docstrings revised): the window split under a gap and the conditional "
             "density-one theorem. `MNF/RH/Density.lean`: `NcountSuperlinear` is a theorem here (delegated to zeta23's "
             "Riemann–von Mangoldt formula); off-line zeros carry at most 1/3 + ε of N(0,T) (zeta23's Theorem B restated); "
             "`ReservoirDensityOne` (for every fixed δ, density one within δ of the line) follows from Bohr–Landau alone; "
             "`OnLineDensityOne` follows from Bohr–Landau together with a gap at some Δ > 0; Bohr–Landau is reduced, by the "
             "reflection ρ ↦ 1 − ρ̄, to its right-half form. Bohr–Landau itself is NOT proved: `Zeta23/BohrLandau.lean` names its "
             "two analytic inputs as `sorry` lemmas, which are not in the claim set and on which no claimed theorem depends.")
    L.append("- `MNF/RH/Strip.lean` and `MNF/Extension/InjectionEjection.lean`: the threshold, ejection and injection operators "
             "and the band around the line; bookkeeping with no analytic content. `Zeta23/BL/*.lean`: a Dirichlet-polynomial "
             "mean-value inequality (two forms) and Jensen-disc inequalities, Mathlib-only, the first lemmas toward Bohr–Landau.")
    L.append("- None of this proves, weakens or replaces `SpectralGapHyp` (RH for Δ ≥ 1/2; an open zero-free strip for 0 < Δ < 1/2); "
             "`OnLineDensityOne` follows from RH and is not known to imply it. Nothing here uses OpenAI's 7/8 theorem, and no "
             "sentence should put the two together as one result.")
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
    L.append((read(mnfdir / "density_sha256.txt") or "(missing)").rstrip())
    L.append("```")
    L.append("")
    if log:
        tail = [l.rstrip() for l in log.splitlines() if l.strip() and "has local changes" not in l][-12:]
        L.append("## Last lines of Comparator's log")
        L.append("")
        L.append("```")
        L.extend(x[:200] for x in tail)
        L.append("```")
    (mnfdir / "MNF_DENSITY.md").write_text("\n".join(L) + "\n")
    for x in problems:
        print("problem:", x)
    print(f"MNF_DENSITY={state}")
    sys.exit(0 if state == "ACCEPTED" else 1)


if __name__ == "__main__":
    main()
