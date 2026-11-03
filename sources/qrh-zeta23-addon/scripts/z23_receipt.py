#!/usr/bin/env python3
"""Write RECEIPT-zeta23.md and receipt.json for the zeta23 Comparator run. Called by z23_report.sh.

    z23_receipt.py QRH_WORK ADDON_DIR        prints the receipt, then VERDICT=... as the last line

Verdicts
  PASS         Comparator accepted in a cold run and every condition below held.
  INVALID      Comparator accepted but a condition did not hold (listed). Not a certification.
  REJECTED     Comparator decided against the proof (statement mismatch, extra axiom, kernel
               rejection, or a solution file that did not compile).
  ERROR        The run ended without a decision (killed, lost, machine trouble).
  INCOMPLETE   Not finished, or not started.
"""
import json
import re
import sys
from pathlib import Path

LABEL = "zeta23-main"
ACCEPT = "Your solution is okay!"
NANODA_OK = "Nanoda kernel accepts the solution"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def read(p):
    try:
        return Path(p).read_text(errors="replace")
    except OSError:
        return None


def facts_of(path):
    out, allv = {}, []
    for line in (read(path) or "").splitlines():
        parts = line.split("\t")
        if len(parts) == 3:
            out[parts[1]] = parts[2]
            allv.append(parts)
    return out, allv


def pins_of(path):
    out = {}
    for line in (read(path) or "").splitlines():
        m = re.match(r'^([A-Z0-9_]+)="([^"]*)"', line)
        if m:
            out[m.group(1)] = m.group(2)
    return out


def main():
    work, addon = Path(sys.argv[1]), Path(sys.argv[2])
    logs, receipt = work / "logs", work / "receipt"
    facts, _ = facts_of(receipt / "facts.tsv")
    pins = pins_of(addon / "PINS-zeta23.env")
    z23 = Path(facts.get("z23_dir", work / "formal-math" / pins.get("Z23_SUBDIR", "zeta23")))
    cfg_name = facts.get("config_used", pins.get("Z23_CONFIG", "comparator.json"))
    cfg = {}
    try:
        cfg = json.loads(read(z23 / cfg_name) or "{}")
    except json.JSONDecodeError:
        pass
    names = cfg.get("theorem_names", [])
    nanoda = facts.get("nanoda_enabled") == "yes"

    state = facts.get("main_state", "not-started")
    exit_s = (read(logs / f"{LABEL}.exit") or "").strip()
    log = read(logs / f"{LABEL}.log") or ""
    loglines = [l.rstrip() for l in log.splitlines() if l.strip()]
    start = (read(logs / f"{LABEL}.start") or "").strip()
    end = (read(logs / f"{LABEL}.end") or "").strip()
    run_type = (read(logs / f"{LABEL}.type") or "").strip()
    timef = read(logs / f"{LABEL}.time") or ""
    wall = re.search(r"Elapsed \(wall clock\) time.*?: (\S+)", timef)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", timef)

    problems, decision = [], None
    if state == "running" or state == "not-started":
        verdict = "INCOMPLETE"
    elif state == "lost" or not exit_s:
        verdict = "ERROR"
        problems.append("the run ended without recording an exit code (killed, rebooted, or stopped)")
    else:
        accepted = exit_s == "0" and bool(loglines) and loglines[-1] == ACCEPT
        if accepted:
            verdict = "PASS"
        else:
            exc = [l for l in loglines if l.startswith("uncaught exception:")]
            if exit_s in ("137", "143", "134") and not exc:
                verdict = "ERROR"
                problems.append(f"the job exited with {exit_s} (killed) before Comparator decided")
            elif exc:
                verdict = "REJECTED"
                decision = exc[-1]
            else:
                verdict = "ERROR"
                problems.append(f"exit {exit_s}; last line: {loglines[-1][:200] if loglines else '(empty log)'}")
        if verdict == "PASS":
            # every condition of the protocol
            def need(cond, text):
                if not cond:
                    problems.append(text)
            need(run_type == "cold", f"run type recorded by the job is {run_type!r}, not cold")
            need(facts.get(f"launch_mode_{LABEL}", "").startswith("systemd-user RestrictAddressFamilies=~AF_UNIX"),
                 "the job was not launched in the restricted systemd unit")
            need(facts.get(f"job_af_unix_{LABEL}") == "denied", "the job could create AF_UNIX sockets")
            need(facts.get("af_unix_restricted") == "yes", "the AF_UNIX probe did not confirm the restriction")
            need(facts.get("sandbox_enforcing") == "yes", "the sandbox probe did not confirm enforcement")
            need(facts.get("probes_boot_id") == facts.get(f"job_boot_id_{LABEL}") == facts.get(f"probes_boot_id_{LABEL}"),
                 "the probes and the job ran in different boots")
            need(facts.get("landrun_static") == "yes", "landrun was not confirmed static")
            need(facts.get("trusted_files_after") == "unchanged", f"trusted files after the run: {facts.get('trusted_files_after')}")
            need(facts.get("tools_after") == "unchanged", f"checker binaries after the run: {facts.get('tools_after')}")
            need(facts.get("deps_after") == "unchanged", f"compiled dependencies after the run: {facts.get('deps_after')}")
            need(facts.get("dep_lakefiles_after") == "unchanged", "the dependencies' Lake files changed")
            need(facts.get("addon_after") == "unmodified", "the add-on's files changed")
            need(facts.get("fm_commit") == pins.get("FM_COMMIT"), "the formal-math checkout was not at the pinned commit")
            need(facts.get("mathlib_commit") == pins.get("Z23_MATHLIB_COMMIT"), "Mathlib was not at the pinned commit")
            need(facts.get("comparator_commit") == pins.get("Z23_COMPARATOR_COMMIT"), "Comparator was not at the pinned commit")
            need(facts.get("lean4export_commit") == pins.get("Z23_LEAN4EXPORT_COMMIT"), "lean4export was not at the pinned commit")
            need("invalidating_override" not in facts, f"a development override was used: {facts.get('invalidating_override')}")
            need(len(names) == int(pins.get("Z23_THEOREM_COUNT", "17")), f"{len(names)} theorem names in the configuration used")
            need(not cfg.get("definition_names"), "the configuration lists definition holes")
            need(set(cfg.get("permitted_axioms", [])) == {"propext", "Quot.sound", "Classical.choice"}, "permitted axioms are not the three standard ones")
            if nanoda:
                need(NANODA_OK in log, "NanoDa was enabled but its acceptance line is not in the log")
            # audit
            audit = read(receipt / "audit.out") or ""
            if facts.get("audit_rc") not in ("skipped", None):
                need(facts.get("audit_rc") == "0", f"the audit compile exited with {facts.get('audit_rc')}")
                need(not re.search(r"\bsorry", audit), "the audit output mentions sorry")
                seen = {}
                for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
                    seen[m.group(1)] = sorted(a.strip() for a in m.group(2).split(",") if a.strip())
                for n in names:
                    if n not in seen:
                        problems.append(f"no axiom report for {n}")
                    elif set(seen[n]) - ALLOWED:
                        problems.append(f"{n} depends on {', '.join(sorted(set(seen[n]) - ALLOWED))}")
            if problems:
                verdict = "INVALID"

    kernels = "Lean's kernel" + (" and NanoDa" if nanoda else "")
    L = ["# Receipt: independent Comparator run of Anthropic's zeta23 formalization", ""]
    L.append(f"**Verdict: {verdict}**")
    L.append("")
    if verdict == "PASS":
        L.append(f"Comparator accepted the proof. Its own closing line: `{ACCEPT}`. This was a cold run: nothing of the "
                 f"challenge, the solution or the Zeta23 library had been compiled on this machine before Comparator compiled "
                 f"it in its sandbox. Kernels that replayed the proof: {kernels}.")
    elif verdict == "REJECTED":
        L.append(f"Comparator decided against the proof: `{decision}`")
    elif verdict == "INVALID":
        L.append("Comparator accepted, but a condition of the protocol did not hold (see Problems). Not a certification.")
    elif verdict == "ERROR":
        L.append("The run ended without a decision by Comparator. This says nothing about the proof.")
    else:
        L.append("No result yet: the run is still going, or was not started.")
    L.append("")
    L.append("## What was checked")
    L.append("")
    L.append(f"- Project: `{pins.get('Z23_SUBDIR', 'zeta23')}/` of {pins.get('FM_REPO')} at commit `{pins.get('FM_COMMIT')}`"
             " (Alpöge–Furman, arXiv:2608.13637, formalized by Anthropic)")
    L.append(f"- Statements: the {len(names)} theorems named in `{pins.get('Z23_CONFIG')}` (sha256 `{pins.get('SHA_Z23_CONFIG')}`), "
             f"stated in `Challenge.lean` (sha256 `{pins.get('SHA_Z23_CHALLENGE')}`), which imports only Mathlib and inlines the "
             f"definitions of `ChallengeDeps.lean` (sha256 `{pins.get('SHA_Z23_CHALLENGEDEPS')}`)")
    L.append(f"- Proof: module `Solution` and the `Zeta23` library it imports: {facts.get('z23_sources_files', '?')} files, "
             f"{facts.get('z23_sources_lines', '?')} lines, on Mathlib `{facts.get('mathlib_commit', '?')[:12]}` and {pins.get('Z23_TOOLCHAIN')}")
    L.append(f"- Configuration given to Comparator: `{cfg_name}` (sha256 `{facts.get('config_used_sha256', '?')}`); kernels: {kernels}")
    L.append("- Axioms allowed: `propext`, `Quot.sound`, `Classical.choice`; no definition holes")
    L.append(f"- Checker: Comparator `{pins.get('Z23_COMPARATOR_TAG')}` ({facts.get('comparator_commit', '?')[:12]}), lean4export "
             f"{facts.get('lean4export_commit', '?')[:12]}, landrun {facts.get('landrun_commit', '?')[:12]}"
             + (f", nanoda {facts.get('nanoda_commit', '?')[:12]}" if nanoda else "")
             + f"; {facts.get('lean_version', '?')}; toolchain binaries: {facts.get('lean_toolchain_verified', '?')}")
    L.append(f"- Launch: {facts.get(f'launch_mode_{LABEL}', '?')}; AF_UNIX sockets in the job: {facts.get(f'job_af_unix_{LABEL}', '?')}; "
             f"sandbox enforcing: {facts.get('sandbox_enforcing', '?')}; outbound TCP in the sandbox: {facts.get('sandbox_tcp', '?')}")
    L.append(f"- Run: {run_type or '?'}, started {start or '?'}, ended {end or '?'}, exit {exit_s or '?'}"
             + (f", wall clock {wall.group(1)}" if wall else "")
             + (f", largest process {int(rss.group(1)) / 1048576:.1f} GiB" if rss else "")
             + f"; machine: {facts.get(f'launch_cpus_{LABEL}', '?')} CPUs, {facts.get(f'launch_mem_gb_{LABEL}', '?')} GB RAM, "
             f"{facts.get(f'launch_swap_gb_{LABEL}', '?')} GB swap")
    L.append("")
    L.append("## The theorem names")
    L.append("")
    L.extend(f"- `{n}`" for n in names)
    L.append("")
    L.append("## The statements, as given to Comparator (the whole of `Challenge.lean`)")
    L.append("")
    L.append("```lean")
    L.append((read(z23 / "Challenge.lean") or "(Challenge.lean not readable)").rstrip())
    L.append("```")
    L.append("")
    if problems:
        L.append("## Problems")
        L.append("")
        L.extend(f"- {p}" for p in problems)
        L.append("")
    dev = read(receipt / "DEVIATIONS.md")
    L.append("## Deviations")
    L.append("")
    L.append(dev.rstrip() if dev else "none")
    L.append("")
    audit = read(receipt / "audit.out") or ""
    L.append("## Axiom reports (`scripts/PrintAxioms.lean` of the project, plain `lean`, sandboxed)")
    L.append("")
    L.append("```")
    L.append(audit.rstrip() if audit.strip() else "(none)")
    L.append("```")
    L.append("")
    L.append("## What a PASS means")
    L.append("")
    L.append("1. The theorems the proof files prove are the statements above, with every definition they mention identical on both sides.")
    L.append("2. The proofs rest on no axiom other than the three listed.")
    L.append(f"3. {kernels.capitalize()} re-checked the exported proof terms and everything they depend on, Mathlib's part included.")
    L.append("")
    L.append("## What it does not mean")
    L.append("")
    L.append("- It is not a check that the Lean statements match the paper's English, nor of the paper itself. The statements are "
             "the `Challenge.lean` printed above; read it. They are proportions of zeros in windows `(T, 2T]` for large `T`, in the "
             "ε-form shown, counted with multiplicity on the left and as distinct points on the right.")
    L.append("- It is not the Riemann Hypothesis and says nothing about any individual zero. A proportion of zeros on the line, however "
             "large, is not a statement about every zero.")
    L.append("- It is an independent repetition of a check Anthropic reports having run itself (Comparator + NanoDa, AUDIT.md of the "
             "project); it is not a registry admission and not a first verification.")
    L.append("- It trusts: Lean's kernel and the released toolchain" + (" and NanoDa" if nanoda else "") + "; Comparator and lean4export; "
             "Mathlib's definitions and its prebuilt cache; the project's challenge files and lakefile (pinned by sha256); landrun, "
             "Landlock, systemd and the Linux kernel for the sandbox; this machine and whoever operated it.")
    L.append("")
    L.append("## Facts recorded")
    L.append("")
    L.append("| key | value |")
    L.append("|---|---|")
    for k in sorted(facts):
        L.append(f"| `{k}` | {facts[k][:160]} |")
    L.append("")
    if loglines:
        L.append("## Last lines of Comparator's log")
        L.append("")
        L.append("```")
        L.extend(x[:200] for x in [l for l in loglines if "has local changes" not in l][-15:])
        L.append("```")
        L.append("")
    (receipt / "RECEIPT-zeta23.md").write_text("\n".join(L) + "\n")
    (receipt / "receipt.json").write_text(json.dumps({
        "verdict": verdict, "label": LABEL, "run_type": run_type, "exit": exit_s, "started": start, "ended": end,
        "kernels": kernels, "problems": problems, "decision": decision, "theorem_names": names,
        "repo": pins.get("FM_REPO"), "commit": pins.get("FM_COMMIT"), "subdir": pins.get("Z23_SUBDIR"),
        "config_used": cfg_name, "config_used_sha256": facts.get("config_used_sha256"),
        "challenge_sha256": pins.get("SHA_Z23_CHALLENGE"), "config_pinned_sha256": pins.get("SHA_Z23_CONFIG"),
        "toolchain": pins.get("Z23_TOOLCHAIN"), "mathlib": facts.get("mathlib_commit"),
        "comparator": facts.get("comparator_commit"), "lean4export": facts.get("lean4export_commit"),
        "landrun": facts.get("landrun_commit"), "nanoda": facts.get("nanoda_commit") if nanoda else None,
        "facts": facts,
    }, indent=2) + "\n")
    print("\n".join(L))
    print(f"VERDICT={verdict}")


if __name__ == "__main__":
    main()
