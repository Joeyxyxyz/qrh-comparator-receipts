#!/usr/bin/env python3
"""Turn the recorded facts and logs into a verdict and a receipt. Called by 07_receipt.sh.

usage: receipt.py QRH_WORK KIT_DIR            write RECEIPT.md and receipt.json, print the receipt
       receipt.py --classify QRH_WORK LABEL   print the outcome of the current attempt of a run:
                                              none | ACCEPTED | REJECTED | ERROR | NO_EXIT
       receipt.py --decided QRH_WORK          print one line if an attempt of the main run has
                                              settled the case (a rejection, or an accept in a
                                              cold run); print nothing otherwise

Verdicts
  PASS         Comparator accepted in a cold run and every condition of the protocol held.
  PROVISIONAL  Comparator accepted in a warm run (files compiled by an earlier attempt were
               reused). Informative, not a certification.
  INVALID      Comparator accepted, but a condition of the protocol did not hold. Not a certification.
  REJECTED     Comparator reached a decision and it was "no".
  ERROR        The run ended without a decision by Comparator (out of memory, crash, killed, or
               a file that did not compile). If the cause is the machine, this says nothing about
               the proof.
  INCOMPLETE   The run has not finished, or has not been started.
"""
import json
import re
import sys
import time
from pathlib import Path

FINAL_ACCEPT_LINE = "Your solution is okay!"
KERNEL_ACCEPT_LINE = "Lean default kernel accepts the solution"
# Texts of the exceptions with which Comparator announces a decision against the proof: from its
# statement comparison and axiom check (Comparator/Compare.lean, Comparator/Axioms.lean), from the
# kernel replay (Lean/Replay.lean) and from its check of the quotient constants (Main.lean).
DECISION_RE = re.compile(
    r"Illegal axiom detected|do(es)? not match|kind don't match|not found in (solution|challenge)"
    r"|Constant not found|is not a (theorem|definition)|while replaying declaration|kernel rejected the solution"
    r"|Invalid (constructor|recursor)|No such (constructor|recursor)"
    r"|Quotient constant mismatch|Could not find quotient constant"
)
# Lines Comparator prints itself, just before the exception, when the kernel or its own check of
# the quotient constants says no. They make a rejection whatever the exception text is.
REJECT_LINES = ("Lean default kernel rejects the solution", "Quotient post-check rejects the solution")
# The kernel giving up for lack of a resource is not a decision. Only its own message, at the
# start of a line of the exception, counts for that: other text in an exception can come from
# the proof (names, terms) and must not be able to turn a rejection into "no decision".
NO_DECISION_RE = re.compile(r"^(?:uncaught exception: )?\(kernel\) (deep recursion detected"
                            r"|excessive memory consumption detected|deterministic timeout|interrupted)", re.M)
# For the hint in an ERROR's description only.
RESOURCE_RE = re.compile(r"deep recursion|stack overflow|out of memory|Cannot allocate memory|std::bad_alloc"
                         r"|excessive memory consumption", re.I)
KILLED_RE = re.compile(r"Child exited with 137|exited with code 137|\bKilled\b")
BUILD_FAILED_RE = re.compile(r"^error: build failed", re.M)
MAIN_LABEL, DIRICHLET_LABEL = "qrh-main", "qrh-dirichlet"


def read(path, default=""):
    try:
        return Path(path).read_text(errors="replace")
    except OSError:
        return default


def load_pins(path):
    pins = {}
    for line in read(path).splitlines():
        m = re.match(r'^([A-Z0-9_]+)="?([^"#]*)"?', line.strip())
        if m:
            pins[m.group(1)] = m.group(2).strip()
    return pins


def load_facts(path):
    last, every = {}, {}
    for line in read(path).splitlines():
        parts = line.split("\t", 2)
        if len(parts) == 3:
            last[parts[1]] = parts[2]
            every.setdefault(parts[1], []).append(parts[2])
    return last, every


def gib(n):
    return f"{int(n) / 2**30:.1f} GiB"


def attempt(logs, label, suffix=""):
    """Outcome of one attempt of a run, from its files. Log text is data: only Comparator's own
    final lines count, and an accept needs exit code 0, which nothing in the log can forge."""
    out = read(logs / f"{label}.log{suffix}")
    lines = out.splitlines()
    info = {
        "label": label,
        "suffix": suffix,
        "started": read(logs / f"{label}.start{suffix}").strip(),
        "ended": read(logs / f"{label}.end{suffix}").strip(),
        "exit_code": None,
        "job": read(logs / f"{label}.job.sh{suffix}"),
        "run_type": read(logs / f"{label}.type{suffix}").strip(),
        "last_lines": [l[:300] for l in lines[-15:]],
    }
    exit_text = read(logs / f"{label}.exit{suffix}").strip()
    if exit_text.lstrip("-").isdigit():
        info["exit_code"] = int(exit_text)
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", read(logs / f"{label}.time{suffix}"))
    if m:
        info["largest_process_peak_bytes"] = int(m.group(1)) * 1024
    m = re.search(r"Elapsed \(wall clock\) time.*?: ([0-9:.]+)", read(logs / f"{label}.time{suffix}"))
    if m:
        info["wall_clock"] = m.group(1)
    peak = 0
    for row in read(logs / f"{label}.mem.tsv{suffix}").splitlines():
        cols = row.split("\t")
        if len(cols) >= 2 and cols[1].isdigit():
            swap = int(cols[3]) if len(cols) >= 4 and cols[3].isdigit() else 0
            peak = max(peak, int(cols[1]) + swap)
    if peak:
        info["job_memory_peak_bytes"] = peak

    nonblank = [l for l in lines if l.strip()]
    final_exc, said_no = "", False
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].startswith("uncaught exception: "):
            final_exc = "\n".join(lines[i:])
            said_no = any(l.strip() in REJECT_LINES for l in lines[max(0, i - 3):i])
            break
    info["final_exception"] = final_exc.splitlines()[0][:300] if final_exc else ""
    tail = "\n".join(lines[-80:])

    if not info["started"] and not out:
        info["outcome"], info["detail"] = "NOT_STARTED", "the launch did not get as far as starting Comparator"
    elif info["exit_code"] is None:
        info["outcome"], info["detail"] = "NO_EXIT", "no exit code was recorded"
    elif info["exit_code"] == 0:
        if nonblank and nonblank[-1].strip() == FINAL_ACCEPT_LINE and KERNEL_ACCEPT_LINE in lines:
            info["outcome"], info["detail"] = "ACCEPTED", "Comparator accepted the proof"
        else:
            info["outcome"], info["detail"] = "ERROR", "exit code 0 without Comparator's closing lines; not treated as an accept"
    elif final_exc and (DECISION_RE.search(final_exc) or said_no) and not NO_DECISION_RE.search(final_exc):
        info["outcome"], info["detail"] = "REJECTED", "Comparator decided against the proof: " + info["final_exception"]
    else:
        hint = ""
        if info["exit_code"] in (137, 9) or NO_DECISION_RE.search(final_exc) or RESOURCE_RE.search(tail) or KILLED_RE.search(tail):
            hint = " (it looks like a resource limit: out of memory or stack; see docs/TROUBLESHOOTING.md)"
        elif BUILD_FAILED_RE.search(tail):
            hint = (" because a file did not compile inside the sandbox. If the machine is not the cause (memory, disk), "
                    "that is a finding about the published files: report the compiler's message")
            info["build_failed"] = True
        info["outcome"] = "ERROR"
        info["detail"] = f"the run ended with exit code {info['exit_code']} without a decision{hint}"
    return info


def settles(a):
    """After such an attempt the case is not run again: a rejection, or an accept in a cold run.
    (An accept in a warm run settles nothing; an accept of unknown kind is treated as settling.)"""
    return a["outcome"] == "REJECTED" or (a["outcome"] == "ACCEPTED" and a["run_type"] != "warm")


def all_attempts(logs, label):
    """Earlier attempts (archived with a numeric suffix), oldest first, then the current one."""
    nums = set()
    for p in logs.glob(f"{label}.*"):
        m = re.fullmatch(re.escape(label) + r"\.(?:job\.sh|log|start|exit)\.(\d+)", p.name)
        if m:
            nums.add(int(m.group(1)))
    earlier = [attempt(logs, label, f".{n}") for n in sorted(nums)]
    current = attempt(logs, label)
    has_current = bool(current["job"] or current["started"] or current["last_lines"])
    return earlier, (current if has_current else None)


def canonical_job(info, work, config):
    job = info["job"]
    return (f'lake env "{work}/tools/comparator/.lake/build/bin/comparator" "{config}"' in job
            and f'cd "{work}/openai-math/lean"' in job
            and f'export COMPARATOR_LANDRUN="{work}/tools/bin/landrun"' in job)


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--classify":
        logs = Path(sys.argv[2]) / "logs"
        _, cur = all_attempts(logs, sys.argv[3])
        print("none" if cur is None or cur["outcome"] == "NOT_STARTED" else cur["outcome"])
        return
    if len(sys.argv) == 3 and sys.argv[1] == "--decided":
        earlier, cur = all_attempts(Path(sys.argv[2]) / "logs", MAIN_LABEL)
        for a in earlier + ([cur] if cur else []):
            if settles(a):
                kind = "rejected the proof" if a["outcome"] == "REJECTED" else "accepted the proof in a cold run"
                print(f"in the attempt started {a['started'] or '(time not recorded)'} Comparator {kind}")
                return
        return

    work, kit = Path(sys.argv[1]), Path(sys.argv[2])
    logs, receipt = work / "logs", work / "receipt"
    pins = load_pins(kit / "PINS.env")
    facts, every = load_facts(receipt / "facts.tsv")
    f = facts.get
    earlier, cur = all_attempts(logs, MAIN_LABEL)
    unit_props = "systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native"

    # ---- conditions an accept must meet to count ---------------------------------------------
    problems = []

    def need(cond, text):
        if not cond:
            problems.append(text)

    need("invalidating_override" not in every,
         "a development override was used (" + ", ".join(sorted(set(every.get("invalidating_override", [])))) + ")")
    need(f("sandbox_enforcing") == "yes", "the sandbox was not shown to enforce")
    need(f("sandbox_holds_in_comparator") == "yes", "the control that tries to write outside the sandbox from inside Comparator did not pass")
    need(f("af_unix_restricted") == "yes", "the AF_UNIX restriction was not shown to be in force")
    need(f(f"probes_boot_id_{MAIN_LABEL}") and f(f"probes_boot_id_{MAIN_LABEL}") == f(f"job_boot_id_{MAIN_LABEL}"),
         "the sandbox probes were not made in the same boot of the machine as the run")
    need(f(f"launch_mode_{MAIN_LABEL}", "").startswith(unit_props),
         "the main run was not launched through systemd with the socket restriction")
    for n in range(1, 7):
        need((receipt / f"phase_{n}.ok").exists(), f"phase {n} has no completion marker")
    need(f("selftest_failures") == "0", "the control self-test did not pass")
    need(f("controls_accepted") == pins.get("CONTROLS_ACCEPT") and f("controls_rejected") == pins.get("CONTROLS_REJECT"),
         f"the controls did not come out as {pins.get('CONTROLS_ACCEPT')} accepted and {pins.get('CONTROLS_REJECT')} rejected")
    need(f("comparator_commit") == pins.get("COMPARATOR_COMMIT"), "Comparator is not at its pinned commit")
    need(f("lean4export_commit") == pins.get("LEAN4EXPORT_COMMIT"), "lean4export is not at its pinned commit")
    need(f("landrun_commit") == pins.get("LANDRUN_COMMIT"), "landrun is not at its pinned commit")
    need(f("landrun_static") == "yes", "landrun was not confirmed to be a static binary")
    need(f("lean_toolchain_verified", "").startswith("yes"), "the Lean toolchain was not checked against its pinned checksums")
    need(f("mathlib_cache_complete") in ("yes", "not used"), "the Mathlib cache was incomplete")
    need(f("tree_verified_after") == "yes", "the OpenAI checkout did not verify against the pins after the run")
    need(f("trusted_inputs_after") == "unchanged", "inputs the run trusted changed during it: " + f("trusted_inputs_after", "not checked"))
    need(f("closures_after") == "unchanged", "the proof's source files did not verify after the run")
    need(f("tools_after") == "unchanged", "the checker's binaries changed: " + f("tools_after", "not checked"))
    need(f("kit_after") == "unmodified", "the kit's files differ from the shipped ones: " + f("kit_after", "not checked"))
    need(cur is not None and bool(cur["started"]) and f("after_checks_attempt") == cur["started"],
         "the checks after the run on record were not made for this attempt")
    if cur is not None:
        need(canonical_job(cur, work, pins.get("OAI_CONFIG")), "the job that ran is not the canonical Comparator command")
    # Each attempt records its own start from inside its job, just after its start stamp; the
    # files on disk must tell the same story. (An attempt that was cut off between the two has a
    # start stamp, no record and no output: that one case is allowed for.)
    started = [a for a in earlier if a["started"]] + ([cur] if cur and cur["started"] else [])
    ran = [a for a in started if a["last_lines"] or a["exit_code"] is not None]
    recorded = len(every.get(f"attempt_started_{MAIN_LABEL}", []))
    need(len(ran) <= recorded <= len(started),
         f"{len(started)} attempts are on file ({len(ran)} of them with output) but {recorded} were recorded as started")
    decided_before = [a for a in earlier if settles(a)]
    need(not decided_before,
         "an earlier attempt had already settled the case ("
         + ", ".join(f"{a['outcome']}, {a['run_type'] or 'kind unknown'}" for a in decided_before) + "); a decided case is not run again")
    run_type = cur["run_type"] if cur else ""
    need(run_type in ("cold", "warm"), "the kind of run (cold or warm) was not recorded by the job")
    need(f(f"job_af_unix_{MAIN_LABEL}") == "denied",
         "the run's own process was not shown to be denied AF_UNIX sockets (recorded: " + f(f"job_af_unix_{MAIN_LABEL}", "nothing") + ")")

    # ---- verdict --------------------------------------------------------------------------------
    warm = run_type == "warm"
    if cur is None or cur["outcome"] == "NOT_STARTED":
        verdict, reason = "INCOMPLETE", "the run has not been started (or the tree was reset and no new attempt was made)"
    elif cur["outcome"] == "NO_EXIT":
        if f("main_state") == "lost":
            verdict, reason = "ERROR", ("the run was ended from outside before it finished and left no exit code "
                                        "(out-of-memory killer, reboot, or scripts/stop.sh; see docs/TROUBLESHOOTING.md)")
        else:
            verdict, reason = "INCOMPLETE", "the run is still going (see scripts/status.sh)"
    elif f("main_state") != "finished":
        verdict, reason = "INCOMPLETE", ("the run ended while this receipt was being written, before the checks that follow "
                                        "a run could be made; run scripts/07_receipt.sh again")
    elif cur["outcome"] == "ACCEPTED":
        if problems:
            verdict, reason = "INVALID", "Comparator accepted, but the protocol was not followed"
        elif warm:
            verdict, reason = "PROVISIONAL", "Comparator accepted, in a warm run. That is not a certification"
        else:
            verdict, reason = "PASS", "Comparator accepted the proof"
    else:
        verdict, reason = cur["outcome"], cur["detail"]

    # ---- machine-readable -----------------------------------------------------------------------
    def public(a):
        return {k: v for k, v in a.items() if k != "job"}

    data = {
        "verdict": verdict,
        "reason": reason,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "theorem": pins.get("OAI_THEOREM"),
        "repository": pins.get("OAI_REPO"),
        "commit": pins.get("OAI_COMMIT"),
        "solution_module": pins.get("OAI_SOLUTION_MODULE"),
        "config": pins.get("OAI_CONFIG"),
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "run_type": run_type,
        "current_attempt": public(cur) if cur else None,
        "earlier_attempts": [public(a) for a in earlier],
        "protocol_problems": problems,
        "facts": facts,
    }
    _, dcur = all_attempts(logs, DIRICHLET_LABEL)
    if dcur is not None and dcur["outcome"] != "NOT_STARTED":
        dv = dcur["outcome"]
        if dv == "ACCEPTED":
            ok = (not problems and canonical_job(dcur, work, pins.get("OAI_CONFIG_DIRICHLET"))
                  and f(f"launch_mode_{DIRICHLET_LABEL}", "").startswith(unit_props)
                  and f(f"job_af_unix_{DIRICHLET_LABEL}") == "denied")
            dv = "PROVISIONAL" if ok else "INVALID"
        elif dv == "NO_EXIT":
            dv = "INCOMPLETE"
        data["dirichlet"] = {"verdict": dv, "detail": dcur["detail"], "attempt": public(dcur)}
    (receipt / "receipt.json").write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

    # ---- human-readable -------------------------------------------------------------------------
    challenge = read(work / "openai-math/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean").rstrip()
    L = []
    L.append("# Receipt: independent Comparator run of OpenAI's 7/8 zero-free half-plane")
    L.append("")
    L.append(f"**Verdict: {verdict}**")
    L.append("")
    L.append(reason[:1].upper() + reason[1:] + ".")
    L.append("")
    if verdict == "PASS":
        L.append("Comparator's own closing lines: `Lean default kernel accepts the solution` and `Your solution is okay!`. "
                 "This was a cold run: nothing of the proof had been compiled on this machine before Comparator compiled it in its sandbox.")
    elif verdict == "PROVISIONAL":
        L.append("A warm run reuses files that an earlier attempt compiled, so Comparator's assumption that the proof "
                 "was never compiled before does not hold for it. Treat this as \"it will very probably pass\", not as "
                 "a pass. To certify: `scripts/reset_tree.sh`, phase 5, then `scripts/06_run_comparator.sh` with the "
                 "settings that worked here. See docs/PROTOCOL.md, \"Re-runs\".")
    elif verdict == "ERROR":
        if cur and cur.get("build_failed"):
            L.append("ERROR means Comparator did not reach a decision. Here a file failed to compile inside the sandbox. "
                     "First rule out the machine (memory, disk): if it was not the cause, this is a finding in its own "
                     "right about the published files, to be reported with the compiler's message below. It is not a "
                     "rejection by Comparator.")
        else:
            L.append("ERROR means Comparator did not reach a decision. When the cause is the machine (memory, stack, "
                     "disk, a stop), nothing can be concluded about the proof.")
    elif verdict == "INVALID":
        L.append("Do not report this as a verification. The conditions that did not hold:")
        L.append("")
        L.extend(f"- {p}" for p in problems)
    L.append("")
    L.append("## What was checked")
    L.append("")
    L.append(f"- Theorem: `{pins.get('OAI_THEOREM')}`")
    L.append(f"- Proof: module `{pins.get('OAI_SOLUTION_MODULE')}` of {pins.get('OAI_REPO')} at commit `{pins.get('OAI_COMMIT')}`")
    L.append(f"- Proof size: {int(pins.get('CLOSURE_MODULES', 0)):,} project files, {int(pins.get('CLOSURE_LINES', 0)):,} lines, "
             f"plus {pins.get('PNT_CLOSURE_MODULES')} files of PrimeNumberTheoremAnd and {pins.get('RELLICH_CLOSURE_MODULES')} of "
             "rellich-kondrachov (with OpenAI's compatibility patches), on Mathlib "
             f"`{pins.get('MATHLIB_COMMIT', '')[:12]}` and Lean {pins.get('OAI_TOOLCHAIN', '').split(':')[-1]}")
    L.append("- Axioms allowed: `propext`, `Quot.sound`, `Classical.choice`")
    L.append("- Statement, as given to Comparator (the whole challenge file):")
    L.append("")
    L.append("```lean")
    L.append(challenge)
    L.append("```")
    L.append("")
    L.append("## What a PASS means")
    L.append("")
    L.append("1. The theorem the proof files prove is the statement above, with every definition it mentions identical on both sides.")
    L.append("2. The proof rests on no axiom other than the three listed.")
    L.append("3. Lean's kernel re-checked the exported proof term and everything it depends on, Mathlib's part included.")
    L.append("")
    L.append("## What it does not mean")
    L.append("")
    L.append("- It is not a check that the Lean statement matches the paper's English. The statement is a few lines; read it.")
    L.append("- It is not the Riemann Hypothesis. Zeros with 1/2 < Re s <= 7/8 are untouched by this theorem.")
    L.append("- It is one kernel (Lean's own). No second kernel was run.")
    L.append("- It trusts: Lean's kernel and the released Lean toolchain; Comparator and lean4export; Mathlib's definitions"
             + (" and its prebuilt cache" if f("mathlib_build", "").startswith("prebuilt") else "")
             + "; OpenAI's challenge file and lakefile (read when the kit was written, pinned by sha256); "
             "landrun, Landlock, systemd and the Linux kernel for the sandbox; this machine and whoever operated it.")
    L.append("")
    L.append("## Attempts")
    L.append("")
    L.append("| # | Kind | Started (UTC) | Ended (UTC) | Exit | Outcome |")
    L.append("|---|---|---|---|---|---|")
    rows_att = earlier + ([cur] if cur else [])
    for i, a in enumerate(rows_att, 1):
        ex = "-" if a["exit_code"] is None else str(a["exit_code"])
        L.append(f"| {i} | {a['run_type'] or '-'} | {a['started'] or '-'} | {a['ended'] or '-'} | {ex} | {a['outcome']}: {a['detail']} |")
    if not rows_att:
        L.append("| - | - | - | - | - | none yet |")
    L.append("")
    L.append("## The run")
    L.append("")
    c = cur or {}
    rows = [
        ("Wall clock", c.get("wall_clock", "-")),
        ("Run type", run_type or "-"),
        ("Peak memory of the job (program memory plus swap, sampled each minute)", gib(c["job_memory_peak_bytes"]) if "job_memory_peak_bytes" in c else "-"),
        ("Peak memory, largest single process", gib(c["largest_process_peak_bytes"]) if "largest_process_peak_bytes" in c else "-"),
        ("Machine at launch", f"{f(f'launch_cpus_{MAIN_LABEL}', '?')} CPUs, {f(f'launch_mem_gb_{MAIN_LABEL}', '?')} GB RAM, {f(f'launch_swap_gb_{MAIN_LABEL}', '?')} GB swap, kernel {f('preflight_kernel', '?')}, Landlock ABI {f('landlock_abi', '?')}"),
        ("Launch", f(f"launch_mode_{MAIN_LABEL}", "-")),
        ("Inside the run's own unit", f"AF_UNIX sockets {f(f'job_af_unix_{MAIN_LABEL}', '?')}; stack limit {f(f'job_stack_kb_{MAIN_LABEL}', '?')} kB"),
        ("Sandbox enforcing / inside Comparator / AF_UNIX restricted / TCP in sandbox",
         f"{f('sandbox_enforcing', '?')} / {f('sandbox_holds_in_comparator', '?')} / {f('af_unix_restricted', '?')} / {f('sandbox_tcp', '?')}"),
        ("Controls", f"{f('controls_accepted', '?')} accepted, {f('controls_rejected', '?')} rejected (expected {pins.get('CONTROLS_ACCEPT')} and {pins.get('CONTROLS_REJECT')}); {f('upstream_controls_skipped_nanoda', '?')} nanoda-only projects skipped"),
        ("Lean", f"{f('lean_version', '-')}; release files verified: {f('lean_toolchain_verified', '-')}"),
        ("Comparator", f"{pins.get('COMPARATOR_TAG')} `{f('comparator_commit', '-')}`, built with {f('comparator_build_toolchain', '-')} (upstream pins {f('comparator_upstream_toolchain', '-')})"),
        ("lean4export", f"`{f('lean4export_commit', '-')}`"),
        ("landrun", f"`{f('landrun_commit', '-')}` ({f('landrun_version', '-')}), static: {f('landrun_static', '-')}"),
        ("Mathlib", f"`{pins.get('MATHLIB_COMMIT')}`, {f('mathlib_build', '-')}; cache complete: {f('mathlib_cache_complete', '-')}"),
        ("Compiled dependency files before the run", f"{f('deps_compiled_files', '-')} files, digest `{f('deps_compiled_digest', '-')}`"),
        ("After the run", f"OpenAI checkout verified: {f('tree_verified_after', '-')}; trusted inputs: {f('trusted_inputs_after', '-')}; proof sources: {f('closures_after', '-')}; checker binaries: {f('tools_after', '-')}; kit: {f('kit_after', '-')}"),
        ("OpenAI repository head at fetch time", f("oai_remote_head", "-")),
    ]
    L.append("| | |")
    L.append("|---|---|")
    for k, v in rows:
        L.append(f"| {k} | {v} |")
    L.append("")
    if cur and verdict not in ("PASS", "PROVISIONAL"):
        L.append("## Last lines of Comparator's output")
        L.append("")
        L.append("(Program output, reproduced as data.)")
        L.append("")
        L.append("```")
        L.extend(cur["last_lines"] or ["(no output)"])
        L.append("```")
        L.append("")
    if "dirichlet" in data:
        d = data["dirichlet"]
        L.append("## Optional second statement (Dirichlet L-functions)")
        L.append("")
        L.append(f"`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`: **{d['verdict']}**. {d['detail']}. "
                 "This is always a warm run (it reuses the proof files the main run compiled), so it can be PROVISIONAL at best.")
        L.append("")
    L.append("## Deviations from the scripted protocol")
    L.append("")
    dev = read(receipt / "DEVIATIONS.md").strip()
    L.append("One deviation is built into the kit: Comparator and lean4export have no release for Lean 4.34.1, so their "
             "v4.34.0 sources were built with the 4.34.1 toolchain. Their own regression projects were run in that "
             "configuration as part of the controls.")
    L.append("")
    L.append(dev if dev else "No others recorded.")
    L.append("")
    L.append("## Files")
    L.append("")
    L.append("`receipt.json` (this receipt, machine-readable), `facts.tsv` (every recorded fact with its time), "
             "`closure.json` (the static scan of the proof's files), `packages.tsv` (every dependency and its commit), "
             "`deps_compiled.sha256` and `mathlib_sources.sha256` (what the run trusted, file by file), and the logs, "
             "including the exact job script `qrh-main.job.sh` and Comparator's full output `qrh-main.log`.")
    L.append("")
    (receipt / "RECEIPT.md").write_text("\n".join(L))
    print("\n".join(L))
    print(f"VERDICT={verdict}")


if __name__ == "__main__":
    main()
