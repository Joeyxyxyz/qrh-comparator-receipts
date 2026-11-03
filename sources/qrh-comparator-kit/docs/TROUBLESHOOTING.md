# When something does not go to plan

Two principles first. A failed *check* is a result: report it, do not work around it. A failed
*download* is plumbing: run the same phase again, twice at most. The kit itself is not to be
edited (it is read-only on the droplet); a bug in it is something to report.

`scripts/where.sh` shows where the protocol stands and what comes next. `scripts/status.sh
LABEL` shows one job. `scripts/show.sh` shows everything else a diagnosis needs: `show.sh log
LABEL`, `show.sh errors LABEL`, `show.sh failed`, `show.sh memory`, `show.sh machine`,
`show.sh receipt`, `show.sh deviations`. Every script prints the reason for a failure in its
last lines.

## Phase 0, system setup (root)

- `Permission denied (publickey)` for root: the SSH key chosen when the droplet was created is
  not the one in use here, or it has a passphrase and is not loaded in `ssh-agent`. Joey fixes
  this; test with `ssh root@ADDRESS true`.
- `REMOTE HOST IDENTIFICATION HAS CHANGED`: the address was used by an earlier droplet. Joey
  removes the old entry: `ssh-keygen -R ADDRESS`.
- `Could not get lock /var/lib/dpkg/lock`: the droplet was still installing updates. The script
  waits up to ten minutes for the lock; if it still fails, run `remote.sh setup` again.
- The script can be run again at any time. It never touches `~qrh/qrh-work`.

## Phase 1, preflight

| Message | Meaning | What to do |
|---|---|---|
| `running as root` | You are logged in as root. | Log in as `qrh` over SSH. |
| `Landlock is not available` or `ABI ... too old` | The kernel cannot sandbox properly. | Wrong image. Use Ubuntu 24.04 on a normal droplet. Do not continue. |
| `no usable systemd user manager` | You arrived by `su`, or phase 0 did not run. | Log in with `ssh qrh@ADDRESS`. If it persists, run phase 0 again. |
| `GB RAM: too little`, `GB free under ...: need at least 80 GB` | The machine is too small. | Joey resizes or recreates the droplet. |
| `cannot reach ...` | No network path to a download host. | Check the droplet's firewall settings. |
| WARN about RAM under 120 GB | The run may not fit in memory at steps 4 and 5. | Tell Joey before phase 6. |

## Phase 2, toolchain

- A download failed (elan, Lean, Go, landrun's modules, Comparator): run the phase again.
- `elan release archive: sha256 mismatch`, or a `Lean toolchain: ... sha256 mismatch`: what was
  downloaded is not the release that was pinned. Stop and report.
- `Comparator tag ... now points at ...` or `lean4export is at ...`: upstream moved a tag. Stop
  and report. The pins describe what was tested; a different commit is a different experiment.
- `landrun is dynamically linked`: stop and report. The reason it must be static is in
  `PROTOCOL.md`, "Precautions beyond the README".
- The build of Comparator fails: stop and report `show.sh log toolchain`. This would mean the
  toolchain override (see `PROTOCOL.md`, "The one built-in deviation") does not work here.

## Phase 3, controls

Any FAIL here stops the protocol. `show.sh failed` lists the failed controls with their last
lines. Never set a development switch to get past this.

- `a write OUTSIDE the allowed directory succeeded`, or `the proof file wrote OUTSIDE .lake
  while Comparator compiled it`: the sandbox is not enforcing.
- `socket creation succeeded under the run's unit properties`: the systemd restriction is not
  in force.
- `control-...` or `upstream-...: expected exit N and "..."`: Comparator did not judge a control
  as expected, or not for the expected reason.
- `... controls accepted and ... rejected; the kit expects exactly ...`: the set of controls
  that ran is not the audited one.

## Phase 4, fetch

- `fetch` fails with "not our ref" or similar: the audited commit is no longer served. OpenAI
  rewrote or removed it. Stop and report; the kit cannot check a commit it has not seen.
- Any `sha256 mismatch`, `tree is ...`, or `closure digest ... differs`: the files are not the
  audited ones. Stop and report.
- `OpenAI's repository has moved on to ...` is only a warning. The run checks the pinned commit;
  say in the report that a newer one exists.

## Phase 5, dependencies

- A clone fails in `lake update`: network. Run the phase again (it resumes).
- `dependency manifest after lake update (no drift): sha256 mismatch`: a dependency resolved to
  a different version than OpenAI committed. Stop and report.
- `the dependencies' Lake configuration files differ from the audited set`: stop and report.
- `lake exe cache get` fails, or the phase sits in it for more than half an hour (the download
  retries silently): `scripts/stop.sh deps`, then run the phase once more. If that fails too,
  ask Joey: Mathlib's cache server may be down, or may no longer hold this commit.
- `Mathlib is not fully up to date after the cache download`: the cache is incomplete or does
  not match. The phase stops on purpose, because continuing would cost hours and end INVALID.
  Ask Joey. The alternative is to compile Mathlib inside the sandbox instead:
  `scripts/reset_tree.sh "cache incomplete"`, then
  `scripts/detach.sh deps 05_deps.sh --mathlib-from-source`, which makes phase 6 two to three
  hours longer on 16 CPUs (an estimate) and trusts one party fewer.
- `found build output ... The tree is not cold`: something compiled files in the OpenAI tree
  outside the protocol. Tell Joey; the remedy is `scripts/reset_tree.sh "why"` and phase 5
  again.

## Phase 6, the Comparator run

`scripts/status.sh` shows the stage. The five steps:

1. building the challenge: quick with the cache, hours without
2. exporting the challenge: minutes, silent
3. building the solution: the long step, an estimated 2 to 6 hours, one line per file
4. exporting the solution and comparing: silent, memory climbs
5. replaying in the kernel: silent, one process; expected to take minutes, possibly much longer

Step 3 looks slow on a big machine and is not stuck: the proof's files import one another in a
chain about 400 deep, so most of the time only one or two of them can be compiled at once and
the other CPUs wait. The counter moving from one poll to the next is the sign of health.

No output for a long time in steps 2, 4 and 5 is normal. Look at the `process` line of the
status: while the CPU time it shows keeps growing from one poll to the next, the run is working.
The time estimates are in `README.md`, "Time and cost", with what they are based on. A run that
takes twice as long as estimated is not a failure; nobody has timed this proof before.

When the job ends, whatever its exit code, run `scripts/07_receipt.sh`. It names the verdict.

### The verdicts

- **PASS**: done. Go to phase 8.
- **REJECTED**: Comparator made a decision. Report the receipt. The kit will not run it again.
- **ERROR**: no decision. Find the cause below.
- **PROVISIONAL**: an accept from a warm run. Not a certification; a cold run is.
- **INVALID**: Comparator accepted but a condition of the protocol did not hold; the receipt
  lists which. The clean way out is to start over in a fresh work directory (end of this file),
  with Joey's agreement.
- **INCOMPLETE**: no result yet. The run is still going, or the launch never happened;
  `scripts/where.sh` says which and what to do.

### Causes of ERROR

**A file of OpenAI's does not compile** (`error:` lines naming a file under `OAI/` or a
dependency, then `build failed`, then `Child exited with 1`, in step 1 or 3; see
`show.sh errors qrh-main`). First rule out memory: if the same output contains
`exited with code 137` or `Killed`, the compiler was killed, not refuted, and the next
paragraph applies. Otherwise this is a finding, not plumbing. Report the first error with a few
lines of context. Do not edit the file.

**Out of memory.** Signs: `Child exited with 137`, `exited with code 137`, exit code 137,
`STATE=lost`, `Killed`, or `show.sh memory qrh-main` climbing towards the machine's size just
before the end. From Joey's computer, `scripts/remote.sh oom-check` reads the kernel's own
record; on the droplet that record is only readable by root.
The remedy is a bigger machine: Joey powers the droplet off, resizes it ("CPU and RAM only",
which is reversible) to the next Memory-Optimized size, and powers it on. The swap file and the
user's systemd manager come back by themselves. Tell him the highest memory figure reached, so
he can choose the size. Then the next attempt starts cold: `scripts/reset_tree.sh "why"`,
phase 5, phase 6. (If Joey wants to know quickly whether the bigger machine is enough before
paying for the full rebuild, he can ask for `scripts/06_run_comparator.sh --warm` first. Its
result is PROVISIONAL at best, and a cold run still has to follow.)

**Stack exhausted in the replay** (`deep recursion`, or `Stack overflow detected`, after
`Running Lean default kernel on solution`). Not a verdict on the proof, and not expected: every
run already gets a stack of 1 GiB, where a replay at Mathlib's scale needed less than 2 MiB in
testing. Tell Joey. The way to go again is cold with a larger limit:
`scripts/reset_tree.sh "stack exhausted in the kernel replay"`, phase 5, then
`scripts/06_run_comparator.sh --stack 8G`.

**Disk full** (`No space left on device`): `show.sh machine`. Joey adds disk; then a new cold
attempt.

**The droplet rebooted** (`STATE=lost`, and the status shows a recent boot time): find out why
before trying again.

**Anything else**: report `show.sh log qrh-main 60` and stop.

**The launch itself failed** (`06_run_comparator.sh` printed a FAIL line and
`scripts/status.sh` says `STATE=not-started`): nothing ran and nothing counts as an attempt.
Fix what the FAIL line names and run the script again.

To stop a run on purpose: `scripts/stop.sh`. The attempt is then over and the stop is recorded.

## Phase 7, receipt

`07_receipt.sh` can be run at any time and any number of times. If it reports that the OpenAI
checkout no longer verifies, or that trusted inputs changed, the verdict will be INVALID and
the receipt says what differs. Report it. Do not restore anything by hand.

## Phase 8, bridge

- `the bridge only means something after a PASS`: without a PASS there is nothing to build on.
- BRIDGE-FAILED with a Lean error in step A: the bridge file does not compile against this
  Mathlib. It was compiled against the same Mathlib commit when the kit was written, so report
  the error (`show.sh bridge`); the file's checksum is pinned and it is not to be edited.
- BRIDGE-FAILED in step B: report `show.sh bridge`, which names the problem. Lean's own output
  is in `~/qrh-work/logs/bridge_uncond.out` on the droplet.
- BRIDGE-OK with a note that the statements were printed "in a different form": not a failure.
  The theorems are fixed by the pinned source files; Lean's way of printing them can change
  with what else is loaded. Include both versions from `BRIDGE.md` in the report so Joey can
  compare them.

A bridge failure does not touch the Comparator verdict.

## A new session, a dropped connection

Nothing is lost. Detached jobs keep running on the droplet. In a new session run
`scripts/where.sh` and carry on from what it shows. If Claude Code runs on Joey's computer,
phases 1 to 5, the receipt and the bridge only advance while that computer is awake; the long
run in phase 6 does not need it.

## Starting over completely

To discard everything and begin again from phase 1, with Joey's agreement: fetch the receipt
bundle first if there is anything in it worth keeping, then, as `qrh` on the droplet,
`rm -rf ~/qrh-work`. Or destroy the droplet and create a new one, which is cleaner.

A replaced kit also means starting over this way. The records one version of the kit leaves
are not what another version expects, and a receipt built from a mixture would be INVALID.
