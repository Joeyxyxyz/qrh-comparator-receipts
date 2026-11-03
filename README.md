# Independent Comparator receipts for OpenAI's 7/8 zero-free theorem and Anthropic's zeta23, with the MNF.RH library judged on each

Joey Messina, 2026-10-29. One record, eleven artifacts, five receipts, every hash re-derivable
with `./verify_deposit.sh`.

## What this record is

Two public, machine-checked Lean 4 results about the zeros of the Riemann zeta function were
re-checked on one laptop, with Comparator (the Lean FRO's proof judge), under a pinned, sandboxed
protocol whose every input is held to a sha256, and a receipt was written for each run in the
checker's own words:

1. **OpenAI**, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`: ζ has no zeros with Re s > 7/8
   (github.com/openai/math, commit `adc7f124`). Verdict **PASS**, cold run, Lean kernel,
   2026-10-27, 1 h 54 min.
2. **Anthropic**, `zeta23` (Alpöge–Furman, arXiv:2608.13637, formalized by Anthropic): 17
   statements, among them that more than two thirds of the zeros are simple and on the critical
   line, in windows (T, 2T] and (0, T] (github.com/anthropics/formal-math, commit `16a5ce41`).
   Verdict **PASS**, cold run, Lean kernel and NanoDa, 2026-10-28, 21 min.

On top of each verified tree, Joey's consolidated Lean library `MNF.RH` was judged by Comparator
as a further run, with its own challenge file (every proof `sorry`) and, from v2 on, every
definition compared by name, type and body:

3. **MNF.RH on OpenAI's tree, v1**: 40 theorems, ACCEPTED, 2026-10-28.
4. **MNF.RH on OpenAI's tree, v2**: 43 theorems, 17 definitions (bodies compared), ACCEPTED,
   2026-10-28.
5. **MNF.RH on OpenAI's tree, v3**: 87 theorems, 41 definitions, ACCEPTED, 2026-10-29. Adds the
   counting vocabulary, the reductions (each corpus "attack" as an ↔), the Schrödinger bridge
   with the Sturm–Liouville simplicity theorem, and the conditional gap-density theorem.
6. **MNF.RH on Anthropic's tree**: 62 theorems, 23 definitions, Lean kernel and NanoDa, ACCEPTED,
   2026-10-29: zeta23's Theorems A–D restated over MNF's definitions by definitional
   delegation, plus the counting restatements.

(Six runs, five bundles: run 2 and run 6 share the zeta23 tree and are two bundles of one add-on.)

## What a PASS or ACCEPTED means, in the receipts' words

From `RECEIPT.md` (OpenAI's theorem):

> 1. The theorem the proof files prove is the statement above, with every definition it mentions
>    identical on both sides.
> 2. The proof rests on no axiom other than the three listed.
> 3. Lean's kernel re-checked the exported proof term and everything it depends on, Mathlib's
>    part included.
>
> It is not a check that the Lean statement matches the paper's English. The statement is a few
> lines; read it. It is not the Riemann Hypothesis. Zeros with 1/2 < Re s <= 7/8 are untouched by
> this theorem. It is one kernel (Lean's own). No second kernel was run. It trusts: Lean's kernel
> and the released Lean toolchain; Comparator and lean4export; Mathlib's definitions and its
> prebuilt cache; OpenAI's challenge file and lakefile (read when the kit was written, pinned by
> sha256); landrun, Landlock, systemd and the Linux kernel for the sandbox; this machine and
> whoever operated it.

From `MNF_LIBRARY.md` (the library on OpenAI's tree):

> The Riemann Hypothesis is not among the theorems. `riemannHypothesis_iff_gap_three_eighths` says
> the MNF gap hypothesis at any Δ > 3/8 *is* RH; `gap_below_bound_insufficient` says a gap at
> Δ ≤ 3/8 cannot give it. `riemannHypothesis_iff_remaining_strip_seven_eighths` says what is left:
> no zeros with 1/2 < Re s ≤ 7/8.

## What the record does not claim

- Not RH, not the simple-zeros conjecture, and no new technique toward either. The library
  re-expresses RH; the one conditional theorem where the gap does work
  (`on_line_density_one_of_gap`) takes two literature facts as explicit hypotheses that no Lean
  library supplies, and concludes density one on the line, which is strictly weaker than RH.
- Nothing combines the two external results. The 7/8 theorem bounds how far a zero can sit from
  the line; zeta23 bounds what proportion sit on it; neither enters the other's proof, and no
  theorem here puts "2/3" and "7/8" together.
- Not a first verification of either external result: both authors report Comparator runs of
  their own; these are repetitions by a second party, on a different machine, from pinned
  sources, with the receipts attached.
- The MNF runs are warm with respect to the external proof files by design (the checked tree is
  reused, as the kit's protocol prescribes); they are cold with respect to the library itself.

## Contents

| file | what | sha256 |
|---|---|---|
| `qrh-comparator-kit.tar.gz` | the kit: protocol, pins, 21 controls, bridge, docs | `e0745073…` |
| `qrh-receipt.tar.gz` | receipt of run 1 (RECEIPT.md, receipt.json, facts, closures, logs) | `d8670539…` |
| `qrh-mnf-addon.tar.gz` / `qrh-mnf-receipt.tar.gz` | add-on v1 and its report (MNF_LIBRARY.md, audit, logs) | `295ee9c6…` / `f9180842…` |
| `qrh-mnf-addon-v2.tar.gz` / `qrh-mnf-v2-receipt.tar.gz` | add-on v2 and its report | `933c5ba8…` / `c6142a40…` |
| `qrh-mnf-addon-v3.tar.gz` / `qrh-mnf-v3-receipt.tar.gz` | add-on v3 and its report | `3668e138…` / `023d7ada…` |
| `qrh-zeta23-addon.tar.gz` | the zeta23 add-on (both runs' scripts, pins, the MNF layer) | `958abb9f…` |
| `qrh-zeta23-receipt.tar.gz` / `qrh-zeta23-mnf-receipt.tar.gz` | receipts of runs 2 and 6 | `e0b9a4d9…` / `1476f568…` |
| `DEPOSIT_MAP.md` | the register: what is proved, conditional, open, withdrawn, external | `9049e04f…` |
| `CHECKSUMS.sha256`, `verify_deposit.sh` | full hashes; the verifier (hashes, verdicts, manifests, upstream statement files) | |
| `LICENSE`, `NOTICE` | Apache-2.0 for what was authored for this record; third-party items and quoted material named | |

Every add-on tarball carries its own `MANIFEST.sha256`, `README.md` and `CLAUDE.md`; every
receipt bundle carries the exact job script that ran, Comparator's full log, the recorded facts,
and the audit compile's output with every theorem's axiom report.

## How to verify

```
sha256sum -c CHECKSUMS.sha256
./verify_deposit.sh
```

The second re-reads every verdict from the bundles, checks that the library files each MNF
receipt hashed are byte-identical to those in the matching add-on tarball, checks every add-on
against its manifest, and, if online, fetches the two upstream statement files at the pinned
commits and compares them with the pins. To repeat a run, the kit's README and each add-on's
README give the commands; the kit needs a Linux machine with Landlock and a systemd user session.

## The pins

| | |
|---|---|
| OpenAI tree | commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Lean v4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; Comparator v4.34.0 `d03acab1` built with v4.34.1; lean4export `076e8e57`; landrun `811cfff5` (static) |
| Anthropic tree | commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`; Lean v4.33.0-rc2; Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`; Comparator v4.33.0-rc2 `75c730e9`; lean4export `9fb131bb`; NanoDa `68d5ca9d`; the same landrun |
| Trusted statement files | `QuasiRiemannHypothesis.lean` sha256 `065f8c9a…`; `zeta23/Challenge.lean` `6f2a4ba9…`, `ChallengeDeps.lean` `8f9a7e7b…`, `comparator.json` `610d95c6…` |

## Related identifiers

- Alpöge, Furman, "More than two thirds of the zeros of the Riemann zeta function are simple and
  on the critical line", arXiv:2608.13637 (the paper zeta23 formalizes; this record does not
  check the paper, only the Lean statements).
- https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a (artifact under test, run 1).
- https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5 (artifact under test, run 2).
- https://github.com/leanprover/comparator (d03acab1, 75c730e9) and https://github.com/leanprover/lean4export (076e8e57, 9fb131bb): the checker.
- https://github.com/Joeyxyxyz/sturm-liouville-comparator-run: the Sturm–Liouville file of add-on v3 as a standalone Lake project with its own Comparator challenge (accepted again on 2026-11-03, Lean kernel and NanoDa).

## Who did what

Joey Messina: the MNF corpus and library, the protocol, operation of every run, and the
decisions recorded in DEPOSIT_MAP.md. OpenAI and Anthropic: the theorems under test, which are
theirs and are credited as such. The kit and add-on scripts, the Lean additions of 2026-10-28/29
and these documents were produced with Claude Code (Anthropic) under Joey's direction; every
theorem was kernel-checked and every claim here is tied to a receipt. The Sturm–Liouville file
is co-authored by Aristotle (Harmonic); see NOTICE.

## sources/

The same add-ons and the kit, unpacked for browsing (`sources/qrh-comparator-kit`, `sources/qrh-mnf-addon`, `-v2`, `-v3`, `sources/qrh-zeta23-addon`). The tarballs in the root are canonical: their hashes are the ones the receipts cite; the unpacked copies are byte-identical at the time of the commit.
