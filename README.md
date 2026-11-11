# Independent Comparator receipts for OpenAI's 7/8 zero-free theorem and Anthropic's zeta23, with the MNF.RH library judged on each

Joey Messina, 2026-10-29; extended 2026-11-04 and 2026-11-11. One record, twenty-one tarballs (the
kit, nine add-ons, eleven receipt bundles), every hash re-derivable with `./verify_deposit.sh`.

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
as a further run, with its own challenge file (every proof `sorry`) and, from v2 on, no definition
holes, so that the body of every definition a claimed statement refers to is compared:

3. **MNF.RH on OpenAI's tree, v1**: 40 theorems, ACCEPTED, 2026-10-28.
4. **MNF.RH on OpenAI's tree, v2**: 43 theorems, 17 definitions (bodies compared), ACCEPTED,
   2026-10-28.
5. **MNF.RH on OpenAI's tree, v3**: 87 theorems, 41 definitions, ACCEPTED, 2026-10-29. Adds the
   counting vocabulary, the reductions (each corpus "attack" as an ↔), the Schrödinger bridge
   with the Sturm–Liouville simplicity theorem, and the conditional gap-density theorem.
6. **MNF.RH on Anthropic's tree**: 62 theorems, 23 definitions, Lean kernel and NanoDa, ACCEPTED,
   2026-10-29: zeta23's Theorems A–D restated over MNF's definitions by definitional
   delegation, plus the counting restatements.

(Six runs and six receipt bundles; runs 2 and 6 share the zeta23 tree and one deposited add-on.)

Added 2026-11-04 (runs 7–10) and 2026-11-11 (run 11), five more runs on the zeta23 tree, each
re-judging the previous one plus new modules (details: `DEPOSIT_MAP.md` §10 and `notes/density-field-2026-11-03/`):

7. **The density field** (`zeta23-density`, add-on v2): 124 theorems, 66 definitions, Lean kernel
   and NanoDa, ACCEPTED 2026-11-03. `NcountSuperlinear` becomes a theorem (zeta23's Riemann–von
   Mangoldt formula); off-line zeros ≤ (1/3 + ε)·N(0,T) (zeta23's Theorem B); the "for every fixed
   δ" density versus density on the line itself; the strip model; the MNF2 injection/ejection
   algebra; the first lemmas toward Bohr–Landau.
8. **Bohr–Landau for δ > 1/6** (`zeta23-density-v3`, add-on v3): 270 theorems, ACCEPTED
   2026-11-03, with the uniform mean square of ζ for Re s ≥ 2/3.
9. **Bohr–Landau for every δ > 0** (`zeta23-density-v4`, add-on v4): 334 theorems, 81 definitions,
   ACCEPTED 2026-11-04. The first-derivative test for smooth phases, the Fourier series of B₂,
   Euler–Maclaurin for ζ, the sharp approximate formula, the classical O(T) mean square of ζ on
   the lines σ > 1/2, and from them `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau`; so the
   density-one theorem now has exactly one hypothesis, the spectral gap
   (`MNF.RH.onLineDensityOne_of_gap_only`). Bohr–Landau (1914) formalized, not new mathematics.
10. **The reservoir mass and a zero-density estimate with a power saving** (`zeta23-density-v5`,
   add-on v5): 480 theorems, 98 definitions, Lean kernel and NanoDa, ACCEPTED 2026-11-04.
   `MNF/RH/ReservoirMass.lean`: the total displacement of the zeros from the line,
   Σ m(ρ)·|Re ρ − 1/2| over 0 < Im ρ ≤ T, is the layer-cake integral ∫₀^{1/2} NOff(δ) dδ and is
   ≤ A·T·(log T)^{3/5}, so the mean displacement per zero tends to 0 (far weaker than Littlewood
   1924 and Selberg 1946). `Zeta23/Density/StripDensity.lean`: `Zeta23.Density.density_single_window`,
   Carlson's method in single-window form — for 1/2 < σ₁ and σ₁ − 1/2 < δ ≤ 1/2 the zeros with
   Re ρ − 1/2 ≥ δ and 0 < Im ρ ≤ T number ≤ C·T^{1 − (2σ₁−1)²/(2σ₁)}·(1 + log T)³ (weaker than
   Carlson's 4σ₁(1 − σ₁), which is not proved). A count, not a zero-free region: it excludes no
   individual zero and leaves `SpectralGapHyp` open. Erratum: the run 9 report's "How to read
   this" block carries a stale sentence ("Bohr–Landau itself is NOT proved"), true for runs 7–8
   and false for run 9, as that report's own axiom table shows; the verdict, audit and hashes of
   run 9 are unaffected, the generator is corrected in add-on v5, and the bundle is not altered
   (`DEPOSIT_MAP.md` §10).
11. **The strip cube** (`zeta23-density-v6`, add-on v6): 534 theorems, 110 definitions, Lean kernel
    and NanoDa, ACCEPTED 2026-11-11. `MNF/RH/Cube.lean`: the strip seen through three coordinates of
    an ordered pair of zeros (the two shifted real parts and the ordinate difference). An off-line
    zero is degenerate through its mirror 1 − ρ̄; "no degenerate zero" is exactly "RH and all zeros
    simple" (`noDegenerate_iff`); the gap `SpectralGapHyp Δ` is exactly "no two distinct zeros
    within Δ of the line share an ordinate" (`spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`),
    equivalently the band's coincident mass vanishes in every window. The marginals of the pair
    measure reproduce the off-line counts and the reservoir mass; the atom at ordinate difference 0
    is bounded through the one-third theorem. Also proved on this tree: ζ has no real zero in (0, 1)
    (`riemannZeta_ofReal_ne_zero_of_mem_Ioo`), a classical fact with earlier Lean proofs elsewhere
    (`DEPOSIT_MAP.md` §10, Prior Lean work). The equivalences relocate RH, simplicity and the
    gap; they prove none of them, and the cubic small-distance law of the zeros is the GUE
    prediction, not a theorem.

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

(The sentence about `gap_below_bound_insufficient` is the report's own. The Lean statement concerns
abstract symmetric sets of reals and shows only where the squeeze from the 3/8 bound stops; it
does not decide whether a gap at such Δ implies RH. See `DEPOSIT_MAP.md` §10, Errata.)

## What the record does not claim

- Not RH, not the simple-zeros conjecture, and no new technique toward either. The library
  re-expresses RH. The conditional theorem `on_line_density_one_of_gap` of add-on v3 took two
  literature facts as explicit hypotheses; on the zeta23 tree both are now theorems (runs 7 and
  9), so density one on the line follows from the gap alone — and the gap is unchanged: RH for
  Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2. Density one on the line follows from RH and
  is not known to imply it.
- Nothing combines the two external results. The 7/8 theorem bounds how far a zero can sit from
  the line; zeta23 bounds what proportion sit on it; neither enters the other's proof, and no
  theorem here puts "2/3" and "7/8" together.
- Not a first verification of either external result: both repositories ship the Comparator
  configuration, and Anthropic reports having run it; these are repetitions by a second party, on a different machine, from pinned
  sources, with the receipts attached.
- The MNF runs are warm with respect to the external proof files by design (the checked tree is
  reused, as the kit's protocol prescribes); they are cold with respect to the library itself.
  The same holds for runs 7 to 11, which the receipts record as warm: each is cold only for the
  modules its add-on introduces. Runs 3 to 11 therefore report ACCEPTED, not the kit's PASS, which
  is reserved for cold runs.

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
| `qrh-zeta23-addon-v2.tar.gz` / `qrh-zeta23-density-receipt.tar.gz` | add-on v2 (the density field) and its report (MNF_DENSITY.md, audit, logs) | `5dc41dff…` / `975b2178…` |
| `qrh-zeta23-addon-v3.tar.gz` / `qrh-zeta23-density-v3-receipt.tar.gz` | add-on v3 (Bohr–Landau for δ > 1/6) and its report | `c0958d53…` / `0588555d…` |
| `qrh-zeta23-addon-v4.tar.gz` / `qrh-zeta23-density-v4-receipt.tar.gz` | add-on v4 (Bohr–Landau for every δ > 0) and its report | `fb74e8a2…` / `0d1919e4…` |
| `qrh-zeta23-addon-v5.tar.gz` / `qrh-zeta23-density-v5-receipt.tar.gz` | add-on v5 (the reservoir mass; a zero-density estimate with a power saving) and its report | `2d2cf058…` / `37a806b2…` |
| `qrh-zeta23-addon-v6.tar.gz` / `qrh-zeta23-density-v6-receipt.tar.gz` | add-on v6 (the strip cube; no real zero of ζ in (0, 1)) and its report | `99575a1e…` / `ca07a500…` |
| `DEPOSIT_MAP.md` | the register: what is proved, conditional, open, withdrawn, external; §10 the density field | `46a1509b…` |
| `notes/density-field-2026-11-03/` | the working notes of runs 7–11: ledger, plans, the prose reviews, the extracted receipts and dry runs, the agent sources, the numeric exploration of the first 400 zeros (cascade and cube), the Aristotle contract | |
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

- Alpöge, Furman, "More than two thirds of the zeta zeros are simple and on the critical line",
  arXiv:2608.13637 (the paper zeta23 formalizes; this record does not
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
theorem was kernel-checked and every claim here is tied to a receipt. The Lean files of runs 7–11
(2026-11-03 to 2026-11-11) were written with Claude Code, the larger ones (Bohr–Landau, the
zero-density estimate, the displacement bound, the pair-measure module) by parallel workflow agents
from written dependency plans, merged, and corrected after adversarial prose reviews, all
under Joey's direction; the four files `Zeta23/{Superlinear,OffLine,BohrLandau,MNFBridge}.lean`
were supplied by Joey. The Sturm–Liouville file
is co-authored by Aristotle (Harmonic); see NOTICE.

## sources/

The same add-ons and the kit, unpacked for browsing (`sources/qrh-comparator-kit`, `sources/qrh-mnf-addon`, `-v2`, `-v3`, `sources/qrh-zeta23-addon`, `-v2` to `-v6`). The tarballs in the root are canonical: their hashes are the ones the receipts cite; the unpacked copies are byte-identical at the time of the commit.
