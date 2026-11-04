# The density field — ledger of 2026-11-03

Joey Messina's laptop, zeta23 tree (`~/mnf-stageB/z23work2/formal-math/zeta23`: anthropics/formal-math
`16a5ce41`, Lean v4.33.0-rc2, Mathlib `51e6992e`), with the MNF.RH layer of add-on B2 plus the
files of this folder. Everything marked PROVED below compiles with no `sorry`, depends only on
`propext, Classical.choice, Quot.sound` (`audit.out`, 98 lines), and was accepted by Comparator
v4.33.0-rc2 `75c730e9` against the mirror challenge `MNFChallenges/Strip.lean` with every
definition compared by body, Lean kernel and NanoDa (`comparator-precheck.log`, exit 0; warm run
on the author's account, outside the QRH launcher; this is a pre-check, not a receipt).

## The question: st()-density versus N(Δ,·)-density

Shift every nontrivial zero to x = Re ρ − 1/2. Two things one can mean by "the zeros are on the
line in density":

| name | statement | Lean |
|---|---|---|
| st()-density one | for every standard δ > 0, all but a vanishing proportion of the zeros have \|x\| < δ — equivalently (`NNear_eq_nullified_count`), are sent to 0 by N(δ,·) | `MNF.RH.ReservoirDensityOne` |
| on-line density one | all but a vanishing proportion have x = 0 exactly | `MNF.RH.OnLineDensityOne` |

They differ by the order of two quantifiers: st() says ∀δ ∀ε ∃T₀, the line says ∀ε ∃T₀ with
δ = 0. In standard words "x is below every standard scale" IS "x = 0" (`eq_zero_iff_nullified_all`),
but "density one below every scale" is NOT "density one at scale 0". The gap hypothesis is exactly
the uniformity that lets the δ cross the ∃T₀: under `SpectralGapHyp Δ` the Δ-band holds no
displacement but 0, so N_near(Δ) = N₀ (`NNear_eq_N0_of_gap`) and the st()-statement at δ = Δ is
the line statement (`onLineDensityOne_of_reservoir_of_gap`). That is the gap's whole role in the
density theorem.

What feeds each: Bohr–Landau (N_off(δ; T) = O(T) for every δ > 0) gives st()-density one with no
other hypothesis, now that N(T)/T → ∞ is a theorem of the tree (`reservoirDensityOne_of_bohrLandau`).
Nothing analytic feeds the line statement except through a gap.

## Field assignments

| # | statement | status | where |
|---|---|---|---|
| 1 | N(T)/T → ∞ (`NcountSuperlinear`) | **PROVED**, unconditional: delegated to zeta23's Riemann–von Mangoldt formula | `Zeta23.ncountSuperlinear` (Superlinear.lean), `MNF.RH.ncountSuperlinear` |
| 2 | ≥ 2/3 of zeros distinct and on the line; ≥ 2/3 simple on the line; ≥ 5/6 distinct; Montgomery–Taylor constants | **PROVED**, unconditional (zeta23 Theorems A–D; restated over MNF names in B2) | `MNF.RH.Zeta23Restated` |
| 3 | off-line zeros (Re ρ ≠ 1/2, with multiplicity) ≤ (1/3 + ε)·N(0,T) eventually | **PROVED**, unconditional (Theorem B read as an upper bound) | `Zeta23.offLine_le_one_third`, `MNF.RH.offLine_le_one_third`, `NOff_le_one_third` |
| 4 | every window splits N = N_near(δ) + N_off(δ), any δ; N₀ ≤ N_near(δ); N_near(Δ) = N₀ under a gap at Δ | **PROVED** bookkeeping | `Ncount_eq_near_add_off`, `N0_le_NNear`, `NNear_eq_N0_of_gap` (Density.lean) |
| 5 | st()-density one (`ReservoirDensityOne`) | **CONDITIONAL on Bohr–Landau alone** | `reservoirDensityOne_of_bohrLandau`; from the right-half form: `reservoirDensityOne_of_right` |
| 6 | on-line density one (`OnLineDensityOne`) | **CONDITIONAL on Bohr–Landau + a gap at some Δ > 0** (v3's theorem with `NcountSuperlinear` removed) | `onLineDensityOne_of_gap`, `onLineDensityOne_of_reservoir_of_gap`, `onLineDensityOne_of_right` |
| 7 | Bohr–Landau (`BohrLandau`) | **OPEN in Lean.** Reduced sorry-free to the right half-strip (`bohrLandau_of_right`, by the reflection ρ ↦ 1 − ρ̄ with multiplicity, `NLeft_eq_NRight`); the right-half bound reduced to two named analytic inputs, both `sorry` in `Zeta23/BohrLandau.lean`: `meanSquare_strip` (∫₀ᵀ\|ζ(σ+it)\|² dt = O(T), 1/2 < σ ≤ 1) and `rightHalfBound_of_meanSquare` (Littlewood/Jensen count). The σ > 1 mean square is proved (`meanSquare_gt_one`). | `Zeta23.BL.*`, `MNF.RH.bohrLandau_of_right` |
| 8 | mean square of ζ right of the line | σ > 1: **PROVED** (trivial); 1/2 < σ ≤ 1: **OPEN**, see the plan | `Zeta23.BL.meanSquare_gt_one`, `meanSquare_strip` (sorry) |
| 9 | `SpectralGapHyp Δ` | Δ ≥ 1/2: it is RH (`riemannHypothesis_iff_gap_half`); 0 < Δ < 1/2: **OPEN** (an unknown zero-free strip next to the line). Not touched by anything here. | Hypotheses.lean, Gap.lean |
| 10 | the strip model: in the Δ-band E fixes exactly 0 and throws every other point to the edge; readings of fragmented band points are 0 (blind); the trace δ* of the exact representation is \|x\|, of an injected zero \|x\|/k → 0, of the true zero 0; a zero is on the line iff fixed by E / nullified / trace 0 at EVERY threshold; a gap at Δ ⇔ nothing is injected into the Δ-band | **PROVED** bookkeeping, no analytic content | Strip.lean (19 theorems) |
| 11 | RH; simple-zeros conjecture | not claimed, not approached | — |

## What changed against DEPOSIT_MAP.md (v3 record)

- The v3 conditional theorem `on_line_density_one_of_gap` carried two literature hypotheses. One
  of them, `NcountSuperlinear`, is now a theorem (row 1). The theorem now reads: Bohr–Landau +
  gap ⟹ density one on the line (row 6). The deposit's tarballs are untouched; this is a new
  layer on the zeta23 tree, not a re-run of anything.
- The honest split of the remaining hypothesis: Bohr–Landau is the st()-density statement's
  only input (row 5); the gap is only the st() → line conversion (row 4). Earlier prose that
  presented the gap as "doing work" in the density theorem should be read with row 4.
- Bohr–Landau itself is reduced to two analytic inputs that are named, scoped and `sorry`
  (row 7); the scoping plan for them is `BOHR_LANDAU_PLAN.md` in this folder (when present).

## On the question "doesn't signed nullification attack density"

No. The signed classes record the pairing x ↔ −x of the functional equation; every signed sum
of displacements over a symmetric window is 0 whether or not zeros are off the line. The density
statements above are counts of the unsigned class N_off(δ) (row 7 is a bound on exactly that
count), and the sign carries no information about them. Strip.lean makes the positive part of
the intuition exact: ejection, not the reading, distinguishes a true zero inside a band
(`eject_fixed_iff_zero`, `eject_band_edge`), and only the all-thresholds criterion identifies the
line (`on_line_iff_eject_fixed_all`).

## Files

- `as-received/`: the five files Joey uploaded (two versions of BohrLandau.lean; the second
  adds the σ > 1 mean square and isolates `meanSquare_strip`).
- `zeta23-tree/`: the modules as they sit on the tree: `Zeta23/{Superlinear,OffLine,BohrLandau,MNFBridge}.lean`
  (BohrLandau = the second version), `MNF/RH/GapDensity.lean` (v3's file, unchanged),
  `MNF/RH/Density.lean`, `MNF/RH/Strip.lean` (new), `MNF/Extension/InjectionEjection.lean`
  (the MNF2 algebra, rebuilt at this pin), the mirror challenge modules and `Strip.json`,
  `MNF_AuditDensity.lean`.
- `audit.out`, `comparator-precheck.log`, `gen_density_challenge.py`.

## Addendum, same day (later): review, lemmas, plan, add-on

- **Prose review applied.** An adversarial reviewer (workflow agent; `plan/REVIEW_2026-11-03.md`) found
  37 sentences to tighten in Density.lean, Strip.lean, GapDensity.lean (tree copy) and MNFBridge.lean:
  "st()-density" is a nickname for the classical for-every-fixed-δ statement (no nonstandard object is
  formalized); "the gap does nothing else" was rhetoric (literally shown: the gap enters only through
  `NNear_eq_N0_of_gap`, at δ = Δ); "strictly weaker than RH" is not kernel-checkable (now: "follows
  from RH and is not known to imply it"); `band_injection_blind` covers equal k-fold splittings only;
  `band_trivial_of_gap` is `SpectralGapHyp Δ` restated and says nothing about the `inject` operator;
  Bohr–Landau is a 1914 theorem, "not yet formalized" rather than "open". All applied; statements
  unchanged; re-audited and re-run through Comparator (`comparator-precheck.log`).
- **First lemmas toward Bohr–Landau, kernel-checked** (`zeta23-tree/Zeta23/BL/`): the Dirichlet-
  polynomial mean value ∫₀ᵀ|Σ_{n≤N} aₙ n^{−it}|² ≤ T Σ|aₙ|² + Σ_{m≠n} |aₘ||aₙ|·2/|log(n/m)| in two
  forms (`DPMV.dirichlet_mean_value`, `DPMV2.dirichlet_mean_value`), and the Jensen-disc inequalities
  n(r)·log(R/r) ≤ circleAverage(log‖f‖) − log‖f(c)‖ (`sum_divisor_mul_log_le`) and
  circleAverage(log‖f‖) ≤ ½·log circleAverage(‖f‖²) (`AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq`).
  Standard axioms only; included in the 124-theorem Comparator pre-check (`comparator-precheck-124.log`).
- **The plan** (`plan/BOHR_LANDAU_PLAN.md`, with the three scoping reports in `plan/SCOPE_REPORTS_2026-11-03.md`):
  route B (Jensen on discs centred 2+it, averaged in t; no Littlewood lemma needed) with the tree's
  approximate formula `Zeta0EqZeta` and its naive error bound reaches the uniform mean square for
  σ ≥ σ₁ > 2/3 and hence `RightHalfBound` for δ > 1/6, i.e. **zeros with Re ρ > 2/3 are O(T)**;
  the full Bohr–Landau (every δ > 0) needs the sharper approximation (first-derivative test or an
  Euler–Maclaurin tail), estimated at 500+ further lines. A second workflow is executing the plan's
  DAG; its results will be filed as `plan/BOHR_LANDAU_PARTIAL.md` when it returns.
- **Add-on for the cold run.** `math/qrh-zeta23-addon-v2/` packages the layer (124 theorems) for the
  qrh account: `scripts/z23_density.sh`, `_status.sh`, `_report.sh`, label `zeta23-density`, on top of
  the zeta23-main PASS tree; dry run on the author's account in progress (first attempt failed only
  because that scratch workspace had no NanoDa; guard added).

## Addendum, same day (night): the cold receipts and Bohr–Landau for δ > 1/6

- **Cold run of add-on v2 on the qrh account: MNF_DENSITY=ACCEPTED** (label `zeta23-density`,
  2026-11-03 21:05:57Z–21:13:50Z, 7 min, 124 theorems, 66 definitions compared by body, Lean kernel
  and NanoDa, systemd user unit with AF_UNIX denied). Receipt bundle:
  `math/qrh-zeta23-density-receipt.tar.gz`, sha256
  `975b21780c2c84ee84334d8115177a8858f87297731ccd108a4424782a5419fc`, extracted in `receipt-v2/`
  (report, audit, facts: AF_UNIX denied, probes and job in the same boot, files unchanged after
  the run). `dryrun/` holds the author-account dry run of the same add-on.
- **Bohr–Landau for δ > 1/6 is kernel-checked** (`plan/BOHR_LANDAU_PARTIAL.md`; sources
  `zeta23-tree/Zeta23/BL/BohrLandauPartial.lean`, `zeta23-tree/MNF/RH/DensityPartial.lean`):
  `Zeta23.BL.bohrLandau_gt_sixth` — for every δ > 1/6 the nontrivial zeros with 0 < Im ρ ≤ T and
  |Re ρ − 1/2| ≥ δ, with multiplicity, number ≤ C_δ·T for T ≥ 2 — with the uniform mean square of ζ
  for Re s ≥ 2/3 (explicit constant). Rows 7 and 8 of the field table now read: PROVED for δ > 1/6
  (resp. σ ≥ 2/3), the sorries of `Zeta23/BohrLandau.lean` remaining for 0 < δ ≤ 1/6 (resp.
  1/2 < σ < 2/3). Consequences in MNF vocabulary: density one within δ of the line for every
  δ > 1/6 with no hypothesis (`reservoirDensity_gt_sixth`); a gap at any Δ > 1/6 gives density one
  on the line with no other hypothesis (`onLineDensityOne_of_gap_gt_sixth`). A second prose
  review (31 findings) was applied to both files.
- **Add-on v3** (`math/qrh-zeta23-addon-v3`, label `zeta23-density-v3`, 270 theorems, 76 definitions)
  packages v2's layer plus the two new files; dry run on the author's account ACCEPTED
  (`dryrun-v3/`); the cold qrh run is the next step.
- **Cold run of add-on v3 on the qrh account: MNF_DENSITY=ACCEPTED** (label `zeta23-density-v3`,
  2026-11-03 22:03:08Z–22:09:39Z, 270 theorems, 76 definitions compared by body, Lean kernel and
  NanoDa, same launcher). Receipt bundle `math/qrh-zeta23-density-v3-receipt.tar.gz`, sha256
  `0588555dccdcefcb08479e34050c64048ef152ac0ba9d7632be4b7da62c2aaf0`, extracted in `receipt-v3/`. This is the receipt that covers
  `Zeta23.BL.bohrLandau_gt_sixth`, `rightHalf_gt_sixth`, `M3.meanSquareUnif_explicit` and the
  MNF density corollaries, cold under the launcher.

## Addendum, same day (late night): Bohr–Landau closed

- **`MNF.RH.BohrLandau` is a theorem of the tree** (`Zeta23.BL.bohrLandau_full`, in
  `zeta23-tree/Zeta23/BL/BohrLandauClosure.lean`; see `plan/BOHR_LANDAU_CLOSURE.md`): the sharp
  approximate formula (Titchmarsh 4.11 with x = N ≥ t) was formalized from the smooth
  first-derivative test and the Fourier series of B₂, giving Hardy–Littlewood's mean square for
  every σ₁ > 1/2 and hence the zero count O(T) at every distance δ > 0 from the line. Field rows
  5, 7, 8 become PROVED; `OnLineDensityOne` now follows from a gap alone
  (`MNF.RH.onLineDensityOne_of_gap_only`). Comparator pre-check of the whole layer (334 theorems)
  accepted with both kernels (`comparator-precheck-v4.log`, `audit-v4.out`); add-on v4 packaged
  for the cold run.
- **Cold run of add-on v4 on the qrh account: MNF_DENSITY=ACCEPTED** (label `zeta23-density-v4`,
  2026-11-04 00:52:20Z–00:58:52Z, 334 theorems, 81 definitions compared by body, Lean kernel and
  NanoDa, same launcher). Receipt bundle `math/qrh-zeta23-density-v4-receipt.tar.gz`, sha256
  `0d1919e42cbe45408d719536fc3c45ecdaa106bb1c83470e12b063006372f56a`, extracted in `receipt-v4/`. This receipt covers
  `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau` and `MNF.RH.onLineDensityOne_of_gap_only`.
