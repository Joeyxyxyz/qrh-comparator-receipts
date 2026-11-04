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

## Addendum, 2026-11-04 (morning): reservoir mass, a numeric look at the cascade, and the strip plan

- **Reservoir mass is bounded** (`reservoir/`; source `zeta23-tree/MNF/RH/ReservoirMass.lean`, 65
  declarations, standard axioms). With the reservoir mass of height T defined as
  `reservoirMass T := Σ_{ρ ∈ zerosIn 0 T} m(ρ)·|Re ρ − 1/2|` (every nontrivial zero with
  0 < Im ρ ≤ T, with multiplicity, weighted by its distance from the line), the tree now has:
  the layer-cake identity `reservoirMass T = ∫₀^{1/2} NOff δ 0 T dδ` (`reservoirMass_eq_integral`,
  an exact identity for every T); the trivial bound `reservoirMass T ≤ ½·N(0,T)`
  (`reservoirMass_le_half_Ncount`, since every nontrivial zero has |Re ρ − 1/2| < 1/2); an explicit
  Bohr–Landau constant, `NOff δ 0 T ≤ (A·δ^{−5/2} + B)·T` for 0 < δ ≤ 1/2 and T ≥ 2
  (`Zeta23.BL.bohrLandau_explicit`, with A, B built from the tree's explicit mean-square constant);
  and from the two together, splitting the layer cake at δ₀ ≍ (log T)^{−2/5},
  `reservoirMass T ≤ A·T·(log T)^{3/5}` for T ≥ T₀ (`reservoirMass_le_rpow`), i.e. with the
  Riemann–von Mangoldt lower bound N(0,T) ≥ c·T·log T the **mean displacement from the line per zero
  is ≤ A·(log T)^{−2/5} and tends to 0** (`reservoirMass_le_Ncount_mul`,
  `meanDisplacement_tendsto_zero`). By the reflection ρ ↦ 1 − ρ̄ the signed reservoir
  Σ m(ρ)·(Re ρ − 1/2) is exactly 0 and the mass is twice the right-half sum
  (`signedReservoir_eq_zero`, `reservoirMass_eq_two_right`). Honest framing: all of this is a
  consequence of Bohr–Landau (`bohrLandau_full`) and of the zero count; it is compatible with
  the existence of off-line zeros and says nothing about the gap hypothesis `SpectralGapHyp`.
  Comparator pre-check of the whole layer (372 claims, both kernels) accepted
  (`reservoir/comparator-precheck-v5.log`, 2026-11-04T04:40Z; axioms in `reservoir/audit-v5.out`;
  mirrors regenerated by `reservoir/gen_v5.py`, which also records the statements excluded from the
  challenge because they mention zeta23-internal names or a finiteness proof as a term). The six node
  reports of the workflow that produced the file are in `reservoir/RESERVOIR_WORKFLOW_NOTES.md`;
  `reservoir/ReservoirMass.merged.lean` is the merged file before installation. A prose review of
  the installed file (17 findings: unexplained vocabulary, an overclaim about which constants are
  explicit, plan-numbering residue, a misleading audit trailer) was applied; only comments changed,
  the code is byte-identical and the file recompiles; the reviewed file is
  `zeta23-tree/MNF/RH/ReservoirMass.lean`.
- **Numerics: the first 400 zeros read through the threshold cascade** (`numeric/RESULTS.md`,
  figure `numeric/cascade.svg`, data `numeric/zeros.tsv`, `spacings.tsv`, `paircorr.tsv`; pure
  Python, scripts included). Ordinates by Riemann–Siegel, re-located by Euler–Maclaurin and checked
  against the standard tables to 3·10⁻¹⁰. On the 399 normalised spacings the reservoir (hidden mass
  below a threshold Δ) is **empty up to Δ = 0.243**: no spacing below 0.2 (the exact GUE law expects
  3.4, Poisson 72), 4 below 0.3, 29 below 0.5 (GUE 45); the hidden-mass cascade rises like Δ^4.5
  (bootstrap 16–84 % band [4.1, 5.0]) against 3.6 for GUE and 1.7 for Poisson fitted on the same
  thresholds; the spacing distribution is 0.051 from the exact GUE law in Kolmogorov–Smirnov distance
  (p ≈ 0.25) and 0.33 from Poisson (p ≈ 3·10⁻³⁸); the trace δ* is the largest spacing, 2.20. The
  low zeros are slightly more rigid than the GUE limit (fewer small and fewer large spacings, each
  a ≈2σ effect), the known finite-height direction. **This is exploration, not a theorem**, and it
  concerns the spacing of the ordinates, not the real parts.
- **The strip plan** (`strip/STRIP_PLAN.md`; scoping reports in
  `strip/STRIP_SCOPE_REPORTS_2026-11-04.md`; the tree/Mathlib inventory in `strip/Inventory.*`).
  What is still open is the strip itself (`SpectralGapHyp Δ`, no zero with 1/2 < Re ρ < 1/2 + Δ),
  which no known method approaches. What is within reach of the receipted machinery is a
  **zero-density estimate with a power saving**: the milestone target is
  `Zeta23.Density.density_single_window` — for 1/2 < σ₁ and σ₁ − 1/2 < δ ≤ 1/2,
  `NRight δ T ≤ C·T^{1 − (2σ₁−1)²/(2σ₁)}·(1 + log T)³` for T ≥ 2 (σ₁ = 3/4 gives T^{5/6}), i.e.
  the zeros at distance ≥ δ from the line are not merely O(T) but O(T^{1−c(δ)}), a positive
  proportion fewer than Bohr–Landau. The route is Carlson's: the mollifier
  M_X(s) = Σ_{n≤X} μ(n) n^{−s}, the mean square of ζ·M_X on the window by the receipted approximate
  formula and the Montgomery–Vaughan inequality (`Zeta23.MV`), and the disc-average count of zeros
  already used for Bohr–Landau, with an ε-majorant ½·log(ε² + ‖f‖²) in place of ½·log(1 + ‖f‖²) so
  that the mollified function's small mean square is not lost. The plan is a DAG of 16 nodes in
  five stages (the one new piece of mathematics is the divisor-sum bound
  Σ_{m≤Y} d_X(m)² ≤ Y·(1 + log X)³); the stretch target is Carlson's exponent 4σ₁(1 − σ₁) by a
  dyadic re-parametrisation. The execution workflow is running; its result will be filed under
  `strip/` when it returns. As the plan says in its own words: no step of it proves, or claims to
  approach, the strip; it excludes no zero.

## Addendum, 2026-11-04 (06:30Z): the zero-density estimate is proved; add-on v5

- **`Zeta23.Density.density_single_window` is a theorem of the tree** (`strip/exec/`; source
  `zeta23-tree/Zeta23/Density/StripDensity.lean`, 108 declarations, standard axioms): for every
  1/2 < σ₁ and σ₁ − 1/2 < δ ≤ 1/2 there is C with `NRight δ T ≤ C·T^{1 − (2σ₁−1)²/(2σ₁)}·(1 + log T)³`
  for all T ≥ 2 — the zeros at distance ≥ δ to the right of the line (with multiplicity; by
  reflection the same holds on the left) are O(T^{1−c}) with c = (2σ₁−1)²/(2σ₁) > 0, a power
  saving over Bohr–Landau's O(T); at σ₁ = 3/4 the count is O(T^{5/6}(log T)³), and taking σ₁ just
  below 1/2 + δ the saving approaches 4δ²/(1+2δ). The execution workflow proved all 16 nodes of
  `strip/STRIP_PLAN.md` (centre bound and the Möbius identity ζ·M_X − 1 = −ζ·Σ_{n>X} μ(n)n^{−s}
  through Mathlib's `LSeries_zeta_mul_Lseries_moebius`; the product polynomial S_N·M_X; the divisor
  bound Σ_{m≤Y} d_X(m)² ≤ Y(1 + log X)³; partial summation; the window mean squares; the zero
  order of ζ·M_X; Jensen discs with the majorant ½ log(ε² + ‖f‖²) and its Fubini swap; the
  count-to-integral and count-to-mean-square bridges; the exponent arithmetic; the assembly), the
  merge produced one module (`strip/exec/StripDensity.merged.lean`, node reports in
  `strip/exec/NODE_REPORTS.txt`, node files under `strip/exec/nodes/`), which was recompiled
  independently (`strip/exec/compile.merged-independent.log`: 108 `#print axioms` lines, all
  `[propext, Classical.choice, Quot.sound]`) and prose-reviewed (14 findings — an overclaim about
  the saving 4δ²/(1+2δ) being attained, "receipted" and plan-label residue, the wrong lemma named
  for the O(T) bound, a docstring on an `example`; `strip/exec/StripDensity.review.diff`); only
  comments changed. What it is not, in the file's own words: a count, not a zero-free region; it
  excludes no single zero, leaves `SpectralGapHyp` untouched, is not evidence for RH, and is
  weaker than Carlson's 4σ₁(1 − σ₁) (which needs the dyadic windows of Stage 5, not done).
- **Comparator pre-check of the whole layer, 480 theorems and 98 definitions, accepted with both
  kernels** (`strip/comparator-precheck-v6.log`, 2026-11-04T06:25:56Z–06:31:27Z; axioms of all
  480 claims in `strip/audit-v6.out`; mirrors regenerated by `strip/gen_v6.py`; tree copies under
  `zeta23-tree/`). The claim set is v4's 334 + 38 (`ReservoirMass`) + 108 (`StripDensity`).
- **Add-on v5** (`math/qrh-zeta23-addon-v5/`, tarball `math/qrh-zeta23-addon-v5.tar.gz`, sha256
  `2d2cf0589c409ba72363657fbe6d7039b277bb2ec6c171f42a906033d50eb453`, copy in `~/Downloads`; label
  `zeta23-density-v5`, work dir `density-v5`, bundle `qrh-zeta23-density-v5-receipt.tar.gz`)
  packages the layer with the two new files; `z23_density.sh` checks that `ReservoirMass`,
  `StripDensity` and their mirrors are cold in the tree. Dry run on the author's account
  (`dryrun-v5/`): MNF_DENSITY=ACCEPTED, 2026-11-04T06:33:50Z–06:40:37Z, 480 theorems, 98
  definitions, both kernels, no problems; the cold qrh run needs Joey at the keyboard.
- **Erratum on the v4 receipt's report text.** The `## How to read this` block of
  `receipt-v4/density-v4/MNF_DENSITY.md` (and so of the bundle `qrh-zeta23-density-v4-receipt.tar.gz`)
  carries the sentence "Bohr–Landau itself is NOT proved: `Zeta23/BohrLandau.lean` names its two
  analytic inputs as `sorry` lemmas …", inherited from the v2/v3 report generator, where it was
  true. For v4 it is false: the same report's statement block and axiom table show
  `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau` with standard axioms. The Lean facts of the
  receipt are unaffected (Comparator's verdict, the audit, the hashes); the prose of the
  generator is corrected in add-on v5 (`scripts/z23_density_check.py`), and the receipts
  repository's README should carry this erratum. The bundle itself is not altered.

## Addendum, 2026-11-04 (14:46Z): the cold receipt for v5

- **Cold run of add-on v5 on the qrh account: MNF_DENSITY=ACCEPTED** (label `zeta23-density-v5`,
  2026-11-04T14:38:23Z–14:45:29Z, 7 min, exit 0, 480 theorems, 98 definitions compared by body,
  Lean kernel and NanoDa, systemd user unit with AF_UNIX denied, probes and job in the same boot,
  layer files unchanged after the run, no Problems). Receipt bundle
  `math/qrh-zeta23-density-v5-receipt.tar.gz`, sha256
  `37a806b20c4ef5abf9bed06f127746e46d2184b928a75a0efcaa06de1a5ef863` (copy in `~/`), extracted in
  `receipt-v5/`. The layer's Lean files and the challenge are byte-identical to the dry run's
  (`density_sha256.txt` listings differ only in the two trees' `lakefile.toml`). This is the
  receipt that covers `MNF.RH.reservoirMass_le_rpow`, `MNF.RH.meanDisplacement_tendsto_zero`
  and `Zeta23.Density.density_single_window`, cold under the launcher, on top of everything v4
  covered. Its `## How to read this` block carries the corrected prose (Bohr–Landau PROVED;
  the zero-density estimate described as a count, not a zero-free region).
