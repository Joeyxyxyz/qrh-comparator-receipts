# Final re-check of Lean statements, theorem sentences and the two appendix tables

Reviewed file: `WORK/paper.md` as it stood after the review edits (670 lines, mtime 2026-11-10 18:27 local,
sha256 beginning `dd619198dfe1505f`). The check was made independently of the earlier reviewers:
`review/APPLIED.md` was opened only after the comparison below was finished, to see which passages
had been edited. Nothing outside `WORK/review/` was written; `paper.md` was not changed.

Abbreviations: `V6` = `REPO/sources/qrh-zeta23-addon-v6`, `M3` = `REPO/sources/qrh-mnf-addon-v3`,
`EX` = `WORK/extracted`, `R11` = `EX/qrh-zeta23-density-v6-receipt/density-v6`,
`R5` = `EX/qrh-mnf-v3-receipt/mnf-v3`.

## Result

- Fenced Lean statements: 17 blocks, 23 statements. All 23 are byte-identical to the source the
  paper names for them. No mismatch.
- Sentences that state a theorem: no sentence misstates a Lean theorem. Three minor imprecisions
  are listed under "Mismatches"; none changes a claim.
- Appendix A (11 rows) and Appendix B (30 rows): every cell agrees with the receipts, with
  `facts/runs.md`, with `CHECKSUMS.sha256` (hashes recomputed from the tarballs) and with the
  register. No mismatch.

## Mismatches (3, all minor)

### M1. Notation, line 62: what the leading `@` marks

Text: "a leading `@` appears where Lean prints a theorem that has implicit arguments."

Evidence. In `R11/audit.out` all 279 statements printed with `@` begin with an implicit or
instance binder, and none of the 255 printed without `@` does; but at least 23 of those 255 have
an implicit binder later in the statement, for example
`MNF.RH.onLineDensityOne_of_gap : MNF.RH.BohrLandau → ∀ {Δ : ℝ}, 0 < Δ → ...` and
`MNF.RH.pairSum_nonneg : ∀ (T : ℝ) {f : ℝ → ℝ → ℝ → ℝ}, ...`. The paper's own quotations from the
run 5 report are in signature form with an implicit binder and no `@`
(`MNF.RH.spectralGapHyp_iff_zeroFree_strip {Δ : ℝ} : ...`, line 174;
`MNF.RH.on_line_density_one_of_gap ... {Δ : ℝ} ...`, line 198). So the rule as written is
contradicted by statements printed in the paper.

Corrected text: "In them `↑` is a coercion (from natural to real numbers, or from real to complex
numbers). The statements quoted from the report of run 5 are in signature form, with named
binders; in those quoted from the run 11 bundle a leading `@` appears where the first argument of
the theorem is implicit."

### M2. Step 6 of *Architecture of the formal proof*, line 319: the choice of σ₁ for every δ > 0

Text: "Hence $N(\tfrac12+\delta,T)=O(T)$ for every $\delta>\sigma_1-1/2$, and
$\sigma_1=1/2+\delta/2$ gives the right-half bound for every $\delta>0$ (`Zeta23.BL.rightHalf_all`)."

Evidence. `V6/Zeta23/BL/BohrLandauClosure.lean`, proof of `rightHalf_all` (lines 1212 to 1219):
the case `1/2 ≤ δ` is closed by `NRight_eq_zero_of_half_le` (the count is 0), and only for
`0 < δ < 1/2` is `rightHalf_of_meanSquareUnif` applied with `σ₁ := 1/2 + δ/2`; its docstring says
"For `δ ≥ 1/2` the count is `0` ...; for `0 < δ < 1/2` apply J8 ... with `σ₁ := 1/2 + δ/2 ∈ (1/2, 3/4)`".
`rightHalf_of_meanSquareUnif` needs `σ₁ < 1`, so the choice `σ₁ = 1/2 + δ/2` is not available for
`δ ≥ 1`. The statement of the theorem (`∀ δ, 0 < δ → ∃ C, ∀ T, 2 ≤ T → NRight δ T ≤ C * T`) is
quoted correctly; only the description of the proof is loose.

Corrected text: "Hence $N(\tfrac12+\delta,T)=O(T)$ for every $\delta>\sigma_1-1/2$. For
$0<\delta<1/2$ the choice $\sigma_1=1/2+\delta/2$ applies, and for $\delta\ge1/2$ the count is zero,
which gives the right-half bound for every $\delta>0$ (`Zeta23.BL.rightHalf_all`)."

### M3. Appendix B, header (line 556): gloss of the tag [RESTATEMENT | zeta23]

Text: "[RESTATEMENT \| zeta23], a theorem of zeta23 under the library's names".

Evidence. The gloss fits the row `MNF.RH.twoThirdsSimpleOnLine`. It does not fit the two rows of
run 7 that carry the same tag. `MNF.RH.ncountSuperlinear` is `Zeta23.ncountSuperlinear`, and
`MNF.RH.offLine_le_one_third` is `Zeta23.offLine_le_one_third` (`V6/MNF/RH/Density.lean`, lines
180 and 188 to 190); those two are proved in `V6/Zeta23/Superlinear.lean` and `V6/Zeta23/OffLine.lean`,
files of this layer that `NOTICE` lists as "supplied by Joey Messina on 2026-11-03", from
zeta23's `riemannVonMangoldt_zeta` and `thmB₀_mult_cumulative`. They are short consequences of
theorems of zeta23, not theorems of zeta23 under other names. The body of the paper says this
correctly ("It is derived from the main term of ...", "The step from Theorem B is bookkeeping",
lines 265 and 271), and the two "Reading" cells are correct; only the gloss in the header is too
narrow. The register's own wording for the first is "delegated to zeta23's Riemann–von Mangoldt
formula" (`DEPOSIT_MAP.md`, section 10).

Corrected text: "[RESTATEMENT \| zeta23], a theorem of zeta23 under the library's names, or (the
two rows of run 7) a short consequence of one, derived in the supporting files
`Zeta23/Superlinear.lean` and `Zeta23/OffLine.lean` of this layer".

## 1. Fenced Lean statements

Method: `fs_tools/blocks.py` (in the session scratchpad) splits every block tagged `lean` into its
statements and looks for each as a whole-line, byte-exact substring of the receipts and sources.

| Paper line | Statement | Source the paper names | Found byte-identical in |
|---|---|---|---|
| 149 | `theorem riemannZeta_ne_zero_of_seven_eighths_lt_re ... := by sorry` | run 1 challenge file | `EX/qrh-receipt/receipt/RECEIPT.md` lines 22 to 24 (inside `namespace OAI`) |
| 173 | `MNF.RH.spectralGapHyp_iff_zeroFree_strip` | report of run 5 | `R5/MNF_LIBRARY.md` lines 71 to 72; `R5/audit.out` |
| 182 | `MNF.RH.riemannHypothesis_iff_gap_half` | report of run 5 | `R5/MNF_LIBRARY.md` lines 37 to 38 |
| 189 | `MNF.RH.riemannHypothesis_iff_gap_three_eighths` | report of run 5 | `R5/MNF_LIBRARY.md` line 78 |
| 197 | `MNF.RH.on_line_density_one_of_gap` | report of run 5 | `R5/MNF_LIBRARY.md` lines 152 to 153 |
| 233 | `sturm_liouville_simple_eigenvalues` | report of run 5 | `R5/MNF_LIBRARY.md` line 130 |
| 255 | `def ReservoirDensityOne`, `def OnLineDensityOne` | `MNF/RH/Density.lean`, docstrings omitted | `V6/MNF/RH/Density.lean` lines 207 to 208 and 211 to 212 |
| 267 | `MNF.RH.offLine_le_one_third` | run 11 bundle | `R11/MNF_DENSITY.md` line 27; `R11/audit.out` line 557 |
| 277 | `def BohrLandau` | `MNF/RH/GapDensity.lean` | `V6/MNF/RH/GapDensity.lean` line 73 (same text in `M3`, line 71) |
| 283 | `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau` | reports of runs 9 to 11 | the three reports (run 11: line 429) and `R11/audit.out` line 1691 |
| 311 | `@BLClosure.meanSquareUnif_all` | `audit.out` of run 11 | `R11/audit.out` lines 1683 to 1685 |
| 327 | `Zeta23.BL.bohrLandau_gt_sixth` | run 11 bundle | `R11/MNF_DENSITY.md` line 387; `R11/audit.out` line 1372 |
| 335 | `MNF.RH.reservoirDensityOne_unconditional` | run 11 bundle | `R11/MNF_DENSITY.md` line 431 |
| 335 | `@MNF.RH.onLineDensityOne_of_gap_only` | `audit.out` of run 11 | `R11/audit.out` line 1696 |
| 352 | `@Zeta23.Density.density_single_window` | `audit.out` of run 11 | `R11/audit.out` lines 2436 to 2441 |
| 384 | `MNF.RH.reservoirMass_eq_integral`, `reservoirMass_le_rpow`, `meanDisplacement_tendsto_zero` | run 11 bundle | `R11/MNF_DENSITY.md` lines 456, 487, 490 to 491 |
| 417 | `MNF.RH.noDegenerate_iff`, `spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`, `spectralGapHyp_iff_bandCoincidentMass` | run 11 bundle | `R11/MNF_DENSITY.md` lines 538 to 539, 542 to 543, 547 to 548 |
| 430 | `@MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo` | `audit.out` of run 11 | `R11/audit.out` line 2477 |

Each printed statement was also read against the declaration in the Lean source. Points that the
print leaves ambiguous were settled from the source: the exponents in `reservoirMass_le_rpow`,
`reservoirMass_le_Ncount_mul` and `bohrLandau_explicit` are real (`(Real.log T) ^ ((3:ℝ)/5)`,
`^ (-(2:ℝ)/5)`, `δ ^ (-(5/2 : ℝ))`, `V6/MNF/RH/ReservoirMass.lean` lines 1042, 1119, 468), as the
paper says ("a real power").

## 2. Sentences that state a theorem

Every backticked Lean name in the paper (127 name-like tokens) occurs in the sources or receipts,
except `riemannZeta_real_neg`, which the paper attributes to an external repository and which is
outside this check. The sentences below were compared with the declaration and with Lean's print.

Introduction, Notation and *The first six runs and the MNF.RH library*

- `SpectralGapHyp Δ := SpectralGapProperty ShiftedZeroSpectrum Δ`, `SpectralGapProperty S Δ := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ`, `ShiftedZeroSpectrum := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}`, `nullify Δ x := if Δ ≤ |x| then x else 0`, `gap_iff_nullify_id` (`M3/MNF/RH/Gap.lean`, `Hypotheses.lean`, `Core.lean`): as described.
- Notation table: `Ncount`, `N0` (with multiplicity), `NOffLine` (`ρ.re ≠ 1/2`), `NOff` (`δ ≤ |ρ.re - 1/2|`), `NRight` (`δ ≤ ρ.re - 1/2`; the same body in `MNF.RH` and in `Zeta23.BL`), `reservoirMass`, `offDiagonalCoincidentMass`: as described (`V6/MNF/RH/Counting.lean`, `GapDensity.lean`, `Density.lean`, `ReservoirMass.lean` line 675, `Cube.lean`, `V6/Zeta23/BohrLandau.lean`). `Ncount_eq_N0_add_NOffLine` is in the claim set of run 11.
- Run 2: 17 statements, eleven about ζ and six about Dirichlet L-functions, all of the form `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * Ncount ... ≤ ...`; the constants `2/3`, `5/6`, `2 - 1/cMT`, `3/2 - cMT⁻¹/2`; the decimals 0.67250 and 0.83625 only in docstrings (`EX/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`).
- `spectralGapHyp_three_eighths_iff` (β ∈ {1/2, 1/8, 7/8}), `gap_of_rh`, `shifted_bounded` (|x| < 1/2), `shifted_bounded_three_eighths` (|x| ≤ 3/8), `order_one_iff_deriv`, `zeta_order_reflect`, `deriv_reflect`, `rh_of_symmetric_operator`, `rh_of_realization`, `multiplicityDictionary_iff`, `allZerosSimple_of_speiser_and_double_zero_hyp`, `SpeiserTheorem`, `BohrLandau`, `NcountSuperlinear`: as described. The sentence that the argument "does not show that G(3/8) fails to imply RH" agrees with Lean: `gap_below_bound_insufficient` is a statement about abstract sets.
- Counts: run 4 added three theorems (`spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of`, `spectralGapHyp_three_eighths_iff`; absent from the run 3 axiom table, present in run 4's). Run 5: 36 (Core 14, Gap 12, Hypotheses 10) + 8 (Unconditional, the only file with `import OAI...`) + 13 + 4 + 14 + 8 + 4 = 87. Run 6: 36 + 13 + 13 = 62, of the 13 in `Zeta23Restated.lean` eleven restate and two rewrite. `MNF.RH.Counter` is a `def` of the mirrors and occurs in no audited statement.
- Sturm–Liouville: 581 lines, four definitions, four claimed theorems; `IsConfiningPotential` is continuity plus `Tendsto V (cocompact ℝ) atTop`; `IsSimpleEigenvalue` is proportionality of any two `L²` eigenfunctions.

*The density layer*

- `Ncount_eq_near_add_off`, `N0_le_NNear`, `NNear_eq_N0_of_gap`, `ncountSuperlinear`, `offLine_le_one_third`: as described; all in the claim set.
- `Zeta23.BL.bohrLandau` rests on the two `sorry` lemmas `meanSquare_strip` and `rightHalfBound_of_meanSquare` and is in no claim set (0 of the 534 audit reports; every report of every run lists only the three axioms).
- Steps 1 to 5 and 7: `zeta_eq_euler_maclaurin`, `tail_by_parts` (with `P = (B2per - 1/6)/2`, `P_intCast`), `B2per_fourier`, `P_fourier`, `first_derivative_test_amp_smooth'` (bound `4 * G a / lam`), `tail_mode_bound'` (`t ≤ π x`, bound `8/(π ν) * x^(-σ-2)`), `tail_sharp`, `zeta_approx_sharp` (`σ₀ ≤ σ ≤ 2`, `0 ≤ t ≤ N`, `1 ≤ N`, `s ≠ 1`), `M1.dirichlet_meanSquare_le` (constant 26, weight `n + 1`), `meanSquareUnif_all`, `MNF.RH.NOff_eq_right_add_left`, `NLeft_eq_NRight`, `bohrLandau_of_right` (constant `2 * C`): as described. Step 6: `Rout σ₁ = 2 - σ₁`, `Lz = (1/2) log(1 + ‖ζ‖²)`, `geom_facts`, `count_le_integral` (`4 ≤ T`, window `3..T+3`, `log 3`), `rightHalf_of_meanSquareUnif`: as described, except for M2.
- The intermediate result: `norm_R_le` gives `(σ + t) * N^(-σ₁) / σ₁`; `M3.meanSquareUnif_explicit` has `2/3 ≤ σ₁ < 1` and uses `N = ⌊T^(3/2)⌋₊ + 1`; the quotation "a limitation of this route, not a theorem about ζ" is in `V6/MNF/RH/DensityPartial.lean` (lines 44 to 45, across a line break).
- 139 and 64 theorems in `BohrLandauPartial.lean` and `BohrLandauClosure.lean`: counted, and all of them are in the claim set of run 11.

*A zero-density estimate, the displacement bound and the pair measure*

- Zero-density sketch: `fz_sub_one_eq`, `neg_log_norm_fz_two_le` (`4 ≤ X`, bound `π²/(3X)`), `S_mul_Mx_eq`, `cm_eq_of_le`, `abs_cm_le`, `sum_dX_sq_le`, `norm_add_sq_le_eta`, `integral_Leps_segment_le_of_meanSquare`, and the parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`, `ε² = 1/X`, `θ = (2σ₁-1)/(2σ₁)` (`exponent_single`, `count_le_Egen`): as described. No theorem of the claim set bounds `NOff` by a power below 1, as the paper says.
- Displacement: `bohrLandau_explicit` (`∃ A B, 0 ≤ A ∧ 0 ≤ B ∧ ...`, `0 < δ ≤ 1/2`, `2 ≤ T`), `MNF_Ncount_le_mul_log`, `MNF_mul_log_le_Ncount`, the split at `(log T)^(-2/5)`, the tail `(2/3) A₂ δ₀^(-3/2) + B₂/2`, `reservoirMass_le_Ncount_mul`, `signedReservoir_eq_zero`, `reservoirMass_le_half_Ncount`: as described.
- Pair measure: `pairSum`, `pairSum_const`, `pairSum_fst`, `pairSum_fst_indicator`, `pairSum_fst_abs`, `coincidentMass_eq`, `Ncount_le_diagonalMass`, `diagonalMass_le_sq_Ncount`, `offLine_sq_le_offDiagonalCoincidentMass`, `offDiagonalCoincidentMass_le`, `_le_two_thirds`, `_le_five_ninths`: as described. The counterexample gives 2+2+2+2+1+1 = 10 against 2·4 = 8, and the corrected bound gives 12.
- Equivalences: `Degenerate`, `OnLine`, `bandZeros` (the line included), `OrdinatesInjectiveOn`, `bandCoincidentMass`, `degenerate_of_not_onLine`, the three equivalences for every real `Δ`: as described. Their proofs reach `Zeta23.zetaZeroConfig.reflect_mem` through `is_nontrivial_zero_mirror` (`V6/MNF/RH/Cube.lean`, line 175), and the third uses `nontrivial_zero_im_ne_zero`, so the tag [PROVED | this tree] and its justification in the header of Appendix B are right.
- Real zeros: `zeta_em_remainder_norm_le` (`≤ 1/2/σ`), `Zeta0EqZeta` at `N = 1` (`Cube.lean`, line 452), `nontrivial_zero_im_ne_zero`: as described; the identity `1/2 + σ/(1-σ) = 1/(1-σ) - 1/2` holds.
- Counts in *Lessons learned* and *Errata*: 18 mirrors, 13 of them with claimed theorems; 27 theorems of `ReservoirMass.lean` and 2 of `Cube.lean` omitted (65 − 38, 56 − 54); 13 `aux_` lemmas in the mirror of `InjectionEjection.lean` and in no audit report; 255 statements without `@` and 279 with `@` among the 534 of run 11; `Zeta23.BL.CG`, `meanSquareB` and `A₀` are definitions of the mirror and occur in no audited statement.

## 3. Appendix A, row by row

Start, end and exit from `logs/<label>.start`, `.end`, `.exit` of each bundle (for runs 3 to 5 the
files are under `mnf*/logs/`); counts from the first lines of each report; hashes recomputed with
`sha256sum` from the tarballs in REPO and compared with `CHECKSUMS.sha256`.

| Run | Label | Thm / Def | Kernels | Start to end | Verdict | Add-on, receipt | Agrees |
|---|---|---|---|---|---|---|---|
| 1 | `qrh-main` | 1 / none listed | Lean | 2026-10-27T17:43:45Z to 19:38:23Z | PASS | `e0745073`, `d8670539` | yes |
| 2 | `zeta23-main` | 17 / no count, no holes | Lean, NanoDa | 2026-10-28T11:08:56Z to 11:29:58Z | PASS | `958abb9f`, `e0b9a4d9` | yes |
| 3 | `mnf-library` | 40 / 17 as holes | Lean | 2026-10-28T00:20:02Z to 00:32:46Z | ACCEPTED | `295ee9c6`, `f9180842` | yes |
| 4 | `mnf-library-v2` | 43 / 17 | Lean | 2026-10-28T03:25:44Z to 03:39:13Z | ACCEPTED | `933c5ba8`, `c6142a40` | yes |
| 5 | `mnf-library-v3` | 87 / 41 | Lean | 2026-10-29T05:56:47Z to 06:10:47Z | ACCEPTED | `3668e138`, `023d7ada` | yes |
| 6 | `zeta23-mnf` | 62 / 23 | Lean, NanoDa | 2026-10-29T02:06:38Z to 02:12:34Z | ACCEPTED | `958abb9f`, `1476f568` | yes |
| 7 | `zeta23-density` | 124 / 66 | Lean, NanoDa | 2026-11-03T21:05:57Z to 21:13:50Z | ACCEPTED | `5dc41dff`, `975b2178` | yes |
| 8 | `zeta23-density-v3` | 270 / 76 | Lean, NanoDa | 2026-11-03T22:03:08Z to 22:09:37Z | ACCEPTED | `c0958d53`, `0588555d` | yes |
| 9 | `zeta23-density-v4` | 334 / 81 | Lean, NanoDa | 2026-11-04T00:52:20Z to 00:58:43Z | ACCEPTED | `fb74e8a2`, `0d1919e4` | yes |
| 10 | `zeta23-density-v5` | 480 / 98 | Lean, NanoDa | 2026-11-04T14:38:23Z to 14:45:29Z | ACCEPTED | `2d2cf058`, `37a806b2` | yes |
| 11 | `zeta23-density-v6` | 534 / 110 | Lean, NanoDa | 2026-11-11T00:02:37Z to 00:17:52Z | ACCEPTED | `99575a1e`, `ca07a500` | yes |

The text under the table also agrees with the bundles: `.type` reads `cold` for runs 1 and 2,
`warm` for runs 6 to 11, and is absent for runs 3 to 5; the order by start time is 1, 3, 4, 2, 6, 5,
7 to 11; run 2's facts record the manifest hash `a20b1b1d...` while the deposited
`qrh-zeta23-addon/MANIFEST.sha256` hashes to `0c37cc13...`; the five Lean sources hashed in run 6's
`mnf_sha256.txt` are byte-identical to those under `REPO/sources/qrh-zeta23-addon/MNF/RH/`
(recomputed here). The table of runs 3 to 6 in the body (labels, counts, kernels, start times, wall
clocks 12:43.44, 13:28.87, 14:00.38, 5:55.36, result lines) agrees as well.

## 4. Appendix B, row by row

"First run" is the first run whose axiom table lists the name (checked in the reports of runs 3
to 11). "Module" was checked in the add-on of that run and in `M3` or `V6`. "Tag" was checked
against `DEPOSIT_MAP.md` (sections 1, 2, 3, 8 and 10) and, for the two Mathlib-only lemmas of
run 7, against `V6/README.md` (lines 23 to 24), as the header says.

| Lean name | Module | Reading against the Lean statement | Tag | First run |
|---|---|---|---|---|
| `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` | ok (receipt: module `OAI.NumberTheory.DirichletL.Nonvanishing`) | ok | ok | 1 |
| `two_thirds_simple_on_critical_line` | ok (receipt: module `Solution`) | ok | ok | 2 |
| `MNF.RH.riemannHypothesis_iff_gap_half` | ok | ok | ok | 3 |
| `MNF.RH.riemannHypothesis_iff_gap_three_eighths` | ok | ok | ok | 3 |
| `MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths` | ok | ok | ok | 3 |
| `MNF.RH.spectralGapHyp_iff_zeroFree_strip` | ok | ok | ok | 4 |
| `sturm_liouville_simple_eigenvalues` | ok | ok | ok | 5 |
| `MNF.RH.on_line_density_one_of_gap` | ok | ok | ok | 5 |
| `MNF.RH.twoThirdsSimpleOnLine` | ok | ok | ok | 6 |
| `MNF.RH.ncountSuperlinear` | ok | ok | ok (see M3 for the gloss) | 7 |
| `MNF.RH.offLine_le_one_third` | ok | ok | ok (see M3 for the gloss) | 7 |
| `DPMV.dirichlet_mean_value` | ok | ok (`0 < T`; off-diagonal term `‖a m‖ * ‖a n‖ * (2 / |log (n/m)|)`) | ok (README of v6) | 7 |
| `sum_divisor_mul_log_le` | ok | ok | ok (README of v6) | 7 |
| `Zeta23.BL.bohrLandau_gt_sixth` | ok | ok | ok | 8 |
| `BLClosure.zeta_approx_sharp` | ok | ok | ok | 9 |
| `BLClosure.meanSquareUnif_all` | ok | ok | ok | 9 |
| `Zeta23.BL.bohrLandau_full` | ok | ok | ok | 9 |
| `MNF.RH.reservoirDensityOne_unconditional` | ok (declared in `BohrLandauClosure.lean`) | ok | ok | 9 |
| `MNF.RH.onLineDensityOne_of_gap_only` | ok (declared in `BohrLandauClosure.lean`) | ok | ok | 9 |
| `Zeta23.BL.bohrLandau_explicit` | ok (declared in `MNF/RH/ReservoirMass.lean`, namespace `Zeta23.BL`) | ok | ok | 10 |
| `MNF.RH.reservoirMass_eq_integral` | ok | ok | ok | 10 |
| `MNF.RH.reservoirMass_le_rpow` | ok | ok | ok | 10 |
| `MNF.RH.meanDisplacement_tendsto_zero` | ok | ok | ok | 10 |
| `Zeta23.Density.density_single_window` | ok | ok | ok | 10 |
| `MNF.RH.noDegenerate_iff` | ok | ok | register [PROVED]; paper [PROVED \| this tree], disclosed in the header and supported by the source | 11 |
| `MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros` | ok | ok | as the previous row | 11 |
| `MNF.RH.spectralGapHyp_iff_bandCoincidentMass` | ok | ok | as the previous row | 11 |
| `MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo` | ok | ok | ok | 11 |
| `MNF.RH.offDiagonalCoincidentMass_le_five_ninths` | ok | ok | ok (register: "[PROVED \| this tree] for the eventual bound") | 11 |

All "Run" cells of the paper equal the first run found. The sentence of the header on the two
rows of run 3 that mention the gap hypothesis is right: two of the three rows of run 3 do, and the
17 definitions of run 3 were listed as holes.

## 5. Not checked here

- The zeta23 library itself is not in REPO; statements about what its lemmas say
  (`riemannVonMangoldt_zeta`, `Zeta0EqZeta`, `Zeta23.MV.mvDiag_thirteen`, `zeta_lower_bound_two`,
  `zetaZeroConfig.reflect_mem`, `mult_reflect`) were checked only through the way the layer's
  sources use and describe them.
- Bibliographic statements, the numerics, the protocol section and the pins table were outside
  this pass (the pins table was compared with `facts/runs.md` in passing and agrees).
