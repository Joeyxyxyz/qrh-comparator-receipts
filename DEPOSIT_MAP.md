# MNF × Riemann zeta — deposit map

What in the Lean corpus is proved, what is conditional (and on what), what is open, and what
is withdrawn. Written 2026-10-27 against the consolidated library `MNF/RH/*.lean` in this
add-on, which replaces the RH files of the corpus (output28–86) for deposit purposes; revised
2026-10-28 for add-on v2 (three theorems added, §1–§2; §8 added), and 2026-10-29 for add-on v3
(the frontier package: §1 Counting and Reduction rows, §3 Schrodinger and GapDensity rows, §9).
Receipts behind this map, all from the kit's launcher on Joey's laptop: v1 `qrh-mnf-receipt.tar.gz`
(ACCEPTED, 40 theorems, sha256 `f9180842…`); v2 `qrh-mnf-v2-receipt.tar.gz` (ACCEPTED, 43, definition
bodies compared, `c6142a40…`); v3 `qrh-mnf-v3-receipt.tar.gz` (ACCEPTED 2026-10-29 05:56–06:10 UTC, 87
theorems, 41 definitions, `023d7ada93e313296e7e9d88c82569fa65c704a2624149a67e5e74c762c8159a`); zeta23
`qrh-zeta23-receipt.tar.gz` (PASS, `e0b9a4d9…`) and the MNF layer on it `qrh-zeta23-mnf-receipt.tar.gz`
(ACCEPTED, 62, `1476f568…`). Revised again 2026-11-04 and 2026-11-11 for the density field (§10): five more
receipts on the zeta23 tree, add-on v2 `qrh-zeta23-density-receipt.tar.gz` (ACCEPTED 2026-11-03,
124 theorems, `975b2178…`), v3 `qrh-zeta23-density-v3-receipt.tar.gz` (ACCEPTED, 270, `0588555d…`),
v4 `qrh-zeta23-density-v4-receipt.tar.gz` (ACCEPTED 2026-11-04 00:52–00:58 UTC, 334 theorems, 81
definitions, `0d1919e42cbe45408d719536fc3c45ecdaa106bb1c83470e12b063006372f56a`), v5
`qrh-zeta23-density-v5-receipt.tar.gz` (ACCEPTED 2026-11-04 14:38–14:45 UTC, 480 theorems, 98
definitions, `37a806b20c4ef5abf9bed06f127746e46d2184b928a75a0efcaa06de1a5ef863`: the reservoir mass and
a zero-density estimate with a power saving), v6
`qrh-zeta23-density-v6-receipt.tar.gz` (ACCEPTED 2026-11-11 00:02–00:17 UTC, 534 theorems, 110
definitions, `ca07a500aa8384b96b03f3480053cd48271bb157a04155de42342ca21254a90c`: the strip cube and the
absence of real zeros of ζ in (0, 1)). This root copy is the current deposit map;
the copies inside the add-on folders and inside the Zenodo record of 2026-10-29 are frozen with
the add-on or record they belong to.

Register tags: **[PROVED]** kernel-checked from Mathlib alone; **[PROVED | 7/8]** kernel-checked
from Mathlib plus OpenAI's 7/8 theorem (exactly as reliable as the Comparator PASS in
RECEIPT.md); **[CONDITIONAL]** proved from explicit named hypotheses; **[LITERATURE]** a
published theorem stated as a hypothesis, not formalized; **[OPEN]** conjecture;
**[WITHDRAWN]** a corpus claim that does not survive.

## 1. Unconditional — [PROVED] (MNF/RH/Core.lean, Gap.lean)

| theorem | says | corpus origin |
|---|---|---|
| `zeta_order_ge_one` | every nontrivial zero has multiplicity ≥ 1 | output28/71 (re-proved; the old proof used `riemannZeta_two`, which is not in Mathlib) |
| `order_one_iff_deriv`, `deriv_zero_of_high_order`, `allZerosSimple_iff_derivativeNonvanishing` | simple ⟺ ζ'(ρ) ≠ 0 | output35/71/84 |
| `nontrivial_zero_reflect`, `shifted_symmetric` | ρ zero ⟹ 1−ρ zero; the shifted spectrum is symmetric | new (hackathon scan item 4) |
| `deriv_reflect` | ζ'(1−ρ) = −F(ρ)·ζ'(ρ) at zeros, F ≠ 0 | replaces output86's **axiom** `func_eq_deriv` (false for general s; true at zeros) |
| `analyticOrderAt_reflect`, `zeta_order_reflect` | multiplicities are symmetric under ρ ↦ 1−ρ | new (scan item 7) |
| `in_strip_of_zero`, `riemannHypothesis_iff_strip`, `riemannHypothesis_iff_shifted_subset_zero` | Mathlib's `RiemannHypothesis` ⟺ every nontrivial zero has Re = 1/2 ⟺ S ⊆ {0} | replaces the **Bridge hypothesis** of output71/72 and the local `def RiemannHypothesis` of output40/83 |
| `shifted_bounded` | \|x\| < 1/2 on S | output0–23 |
| `tau_threshold` | gap at Δ + bound \|x\| < Δ ⟹ S ⊆ {0} | tau_half_real |
| `riemannHypothesis_iff_gap_half` | **RH ⟺ SpectralGap(S, Δ) for every Δ ≥ 1/2**, no hypothesis | the corpus "master theorem" (output72), now unconditional |
| `riemannHypothesis_iff_gap_of_zeroFree`, `riemannHypothesis_iff_remaining_strip` | with a zero-free region Re > θ: RH ⟺ gap at any Δ > θ−1/2 ⟺ no zeros in 1/2 < Re ≤ θ | bridge §7 |
| `gap_below_bound_insufficient`, `delta_from_ratio_38_insufficient` | a gap at Δ below the bound cannot give S ⊆ {0}; the Δ/scale = ½ rule gives Δ = 3/16, which is below it | scan items 3, 6 |
| `symmetric_bounded_not_on_line` | symmetry + Re ≤ 7/8 do not force the line (four-point witness) | bridge §8 |
| `sign_gate_trivial`, `sign_gate_shifted` | the hackathon sign gate returns {0} on any symmetric set: applied to S it assumes RH | scan item 5 |
| `nullify_dilation`, `gap_iff_nullify_id` | nullify is dilation-covariant; the gap property is "nullify is the identity on S" | Python-verified in the corpus, now kernel-checked |
| `spectralGapHyp_iff_zeroFree_strip` (v2) | **the gap hypothesis at Δ is exactly a zero-free strip 1/2 < Re s < 1/2 + Δ** (no hypothesis, any Δ) | new; makes the §4 remark on Δ ≤ 3/8 a theorem |
| `spectralGapHyp_three_eighths_iff_of` (v2) | given `ZeroFreeRightOf (7/8)`: gap at exactly 3/8 ⟺ every nontrivial zero has Re ∈ {1/2, 1/8, 7/8} | new; shows where the squeeze from the bound \|Re ρ − 1/2\| ≤ 3/8 stops: at Δ = 3/8 it leaves the line Re s = 7/8 open |
| `zerosIn_finite`, `Ndist_le_Ncount`, `N0star_le_Ndist`, `N0simple_le_N0star` (v3, Counting) | the zeros in a window (T₁,T₂] are finitely many; distinct ≤ with multiplicity; on-line ≤ distinct; simple on-line ≤ on-line | [BOOKKEEPING]; zeta23's vocabulary over MNF's names |
| `riemannHypothesis_iff_window_counts`, `allZerosSimple_iff_window_counts` (v3, Counting) | RH ⟺ ∀ T₁ T₂, N0star = Ndist; AllZerosSimple ⟺ ∀ T₁ T₂, Ncount = Ndist | [BOOKKEEPING] restatements, not density results |
| `gap_iff_zeroFreeBand`, `gap_of_right_side`, `rh_of_band_of_zeroFree` (v3, Reduction) | the gap at Δ IS the zero-free band 1/2 < Re ρ < 1/2 + Δ; one side suffices; with a region Re > θ, RH ⟺ no zero with 1/2 < Re ρ ≤ θ | frontier package; `rh_of_band_seven_eighths` is the θ = 7/8 instance (§2) |
| `multipleZeroKillsGap_iff`, `fischerForward_iff` (v3, Reduction) | the corpus hypotheses `MultipleZeroKillsGap` and `FischerForward` are each ⟺ (RH → AllZerosSimple) | so neither is a route to RH and no experiment bears on them (notes/FischerForward_The_Math.md) |
| `rh_of_realSpectrumRealization`, `allZerosSimple_of_multiplicity_dictionary` (v3, Reduction) | a set of reals containing (ρ − 1/2)/i for every zero is RH; a multiplicity dictionary with all multiplicities 1 is simplicity | Hilbert–Pólya without an operator |
| `gap_of_mechanism`, `mechanism_of_gap`, `gapMechanism_iff`, `probes_zero_iff` (v3, Reduction) | a gap mechanism (a predicate every band zero has and nothing has) is the same as the band; both τ-probes read 0 ⟺ Re ρ = 1/2 | the precise form of "the gap route is RH restated" |
| `sturm_liouville_simple_eigenvalues` (v3, SturmLiouville) | for a continuous confining `V`, any two `L²` eigenfunctions of −u'' + V u = λu are proportional | Joey's consolidated corpus file (Aristotle), ported to this pin; a statement about 1-D Schrödinger operators, not about ζ. Classical (the limit-point case of Weyl's theory: Coddington–Levinson ch. 9, Teschl *Mathematical Methods in Quantum Mechanics* ch. 9, Berezin–Shubin); as a formalization, no completed Lean proof of this result is known to the depositor as of 2026-11-03, after searching Mathlib master (no Sturm–Liouville, Schrödinger or function-Wronskian material), the Palomar registry, and GitHub (atlas-lean has a Dirichlet existence theorem on [0,1]; math-physics-lab states simplicity on a compact interval with the proof left `sorry`) |
| `N0_le_Ncount`, `NOff_le_Ncount`, `gap_forces_NOff_eq` (v3, GapDensity) | on-line and off-line counts bound the total; under a gap at Δ > 0 every window splits exactly as N = N₀ + N_off(Δ) | [BOOKKEEPING] |

## 2. Unconditional given OpenAI's theorem — [PROVED | 7/8] (MNF/RH/Unconditional.lean)

`zeroFree_seven_eighths`, `nontrivial_zero_re_le_seven_eighths`, `shifted_bounded_three_eighths`,
`riemannHypothesis_iff_gap_three_eighths` (RH ⟺ gap at any Δ > 3/8),
`riemannHypothesis_iff_remaining_strip_seven_eighths` (RH ⟺ no zeros in 1/2 < Re s ≤ 7/8),
`rh_of_gap_three_eighths`. Same content as the kit's `MNF_Bridge78_Unconditional.lean`,
restated over the consolidated definitions. v2 adds `spectralGapHyp_three_eighths_iff` (the
boundary case: a gap at exactly 3/8 ⟺ every nontrivial zero has Re ∈ {1/2, 1/8, 7/8}); it is
not RH, because the 7/8 theorem leaves the line Re s = 7/8 itself open, and nobody conjectures
zeros there.

## 3. Conditional — [CONDITIONAL] (MNF/RH/Hypotheses.lean)

| theorem | hypotheses | note |
|---|---|---|
| `rh_of_gap` | `SpectralGapHyp Δ`, Δ ≥ 1/2 | the hypothesis is RH itself (§1) |
| `rh_of_gap_three_eighths` | `SpectralGapHyp Δ`, Δ > 3/8 | likewise, given 7/8 |
| `multiplicityBoundOne_iff_allZerosSimple` | — | output40's "one conjecture" is the simple-zeros conjecture verbatim |
| `derivativeNonvanishing_of_left` | — | simplicity need only be checked for Re ρ ≤ 1/2 (symmetry does the rest) |
| `allZerosSimple_of_speiser_and_double_zero_hyp` | RH, `SpeiserTheorem`, `DoubleZeroForcesLeftDerivZero` | output83's argument with both assumptions visible; see §5 |
| `allZerosSimple_of_rh_of_line` | RH, ζ' ≠ 0 at zeros on the line | a restatement; Speiser contributes nothing to simplicity |
| `rh_of_symmetric_operator` | a symmetric operator `T` with eigenvalues (ρ − 1/2)/i | Hilbert–Pólya ⟹ RH, in one step; the operator is the open part |
| `rh_of_realization`, `realization_forces_line` (v3, Schrodinger) | `SchrodingerRealization` (a confining `V` with `L²` eigenfunctions at the levels (ρ − 1/2)/i) | the realization's dictionary conjunct alone forces Re ρ = 1/2: filling it in IS proving RH |
| `eigenvalue_simple_of_realization`, `allZerosSimple_of_realization`, `multiplicityDictionary_iff` (v3, Schrodinger) | a realization, plus a `MultiplicityDictionary` | every level is a simple eigenvalue by Sturm–Liouville (free); the dictionary is ⟺ `AllZerosSimple`, so SL does not shortcut simplicity |
| `on_line_density_one_of_gap` (v3, GapDensity) | `BohrLandau` [LITERATURE], `NcountSuperlinear` [LITERATURE], `SpectralGapHyp Δ` with Δ > 0 | a zero-free strip next to the line plus Bohr–Landau gives density one on the line (which follows from RH and is not known to imply it); folklore, not new mathematics. On the zeta23 tree both literature Props are now theorems (§10), so the same conclusion holds there from the gap alone: `MNF.RH.onLineDensityOne_of_gap_only` (receipt v4). The gap enters only through the window split `gap_forces_NOff_eq` |

## 4. Open — [OPEN]

- `SpectralGapHyp Δ` for any Δ > 0. For Δ > 3/8 it is RH (§2); for every Δ it is, kernel-checked
  (`spectralGapHyp_iff_zeroFree_strip`, §1), the zero-free strip 1/2 < Re ρ < 1/2 + Δ next to the
  line, not known for any Δ > 0. No source in the corpus, the hackathon, or the qexp package
  supplies an argument for it.
- `AllZerosSimple` / `MultiplicityBoundOne` (the simple-zeros conjecture). Nothing in the corpus
  bears on it: all threshold, Bloch-length and residue quantities are real-valued in [0,1], while
  multiplicity is an integer ≥ 1 with no gap structure to exploit.
- `SpeiserTheorem` [LITERATURE, Speiser 1934]: not in Mathlib; kept as a named hypothesis.
- `BohrLandau` and `NcountSuperlinear` [LITERATURE as of 2026-10-29]: no longer open on the zeta23
  tree. `NcountSuperlinear` is proved there from zeta23's Riemann–von Mangoldt formula
  (`MNF.RH.ncountSuperlinear`, receipt v2 of §10) and `BohrLandau` is proved there outright
  (`Zeta23.BL.bohrLandau_full`, receipt v4 of §10). On the OpenAI tree (GapDensity.lean, add-on v3
  of 2026-10-29) they remain named hypotheses; that file is frozen with its receipt.
- `SchrodingerRealization` [OPEN]: an explicit confining `V`; the Berry–Keating / Connes programmes aim
  at exactly this and none is a theorem. `GapMechanism Δ` [OPEN] is ⟺ the band, hence ⟺ RH for Δ > 3/8.
- The operator realization (the corpus's `HPContext`, Hilbert–Pólya): a symmetric operator
  whose eigenvalues are (ρ − 1/2)/i. `rh_of_symmetric_operator` (Hypotheses.lean) shows the
  implication to RH is immediate once such an operator is given, so this route has no content
  short of constructing the operator. The corpus's Sturm–Liouville bridge to it (stress-test
  `sl_simplicity_implies_multiplicity_bound`, stub 2 `HilbertPolyaOperator`) is vacuous as
  written: the first concludes `… → True`, the second quantifies over a `Classical.choice`
  placeholder eigenfunction. Neither is deposited as a theorem about ζ.

## 5. Withdrawn — [WITHDRAWN]

- output83 `axiom argument_principle_double_zero_forces_left_strip_zero` (cited to
  Levinson–Montgomery 1974). Together with Speiser it would give RH ⟹ all zeros simple, which is
  not a known theorem; a multiple zero on the line is a zero of ζ' **on** the line, which Speiser
  does not forbid. The citation does not support the axiom. Consequently output83's
  `rh_implies_all_simple`, `multiple_zero_kills_gap`, `fischer_forward_speiser_path` and the
  "capstone" `rh_and_all_zeros_simple_speiser_path` are withdrawn; the argument survives only in
  the explicit conditional form `allZerosSimple_of_speiser_and_double_zero_hyp`.
- output86 `axiom func_eq_deriv` (ζ'(1−s) = −F(s)ζ'(s) for all s in the strip): false as stated
  (the product rule has a ζ(s)·F'(s) term); replaced by the proved `deriv_reflect` at zeros.
  output86's `rh_and_speiser_implies_simple` contained a `sorry` and is withdrawn.
- output40 / output66–70 (GUE): `riemann_von_mangoldt_stmt`, `montgomery_pair_correlation_stmt`,
  `zero_multiplicity_bound_stmt` and `ZeroDensityControl` are stated over placeholder functions
  (`N_count`, `pair_corr_stat := Classical.choice ⟨…⟩`) that are not the zero-counting function
  or the pair-correlation statistic of ζ. As the corpus's own stub 3 notes, one earlier "proof"
  exploited this vacuity. These statements say nothing about ζ and are not deposited.
- The corpus's `Bridge` hypothesis (output71/72) and `level1_stmt` (output40): no longer
  hypotheses; proved (§1).
- "SpectralGap(1/2) is a physical input" (output40 inventory): under §1 it is RH verbatim, so it
  cannot be described as an input weaker than RH.

## 6. What the deposit can claim

1. An independent Comparator verification of OpenAI's 7/8 zero-free-region theorem (RECEIPT.md),
   with the MNF bridge compiled on top (BRIDGE.md).
2. A kernel-checked library (this add-on, MNF_LIBRARY.md) establishing that the MNF gap
   hypothesis is equivalent to RH for every Δ > 3/8 (given OpenAI's theorem; for Δ ≥ 1/2 from Mathlib
   alone), that the squeeze from the bound |Re ρ − 1/2| ≤ 3/8 does not reach Δ ≤ 3/8
   (`gap_below_bound_insufficient` is a statement about abstract symmetric sets of reals; it does
   not decide whether a gap at such Δ implies RH), and (v2)
   that at every Δ it is exactly a zero-free strip next to the critical line; the multiplicity
   lemmas; the functional-equation symmetry of multiplicities; and the exact relation between
   Mathlib's `RiemannHypothesis` and the strip form. The v1 run (2026-10-28, ACCEPTED) compared
   the 40 statements but listed the 17 definitions as holes, which Comparator compares by name,
   type and universe levels only; the v2 run lists no holes, so it is the run in which the
   definition bodies were compared by Comparator (before it, they were attested by the verbatim
   copy in the challenge and by the audit compile).
3. Not RH, not simplicity, and no new technique toward either. The honest one-line summary:
   *the nullification framework re-expresses RH; it does not reduce it.*
4. (2026-11-03/04, §10) On the zeta23 tree: the density field formalized and kernel-checked;
   Bohr–Landau (1914) formalized from Mathlib and the tree's own approximate formula, so that the
   density-one theorem has exactly one hypothesis left, the gap; the MNF2 injection/ejection
   algebra and the strip model as proved bookkeeping; and the Sturm–Liouville simplicity theorem
   with its first oscillation step as a standalone Lake project (github.com/Joeyxyxyz/sturm-liouville-comparator-run).
   None of this bears on `SpectralGapHyp`, which is unchanged: RH for Δ ≥ 1/2, an open zero-free
   strip for 0 < Δ < 1/2.

## 7. The rest of the corpus (inventory by file group; not re-examined here)

Of the 241 project documents, the RH line consolidated above is: output.lean (1)–(31) /
output32–47 (incl. 40_capstone, 42/44 stress, 45_speiser, 46_average_multiplicity, 47_xi_real),
output48–57 (incl. 56 PathD / signed nullification, 57 signed multiplicity), output58–65 and
the sturm_liouville / Strum_Loui files (Sturm–Liouville simplicity, bridge to HPContext),
output66–70 (GUE suite), output71–86 (minimal axiom, master theorem, definitive capstone,
speiser double zero, master, pole probe), the aristotle stubs 1–3, and
aristotle_stress_test_synthesis. Everything those files prove about ζ that survives is in
§1–§3; what does not is in §5.

Outside the RH line, grouped by name: Batch1–14 and MdBatch1–7 with their `_aristotle`
variants (operator core: classification, monotonicity, distributivity, Yang–Mills, image,
gauge invariance, mass gap, Wightman, IBM validation, NSA equivalence, partition power);
Batch15–17 (3-sphere, zero-zero E field, toroid nullification, topological correction,
dimensional arc); Batch4_1–4_3 (Ξ baryon signed probe, degenerate zero mechanisms, triangle
degenerate zero); Stub5 (finite lattice confining); output87–96 (DMD/DLP projection, NLOS,
OGR, binary hologram, signed depth multiplexing); output97–102 (fluoride phase control,
multizone optimization, temperature coupling, nucleation derived threshold, transport layer,
speciation) and the battery/fluoride files; wormhole_1–4, mnf_wormhole_nsa_merged,
puthoff_pv_nullification, HalJoeyMikePVNOQI; MNFmeetsDavisSet1–4; ProtonExtSet1–2;
RingFlux_vs_SphereFlux / ringVsSphere; output_apery_criterion, output_frontiermath_dioph_mnf,
output_YM_Lagrangian, Shannon_Incompleteness / RequestProject_ShannonIncompleteness;
Complete_StressTest; mnf_qexp_v0_1 (MNFCore_* with AXIOM_AUDIT_core.md). These belong to
Zenodo Vol 1 (operator core) and Vol 3 (physical applications) and are outside this deposit.
The pattern to check in each before any re-deposit is the one documented in §5: a hypothesis
typed as `True`, a `Classical.choice` placeholder standing in for a real function, or a
conclusion of the form `… → True`.

## 8. External results read for this work, not run here — [EXTERNAL]

Register tag **[EXTERNAL | not run here]**: a public, kernel-checked artifact of someone else, read
and pinned by hash, whose Comparator run has not been repeated on this machine. **[EXTERNAL | run
here]** would require a receipt from the kit's launcher, as for OpenAI's theorem (RECEIPT.md).

| artifact | pin | what it says | what it does and does not give the library |
|---|---|---|---|
| OpenAI, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (github.com/openai/math) | commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Lean v4.34.1, Mathlib `d13f23b7`; challenge `lean/ComparatorChallenges/QuasiRiemannHypothesis.lean` sha256 `065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5` | ζ has no zeros with Re s > 7/8 | **[EXTERNAL \| run here]**: kit verdict PASS, cold, 2026-10-27, receipt bundle sha256 `d86705398e4858e034bb8f18397e28984ec6525699b31f1d794b230e1998fcbb`. Consumed once, as `zeroFree_seven_eighths`; everything in §2 rests on it. |
| Anthropic, `zeta23` (github.com/anthropics/formal-math, Alpöge–Furman arXiv:2608.13637) | commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (head on 2026-10-28; the zeta23 files last changed at `2bafb8c8`, 2026-08-28); Lean v4.33.0-rc2; `zeta23/Challenge.lean` sha256 `6f2a4ba95ab8c5319e541a1cc1b3699c0ae8cef23ea8e68f958e11b07281761e`, `ChallengeDeps.lean` `8f9a7e7bb313bbada77d0dd1b71a80bda1c0580b71ba1dd0020b438d63a318e0`, `comparator.json` `610d95c6c84f13b3e2238b476fe45f0b28567108f536f67a0b9ed1586a2c68f1` (17 theorem names, no definition holes, nanoda enabled) | in every window (T, 2T] for large T, at least 2/3 − ε of the zeros counted with multiplicity are simple and on the line (`two_thirds_simple_on_critical_line`), at least 2/3 − ε are on the line, at least 5/6 − ε are distinct, with Montgomery–Taylor refinements and Dirichlet analogues | **[EXTERNAL \| run here]** as of 2026-10-28: the qrh-zeta23 add-on's cold Comparator run under the kit's launcher, Lean kernel + NanoDa, verdict PASS, 11:08:56–11:29:58 UTC, receipt bundle `qrh-zeta23-receipt.tar.gz` sha256 `e0b9a4d97a04dff75f25cca69f28e684a785bd5f633ea8d0763085be7ea364e5` (Comparator v4.33.0-rc2 `75c730e9`, lean4export `9fb131bb`, nanoda `68d5ca9d`, seven toolchain binaries pinned, all 17 statements, no deviations). Its trusted `IsNontrivialZero` and `zeroMult` are, body for body, this library's `is_nontrivial_zero` and `zeta_order`, so its theorems transfer to MNF vocabulary by definitional unfolding; but it lives at a different Lean/Mathlib pin from OpenAI's tree and this library's Unconditional layer, so no file here imports it. It discharges none of `SpectralGapHyp Δ`, `AllZerosSimple`, `MultiplicityBoundOne`, `DerivativeNonvanishing`: a proportion of zeros, however large, is not a statement about every zero. The decimal constants quoted for it (0.67250, 0.83625) are docstrings, not statements. |

Zero-free half-planes left of 7/8, read on 2026-10-28 (none run here, none registered on Palomar,
all built on OpenAI's own argument by parameter refinement, all at the same pin as this add-on,
Lean v4.34.1 / Mathlib `d13f23b7`): Baiying Liu, arXiv:2610.12234, repository
`liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis`, theorem
`algebraic_zeta_nonzero (s : ℂ) (hs : B_new < s.re) (hpole : s ≠ 1) : riemannZeta s ≠ 0` with
`B_new = (1507 - 2 * Real.sqrt 921) / 1653 ≈ 0.874957`, replayed by the community Quasi-Riemann
Tracker (github.com/GTimG/QuasiRiemannTracker, record `liu-20261010-safe-replay`, Lean kernel +
NanoDa + con-ron, status PASS, not a signed registry admission); and the tracker's own frontier on
2026-10-27, `174797/200000 = 0.873985` (Rohan Arun, tracker PR 84), in the all-Dirichlet form
`LFunction_ne_zero_of_…` from which the ζ case is the `q = 1` specialization. Any of these, once
receipted the way OpenAI's theorem was (a cold Comparator run of its tree under the kit's launcher),
instantiates `riemannHypothesis_iff_gap_of_zeroFree` and `riemannHypothesis_iff_remaining_strip`
verbatim at its θ, with `θ − 1/2` in place of `3/8`; none is used here. Lean zero-density
estimates exist on Palomar (Mark Lewko, PALOMAR-2026-10-07-000009, -10-09-000005, -10-11-000010
and -10-21-000008; the third on Lean v4.35.0-rc2, another pin), one-sided (`Re ρ ≥ σ`), which with the reflection `ρ ↦ 1 − ρ` of
`nontrivial_zero_reflect` would supply the Bohr–Landau-type input the §4 gap-forces-density
remark needs; not attempted at the time (2026-10-28). That input was later proved on the zeta23
tree instead (§10, run 9); Lewko's estimates are earlier and stronger than the zero-density
estimate of run 10 (§10, Prior Lean work).

**The restatement layer (B2, 2026-10-29 UTC), [RESTATEMENT \| zeta23] and [BOOKKEEPING]:** on the
receipted zeta23 checkout, the qrh-zeta23 add-on's second Comparator run (label `zeta23-mnf`, Lean
kernel + NanoDa, MNF_ZETA23=ACCEPTED, 02:06:38–02:12:34 UTC, bundle `qrh-zeta23-mnf-receipt.tar.gz`
sha256 `1476f56809c5739866e538d84d41670d573dc37fb56f74ddcc1709da065c1eef`) judged 62 statements and
23 definition bodies: the 36 Mathlib-only statements of the MNF library (Core, Gap, Hypotheses,
byte-identical to add-on v2), `MNF/RH/Counting.lean` (zeta23's counting vocabulary over
`is_nontrivial_zero` and `zeta_order`; `zerosIn_finite`; `Ndist_le_Ncount`; and the two
restatements `riemannHypothesis_iff_window_counts` : RH ⟺ ∀ T₁ T₂, N0star = Ndist, and
`allZerosSimple_iff_window_counts` : AllZerosSimple ⟺ ∀ T₁ T₂, Ncount = Ndist), and
`MNF/RH/Zeta23Restated.lean` (zeta23's Theorems A–D for ζ over MNF's definitions, by delegation:
`twoThirdsOnLine`, `twoThirdsSimpleOnLine`, `fiveSixthsDistinct`, the five `montgomeryTaylor*`
bounds and the cumulative forms, plus `twoThirdsOnLineDerivNeZero` and
`fiveSixthsDistinct_sandwich`). Register: bookkeeping and restatement; it discharges none of
`SpectralGapHyp`, `AllZerosSimple`, `MultiplicityBoundOne`, `DerivativeNonvanishing`, and uses
nothing of the 7/8 theorem. The six Dirichlet statements of zeta23 are not restated.

What the two external results do not do together: nothing. The 7/8 theorem bounds how far from
the line a zero can sit; zeta23 bounds what proportion of zeros sit on it; neither input enters
the other's proof, and a sentence that puts "2/3" and "7/8" together as one theorem would be
false advertising. The honest composition is a restatement of zeta23's theorems over MNF's
definitions, which is Stage B of the plan (a receipted Comparator run of zeta23 first).

## 9. The frontier package and the lattice experiment (v3)

`Reduction.lean` and `Schrodinger.lean` (notes/FRONTIER.md) rewrite every "attack" idea of the
corpus as an `↔` or a named `Prop`, so the remaining content is a Lean goal: the band
`1/2 < Re ρ ≤ 7/8` on one side (`rh_of_band_seven_eighths`), or a `SchrodingerRealization`. Nothing
in them proves RH or the simple-zeros conjecture, and `multipleZeroKillsGap_iff` /
`fischerForward_iff` show that the February "Fischer forward" chain is `RH ∧ (RH → simple) → RH ∧
simple`.

**MultipleZeroKillsGap experiment (Feb 2026).** A 64-qubit IBM run showing that forced component
degeneracy suppresses the confinement correlator in a 2×4 pure-gauge lattice model (−22% on
untouched components vs. a depth-matched control, P > 99.99%). Filed under lattice gauge /
Yang–Mills. The accompanying Lean hypotheses `FischerForward` and `MultipleZeroKillsGap` are each
kernel-equivalent to "RH ⟹ all zeros simple" (`fischerForward_iff`, `multipleZeroKillsGap_iff`,
MNF/RH/Reduction.lean), so the experiment is **not** evidence for or against RH and is not cited
as such. (Wording from notes/FischerForward_The_Math.md §6.)

## 10. The density field and Bohr–Landau on the zeta23 tree (2026-11-03/04)

Five further Comparator runs on the zeta23 checkout that run 2 checked (under the kit's launcher,
AF_UNIX denied, Lean kernel and NanoDa, no definition holes, so that the body of every definition
a claimed statement refers to is compared). The receipts record these runs as warm: the Zeta23
library was compiled by run 2, and the modules of earlier layer runs by those runs; each run is
cold only for the modules its add-on introduces, which the launch script enforces. They report
ACCEPTED, not the kit's PASS, which is reserved for cold runs. The working notes, the receipts
extracted, the plans, the adversarial prose reviews and the per-agent sources are in
`notes/density-field-2026-11-03/` (ledger `DENSITY_LEDGER.md`).

| run | label | add-on | receipt | theorems | result |
|---|---|---|---|---|---|
| 7 | `zeta23-density` | `qrh-zeta23-addon-v2.tar.gz` `5dc41dff…` | `qrh-zeta23-density-receipt.tar.gz` `975b2178…` | 124 (66 definitions) | ACCEPTED 2026-11-03 21:05–21:13 UTC |
| 8 | `zeta23-density-v3` | `qrh-zeta23-addon-v3.tar.gz` `c0958d53…` | `qrh-zeta23-density-v3-receipt.tar.gz` `0588555d…` | 270 (76) | ACCEPTED 2026-11-03 22:03–22:09 UTC |
| 9 | `zeta23-density-v4` | `qrh-zeta23-addon-v4.tar.gz` `fb74e8a2…` | `qrh-zeta23-density-v4-receipt.tar.gz` `0d1919e4…` | 334 (81) | ACCEPTED 2026-11-04 00:52–00:58 UTC |
| 10 | `zeta23-density-v5` | `qrh-zeta23-addon-v5.tar.gz` `2d2cf058…` | `qrh-zeta23-density-v5-receipt.tar.gz` `37a806b2…` | 480 (98) | ACCEPTED 2026-11-04 14:38–14:45 UTC |
| 11 | `zeta23-density-v6` | `qrh-zeta23-addon-v6.tar.gz` `99575a1e…` | `qrh-zeta23-density-v6-receipt.tar.gz` `ca07a500…` | 534 (110) | ACCEPTED 2026-11-11 00:02–00:17 UTC |

Each run re-judges everything of the previous one plus the new modules; run 11 is the complete
layer. What is proved there, in register terms:

| theorem (module) | status | note |
|---|---|---|
| `MNF.RH.ncountSuperlinear` (Density) | [RESTATEMENT \| zeta23] | N(T)/T → ∞, delegated to zeta23's Riemann–von Mangoldt formula; discharges the v3 hypothesis `NcountSuperlinear` |
| `MNF.RH.offLine_le_one_third`, `NOff_le_one_third` (Density) | [RESTATEMENT \| zeta23] | off-line zeros ≤ (1/3 + ε)·N(0,T), with multiplicity: zeta23's Theorem B read as an upper bound |
| `NNear_eq_nullified_count`, `Ncount_eq_near_add_off`, `NNear_eq_N0_of_gap` (Density) | [PROVED] bookkeeping | the reservoir count is the count of zeros nullified at δ; every window splits at every δ; under a gap at Δ the Δ-reservoir is empty |
| `ReservoirDensityOne` ← `BohrLandau` (`reservoirDensityOne_of_bohrLandau`); `OnLineDensityOne` ← `BohrLandau` + gap (`onLineDensityOne_of_gap`) (Density) | [CONDITIONAL] | the "for every fixed δ" density versus density on the line itself; the gap is used once, to identify the Δ-near count with the on-line count |
| Strip.lean (19), MNF/Extension/InjectionEjection.lean (56) | [PROVED] bookkeeping, operator algebra | the band around the line under N, E and injection; no analytic content; the MNF2 package's algebra (also ACCEPTED at the OpenAI pin on 2026-11-03) |
| `Zeta23.BL.bohrLandau_gt_sixth`, `rightHalf_gt_sixth`, `M3.meanSquareUnif_explicit` (BohrLandauPartial) | [PROVED \| this tree] | Bohr–Landau for δ > 1/6 and the uniform mean square for σ ≥ 2/3, from the tree's approximate formula with its naive error (run 8) |
| `BLClosure.first_derivative_test_smooth` / `_amp_smooth`, `B2per_fourier`, `zeta_eq_euler_maclaurin`, `tail_sharp`, `zeta_approx_sharp`, `meanSquareUnif_all` (BohrLandauClosure) | [PROVED \| this tree] | Titchmarsh Lemmas 4.2/4.3 for smooth phases; the Fourier series of B₂; Euler–Maclaurin for ζ; the sharp tail; the approximate formula with error O(N^{−σ}) for N ≥ t; the classical O(T) mean square of ζ on the lines σ ≥ σ₁, for every σ₁ > 1/2 (run 9) |
| **`Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau`** (BohrLandauClosure) | [PROVED \| this tree] | for every δ > 0 the nontrivial zeros with 0 < Im ρ ≤ T and \|Re ρ − 1/2\| ≥ δ, with multiplicity, number ≤ C_δ·T (T ≥ 2). Bohr–Landau 1914, formalized; not new mathematics |
| `MNF.RH.reservoirDensityOne_unconditional`, **`onLineDensityOne_of_gap_only`** (BohrLandauClosure) | [PROVED \| this tree]; [CONDITIONAL] on the gap alone | density one within every fixed δ of the line with no hypothesis; a gap at any Δ > 0 gives density one on the line with no other hypothesis. For Δ ≥ 1/2 the gap is RH (§1); for 0 < Δ < 1/2 it is the open strip of §4 |
| `Zeta23.BL.meanSquare_strip'`, `rightHalfBound_of_meanSquare'` (BohrLandauClosure) | [PROVED \| this tree] | the two statements that `Zeta23/BohrLandau.lean` named as `sorry`; the originals are kept untouched (their sorries are in no claim set); at σ = 1 the ∫₀ᵀ form holds only by Mathlib's junk-value convention, as the docstrings say |
| `MNF.RH.reservoirMass_eq_integral`, `reservoirMass_le_half_Ncount`, `signedReservoir_eq_zero`, `reservoirMass_eq_two_right` (ReservoirMass) | [PROVED] bookkeeping | the reservoir mass Σ m(ρ)·\|Re ρ − 1/2\| over 0 < Im ρ ≤ T (the total displacement of the zeros from the line, with multiplicity) is the layer-cake integral ∫₀^{1/2} NOff(δ; 0, T) dδ, is ≤ ½·N(0,T), its signed version Σ m(ρ)(Re ρ − 1/2) is 0 by the reflection ρ ↦ 1 − ρ̄, and it is twice the right-half signed sum |
| `Zeta23.BL.bohrLandau_explicit` (ReservoirMass) | [PROVED \| this tree] | NOff(δ; 0, T) ≤ (A·δ^{−5/2} + B)·T for 0 < δ ≤ 1/2 and T ≥ 2, with A and B explicit up to the tree's two existential constants (the approximate-formula constant at σ₀ = 1/2 and the unit-window Riemann–von Mangoldt constant) |
| **`MNF.RH.reservoirMass_le_rpow`**, `reservoirMass_le_Ncount_mul`, **`meanDisplacement_tendsto_zero`** (ReservoirMass) | [PROVED \| this tree] | reservoirMass T ≤ A·T·(log T)^{3/5} for T ≥ T₀, hence ≤ A·(log T)^{−2/5}·N(0,T): the mean distance of the zeros from the line, with multiplicity, tends to 0. Far weaker than Littlewood 1924 (O(T log log T)) and Selberg 1946 (O(T)); compatible with infinitely many zeros off the line and silent on the gap |
| **`Zeta23.Density.density_single_window`** (StripDensity) | [PROVED \| this tree] | for 1/2 < σ₁ and σ₁ − 1/2 < δ ≤ 1/2: NRight(δ, T) ≤ C·T^{1 − (2σ₁−1)²/(2σ₁)}·(1 + log T)³ for all T ≥ 2 (at σ₁ = 3/4: O(T^{5/6}(log T)³)) — a zero-density estimate with a power saving, Carlson's method with one approximate formula on one window; weaker than Carlson's exponent 4σ₁(1 − σ₁), which is not proved. A count, not a zero-free region: it excludes no individual zero and says nothing about zeros closer than δ to the line |
| `sum_dX_sq_le`, `S_mul_Mx_eq`, `fz_sub_one_eq`, `meanSquare_fz_window`, `count_le_meanSquare_fz` (StripDensity) | [PROVED], [PROVED \| this tree] | the divisor bound Σ_{m≤Y} d_X(m)² ≤ Y(1 + log X)³; the product polynomial S_N·M_X; the Möbius identity ζ·M_X − 1 = −ζ·Σ_{n>X} μ(n)n^{−s} for Re s > 1; the window mean square of ζ·M_X; the Jensen-disc count with the majorant ½ log(ε² + ‖f‖²) |
| `MNF.RH.degenerate_of_not_onLine`, **`noDegenerate_iff`** (Cube) | [PROVED \| this tree] (the reflection lemma of the zeta23 library is used); an equivalence | an off-line zero shares its ordinate with its mirror 1 − ρ̄, so it is *degenerate* (multiple, or sharing an ordinate with another zero); "no nontrivial zero is degenerate" ⟺ "every nontrivial zero is on the line and simple". Relocates RH together with the simplicity conjecture; proves neither |
| **`MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`**, `spectralGapHyp_iff_not_inBand`, **`spectralGapHyp_iff_bandCoincidentMass`** (Cube) | [PROVED \| this tree]; an equivalence | `SpectralGapHyp Δ` ⟺ no two distinct zeros within distance < Δ of the line share an ordinate ⟺ the band's coincident mass vanishes in every window (0, T]. Relocates the gap, which stays [OPEN] |
| **`MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo`**, `nontrivial_zero_im_ne_zero` (Cube) | [PROVED \| this tree] | ζ(σ) ≠ 0 for real 0 < σ < 1, so every nontrivial zero has a nonzero ordinate; from the tree's one-term Euler–Maclaurin representation with the remainder bounded by 1/(2σ). Classical and elementary; a zero-free statement about the real segment only, not about the interior of the strip |
| `pairSum_const`, `pairSum_fst_indicator`, `pairSum_fst_abs`, `pairSum_fst_abs_eq_integral`, `pairSum_swap` (Cube) | [PROVED] bookkeeping | the pair measure of a window ("the cube": ordered pairs of zeros at (Re ρ − 1/2, Re ρ′ − 1/2, Im ρ − Im ρ′) with weight m(ρ)m(ρ′)): total mass N², first marginals N·NOff and N·reservoirMass, the double layer cake N·∫₀^{1/2} NOff dδ |
| `coincidentMass_eq`, `offLine_sq_le_offDiagonalCoincidentMass`, `offDiagonalCoincidentMass_le`, `offDiagonalCoincidentMass_le_five_ninths` (Cube) | [PROVED \| this tree] (bookkeeping on the reflection lemma; Theorem B for the eventual bound) | the atom at ordinate difference 0 is the diagonal mass Σ m(ρ)² plus the off-diagonal coincidences; each off-line zero contributes m(ρ)² through its mirror; the off-diagonal part is ≤ NOffLine·(N + N0), hence eventually ≤ (5/9 + ε)·N² by Theorem B. The cubic small-distance law of the zeros is the GUE prediction (Montgomery 1973), not a theorem |

Register tag **[PROVED | this tree]**: proved on the zeta23 checkout from Mathlib and the tree's
sorry-free files (zeta23's own library, receipted in run 2), delegated by unfolding where it is
restated over MNF's names. Nothing in §10 touches `SpectralGapHyp`, `AllZerosSimple` or the
simple-zeros conjecture, uses the 7/8 theorem, or combines the two external results. The
Sturm–Liouville file of add-on v3 lives on as the standalone project
github.com/Joeyxyxyz/sturm-liouville-comparator-run (simplicity plus the first oscillation step,
Comparator-accepted 2026-11-03; no completed Lean proof of the simplicity theorem was known to the
author as of 2026-11-03, see notes/density-field-2026-11-03 and the project's README).

Erratum (2026-11-04). The report inside the run 9 bundle (`density-v4/MNF_DENSITY.md`, block
`## How to read this`) carries the sentence "Bohr–Landau itself is NOT proved …", inherited from
the v2/v3 report generator, where it was true; for run 9 it is false, as the same report's
statement block and axiom table show (`Zeta23.BL.bohrLandau_full` with standard axioms). The
verdict, the audit and the hashes of run 9 are unaffected; the generator is corrected in add-on
v5 and the run 10 report carries the corrected prose; the run 9 bundle is not altered. The
zero-density estimate of run 10 is a count of zeros off the line, not a zero-free region:
`SpectralGapHyp` stays [OPEN] for every Δ, exactly as in §6. The equivalences of run 11 restate RH
with simplicity, and the gap, as statements about coincident ordinates of zeros; each side of each
equivalence is as open as the other.

Prior Lean work (read 2026-11-10/11 for the paper, not run here). Mark Lewko's four Palomar entries
named in §8 register zero-density estimates with stronger exponents than
`Zeta23.Density.density_single_window` (run 10), on another toolchain pin and not on the zeta23
tree; they imply the one-sided Bohr–Landau bound. The absence of real zeros of ζ in (0, 1)
(run 11) has earlier Lean proofs: by the same one-term Euler–Maclaurin route in
AxiomMath/ZetaZerosV2 (`ZetaZeros/Analytic/RealSegment.lean`, commit `1d7edeb4`, 2026-10-03), and
in sthubbar/goldbach-lean. Neither result is claimed as a first formalization. The phrase "first
kernel-checked zero-density estimate with a power saving" in the working notes of run 10
(`strip/STRIP_PLAN.md`, `strip/STRIP_SCOPE_REPORTS_2026-11-04.md`) was provisional, subject to
reading those entries, and does not hold.

Errata (2026-11-11, found while the paper was prepared; no bundle is altered). (1) The receipts
record runs 6 to 11 as warm, cold only for the modules each add-on introduces; this section said
"cold" until this revision, and "cold run" in the ledger means a run under the launcher on the
`qrh` account in that sense. (2) The reports of runs 4 to 11 say that the definitions of the
challenge were "all compared by name, type and body"; the number they print counts `def` lines of
the challenge modules, and Comparator compares those a claimed statement refers to, so each count
is an upper bound (in run 11, `Zeta23.BL.CG`, `meanSquareB` and `A₀` are counted and no claimed
statement refers to them). (3) The "What was proved" block of the reports of runs 7 to 11 omits
the statements Lean prints with a leading `@` (279 of 534 in run 11); the axiom table and
`audit.out` have all. (4) The run 8 report's "How to read this" block is run 7's and does not
mention Bohr–Landau for δ > 1/6, which its statement block and axiom table contain. (5) Run 2's
receipt records an add-on manifest hash (`a20b1b1d…`) other than that of the deposited
`qrh-zeta23-addon.tar.gz` (`0c37cc13…`), which also carries run 6's step: an earlier version of
the add-on launched run 2 and is not in the record; what run 2 judged is fixed by its receipt.
(6) §6 item 2 said the gap hypothesis is "insufficient for every Δ ≤ 3/8" and §1 called the
threshold "exact"; the Lean statement `gap_below_bound_insufficient` is about abstract symmetric
sets of reals and shows only where the squeeze stops. (7) The equivalences of `Cube.lean` were
tagged [PROVED]; their proofs use the zeta23 library's reflection lemma, so the tag is
[PROVED | this tree]. (8) In `notes/density-field-2026-11-03/numeric/RESULTS.md` the "exact GUE"
standard deviation 0.4221 is a typed constant (the Wigner surmise gives 0.4220; `numeric/gue_sd.py`
recomputes the exact law's value, 0.4243), and the eleven tabulated ordinates it compares with are
constants "as recalled", not read from the tables. (9) The mean square on the lines σ > 1/2 was
attributed here and in the README to Hardy and Littlewood without the source having been checked;
it is now called classical. The paper (`paper/`) states each of these.

