# MNF × Riemann zeta — deposit map

What in the Lean corpus is proved, what is conditional (and on what), what is open, and what
is withdrawn. Written 2026-10-27 against the consolidated library `MNF/RH/*.lean` in this
add-on, which replaces the RH files of the corpus (output28–86) for deposit purposes.

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

## 2. Unconditional given OpenAI's theorem — [PROVED | 7/8] (MNF/RH/Unconditional.lean)

`zeroFree_seven_eighths`, `nontrivial_zero_re_le_seven_eighths`, `shifted_bounded_three_eighths`,
`riemannHypothesis_iff_gap_three_eighths` (RH ⟺ gap at any Δ > 3/8),
`riemannHypothesis_iff_remaining_strip_seven_eighths` (RH ⟺ no zeros in 1/2 < Re s ≤ 7/8),
`rh_of_gap_three_eighths`. Same content as the kit's `MNF_Bridge78_Unconditional.lean`,
restated over the consolidated definitions.

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

## 4. Open — [OPEN]

- `SpectralGapHyp Δ` for any Δ > 0. For Δ > 3/8 it is RH (§2); for Δ ≤ 3/8 it is a zero-free
  strip 1/2 < Re ρ < 1/2 + Δ around the line, not known for any Δ > 0. No source in the corpus,
  the hackathon, or the qexp package supplies an argument for it.
- `AllZerosSimple` / `MultiplicityBoundOne` (the simple-zeros conjecture). Nothing in the corpus
  bears on it: all threshold, Bloch-length and residue quantities are real-valued in [0,1], while
  multiplicity is an integer ≥ 1 with no gap structure to exploit.
- `SpeiserTheorem` [LITERATURE, Speiser 1934]: not in Mathlib; kept as a named hypothesis.
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
   hypothesis is equivalent to RH for every Δ > 3/8 and insufficient for every Δ ≤ 3/8; the
   multiplicity lemmas; the functional-equation symmetry of multiplicities; and the exact
   relation between Mathlib's `RiemannHypothesis` and the strip form.
3. Not RH, not simplicity, and no new technique toward either. The honest one-line summary:
   *the nullification framework re-expresses RH; it does not reduce it.*

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
