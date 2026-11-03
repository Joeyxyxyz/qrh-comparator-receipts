# MNF × Riemann zeta — deposit map

What in the Lean corpus is proved, what is conditional (and on what), what is open, and what
is withdrawn. Written 2026-10-27 against the consolidated library `MNF/RH/*.lean` in this
add-on, which replaces the RH files of the corpus (output28–86) for deposit purposes; revised
2026-10-28 for add-on v2 (three theorems added, §1–§2; §8 added), and 2026-10-29 for add-on v3
(the frontier package: §1 Counting and Reduction rows, §3 Schrodinger and GapDensity rows, §9).

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
| `spectralGapHyp_three_eighths_iff_of` (v2) | given `ZeroFreeRightOf (7/8)`: gap at exactly 3/8 ⟺ every nontrivial zero has Re ∈ {1/2, 1/8, 7/8} | new; shows the threshold Δ > 3/8 of §2 is exact |
| `zerosIn_finite`, `Ndist_le_Ncount`, `N0star_le_Ndist`, `N0simple_le_N0star` (v3, Counting) | the zeros in a window (T₁,T₂] are finitely many; distinct ≤ with multiplicity; on-line ≤ distinct; simple on-line ≤ on-line | [BOOKKEEPING]; zeta23's vocabulary over MNF's names |
| `riemannHypothesis_iff_window_counts`, `allZerosSimple_iff_window_counts` (v3, Counting) | RH ⟺ ∀ T₁ T₂, N0star = Ndist; AllZerosSimple ⟺ ∀ T₁ T₂, Ncount = Ndist | [BOOKKEEPING] restatements, not density results |
| `gap_iff_zeroFreeBand`, `gap_of_right_side`, `rh_of_band_of_zeroFree` (v3, Reduction) | the gap at Δ IS the zero-free band 1/2 < Re ρ < 1/2 + Δ; one side suffices; with a region Re > θ, RH ⟺ no zero with 1/2 < Re ρ ≤ θ | frontier package; `rh_of_band_seven_eighths` is the θ = 7/8 instance (§2) |
| `multipleZeroKillsGap_iff`, `fischerForward_iff` (v3, Reduction) | the corpus hypotheses `MultipleZeroKillsGap` and `FischerForward` are each ⟺ (RH → AllZerosSimple) | so neither is a route to RH and no experiment bears on them (notes/FischerForward_The_Math.md) |
| `rh_of_realSpectrumRealization`, `allZerosSimple_of_multiplicity_dictionary` (v3, Reduction) | a set of reals containing (ρ − 1/2)/i for every zero is RH; a multiplicity dictionary with all multiplicities 1 is simplicity | Hilbert–Pólya without an operator |
| `gap_of_mechanism`, `mechanism_of_gap`, `gapMechanism_iff`, `probes_zero_iff` (v3, Reduction) | a gap mechanism (a predicate every band zero has and nothing has) is the same as the band; both τ-probes read 0 ⟺ Re ρ = 1/2 | the precise form of "the gap route is RH restated" |
| `sturm_liouville_simple_eigenvalues` (v3, SturmLiouville) | for a continuous confining `V`, any two `L²` eigenfunctions of −u'' + V u = λu are proportional | Joey's consolidated corpus file (Aristotle), ported to this pin; a statement about 1-D Schrödinger operators, not about ζ |
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
| `on_line_density_one_of_gap` (v3, GapDensity) | `BohrLandau` [LITERATURE], `NcountSuperlinear` [LITERATURE], `SpectralGapHyp Δ` with Δ > 0 | **the one place the gap does work**: a zero-free strip next to the line plus Bohr–Landau gives density one on the line, strictly weaker than RH; folklore, not new mathematics; neither Prop is in any Lean library |

## 4. Open — [OPEN]

- `SpectralGapHyp Δ` for any Δ > 0. For Δ > 3/8 it is RH (§2); for every Δ it is, kernel-checked
  (`spectralGapHyp_iff_zeroFree_strip`, §1), the zero-free strip 1/2 < Re ρ < 1/2 + Δ next to the
  line, not known for any Δ > 0. No source in the corpus, the hackathon, or the qexp package
  supplies an argument for it.
- `AllZerosSimple` / `MultiplicityBoundOne` (the simple-zeros conjecture). Nothing in the corpus
  bears on it: all threshold, Bloch-length and residue quantities are real-valued in [0,1], while
  multiplicity is an integer ≥ 1 with no gap structure to exploit.
- `SpeiserTheorem` [LITERATURE, Speiser 1934]: not in Mathlib; kept as a named hypothesis.
- `BohrLandau` and `NcountSuperlinear` [LITERATURE, Bohr–Landau 1914; Riemann–von Mangoldt]: not in Mathlib
  at this pin; Palomar holds one-sided zero-density estimates (Lewko, Lean v4.35.0-rc2) that could
  discharge `BohrLandau` after a port. Kept as named hypotheses (GapDensity.lean).
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
   hypothesis is equivalent to RH for every Δ > 3/8 and insufficient for every Δ ≤ 3/8, and (v2)
   that at every Δ it is exactly a zero-free strip next to the critical line; the multiplicity
   lemmas; the functional-equation symmetry of multiplicities; and the exact relation between
   Mathlib's `RiemannHypothesis` and the strip form. The v1 run (2026-10-28, ACCEPTED) compared
   the 40 statements but listed the 17 definitions as holes, which Comparator compares by name,
   type and universe levels only; the v2 run lists no holes, so it is the run in which the
   definition bodies were compared by Comparator (before it, they were attested by the verbatim
   copy in the challenge and by the audit compile).
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

## 8. External results read for this work, not run here — [EXTERNAL]

Register tag **[EXTERNAL | not run here]**: a public, kernel-checked artifact of someone else, read
and pinned by hash, whose Comparator run has not been repeated on this machine. **[EXTERNAL | run
here]** would require a receipt from the kit's launcher, as for OpenAI's theorem (RECEIPT.md).

| artifact | pin | what it says | what it does and does not give the library |
|---|---|---|---|
| OpenAI, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (github.com/openai/math) | commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Lean v4.34.1, Mathlib `d13f23b7`; challenge `lean/ComparatorChallenges/QuasiRiemannHypothesis.lean` sha256 `065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5` | ζ has no zeros with Re s > 7/8 | **[EXTERNAL \| run here]**: kit verdict PASS, cold, 2026-10-27, receipt bundle sha256 `d86705398e4858e034bb8f18397e28984ec6525699b31f1d794b230e1998fcbb`. Consumed once, as `zeroFree_seven_eighths`; everything in §2 rests on it. |
| Anthropic, `zeta23` (github.com/anthropics/formal-math, Alpöge–Furman arXiv:2608.13637) | commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (head on 2026-10-28; the zeta23 files last changed at `2bafb8c8`, 2026-08-28); Lean v4.33.0-rc2; `zeta23/Challenge.lean` sha256 `6f2a4ba95ab8c5319e541a1cc1b3699c0ae8cef23ea8e68f958e11b07281761e`, `ChallengeDeps.lean` `8f9a7e7bb313bbada77d0dd1b71a80bda1c0580b71ba1dd0020b438d63a318e0`, `comparator.json` `610d95c6c84f13b3e2238b476fe45f0b28567108f536f67a0b9ed1586a2c68f1` (17 theorem names, no definition holes, nanoda enabled) | in every window (T, 2T] for large T, at least 2/3 − ε of the zeros counted with multiplicity are simple and on the line (`two_thirds_simple_on_critical_line`), at least 2/3 − ε are on the line, at least 5/6 − ε are distinct, with Montgomery–Taylor refinements and Dirichlet analogues | **[EXTERNAL \| not run here]**. Its trusted `IsNontrivialZero` and `zeroMult` are, body for body, this library's `is_nontrivial_zero` and `zeta_order`, so its theorems transfer to MNF vocabulary by definitional unfolding; but it lives at a different Lean/Mathlib pin from OpenAI's tree and this library's Unconditional layer, so no file here imports it. It discharges none of `SpectralGapHyp Δ`, `AllZerosSimple`, `MultiplicityBoundOne`, `DerivativeNonvanishing`: a proportion of zeros, however large, is not a statement about every zero. The decimal constants quoted for it (0.67250, 0.83625) are docstrings, not statements. |

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
estimates exist on Palomar (Mark Lewko, PALOMAR-2026-10-11-000010 and -10-21-000008, Lean
v4.35.0-rc2, another pin), one-sided (`Re ρ ≥ σ`), which with the reflection `ρ ↦ 1 − ρ` of
`nontrivial_zero_reflect` would supply the Bohr–Landau-type input the §4 gap-forces-density
remark needs; not attempted.

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

