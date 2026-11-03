/-
═══════════════════════════════════════════════════════════════════════
MNF × QUASI-RH BRIDGE — UNCONDITIONAL LAYER
The theorems of MNF_Bridge78.lean §7 and §8 with the 7/8 hypothesis
discharged from OpenAI's proof.
═══════════════════════════════════════════════════════════════════════
Lean:    leanprover/lean4:v4.34.1
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612   (the pin of openai/math)
Compiles ONLY inside the `lean/` tree of github.com/openai/math at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, after that tree has been built.

REGISTER: [WRAPPER].  No mathematics happens in this file.  Every proof is
one application of a theorem of MNF_Bridge78.lean to

    zeroFree_seven_eighths : ZeroFreeRightOf (7/8)
      := fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

STATUS.  These statements are exactly as reliable as OpenAI's theorem.
They may be cited as proved only together with a Comparator PASS for
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` at that commit (see the
receipt produced by the kit this file ships in).  Without that receipt the
register is [ASSERTED].

WHAT THIS DOES NOT SAY.  The Riemann Hypothesis is not among the theorems
below.  `riemannHypothesis_iff_remaining_strip_unconditional` states what is
left of it: no zeros with 1/2 < Re s ≤ 7/8.  The MNF gap hypothesis
(`SpectralGapProperty ShiftedZeroSpectrum Δ`) stays open at every Δ > 0;
`riemannHypothesis_iff_gap_unconditional` only lowers the threshold at which
it is equivalent to RH from 1/2 to any Δ > 3/8.
-/

import MNF_Bridge78
import OAI.NumberTheory.DirichletL.Nonvanishing

namespace MNF.Bridge78

/-- OpenAI's theorem, in the form the bridge consumes: `ζ` has no zeros with
real part greater than `7/8`. -/
theorem zeroFree_seven_eighths : ZeroFreeRightOf (7/8) :=
  fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- Every nontrivial zero lies in the closed strip `1/8 ≤ Re s ≤ 7/8`. -/
theorem nontrivial_zero_re_mem_unconditional {ρ : ℂ} (hρ : is_nontrivial_zero ρ) :
    1/8 ≤ ρ.re ∧ ρ.re ≤ 7/8 :=
  nontrivial_zero_re_mem zeroFree_seven_eighths hρ

/-- The shifted zero spectrum lies in `[-3/8, 3/8]`. -/
theorem shifted_bounded_three_eighths_unconditional :
    ∀ x ∈ ShiftedZeroSpectrum, |x| ≤ 3/8 :=
  shifted_bounded_three_eighths zeroFree_seven_eighths

/-- Mathlib's `RiemannHypothesis` is equivalent to the MNF gap at any
threshold `Δ > 3/8`. -/
theorem riemannHypothesis_iff_gap_unconditional {Δ : ℝ} (hΔ : 3/8 < Δ) :
    RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ :=
  riemannHypothesis_iff_gap zeroFree_seven_eighths hΔ

/-- **What is left of RH**: exactly the statement that `ζ` has no zeros in
the strip `1/2 < Re s ≤ 7/8`. -/
theorem riemannHypothesis_iff_remaining_strip_unconditional :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 7/8 → riemannZeta s ≠ 0 :=
  riemannHypothesis_iff_remaining_strip zeroFree_seven_eighths

/-- The ζ-zero set satisfies every hypothesis of the structural no-go
(`structural_inputs_insufficient`): those inputs alone cannot force the line. -/
theorem zetaZeros_satisfies_structural_inputs_unconditional :
    StripSymmetric ZetaZeros ∧ (∀ ρ ∈ ZetaZeros, ρ.re ≤ 7/8) :=
  zetaZeros_satisfies_structural_inputs zeroFree_seven_eighths

/-- `F = ζ · Q` is zero-free in `Re s > 7/8`, like `ζ`, and still has a zero
inside the remaining strip (K3 of MNF_Bridge78.lean). -/
theorem euler_type_no_go_unconditional :
    (∀ s : ℂ, 7/8 < s.re → riemannZeta s * twoFactor s ≠ 0) ∧
    (∃ s : ℂ, 1/2 < s.re ∧ s.re ≤ 7/8 ∧ riemannZeta s * twoFactor s = 0) :=
  euler_type_no_go_under_h78 zeroFree_seven_eighths

end MNF.Bridge78

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.Bridge78.zeroFree_seven_eighths
#print axioms MNF.Bridge78.nontrivial_zero_re_mem_unconditional
#print axioms MNF.Bridge78.shifted_bounded_three_eighths_unconditional
#print axioms MNF.Bridge78.riemannHypothesis_iff_gap_unconditional
#print axioms MNF.Bridge78.riemannHypothesis_iff_remaining_strip_unconditional
#print axioms MNF.Bridge78.zetaZeros_satisfies_structural_inputs_unconditional
#print axioms MNF.Bridge78.euler_type_no_go_unconditional

-- ═══════════════════════════════════════════════════════
-- STATEMENTS  (printed for the report; compared with expected_statements.txt)
-- ═══════════════════════════════════════════════════════
#check MNF.Bridge78.zeroFree_seven_eighths
#check MNF.Bridge78.nontrivial_zero_re_mem_unconditional
#check MNF.Bridge78.shifted_bounded_three_eighths_unconditional
#check MNF.Bridge78.riemannHypothesis_iff_gap_unconditional
#check MNF.Bridge78.riemannHypothesis_iff_remaining_strip_unconditional
#check MNF.Bridge78.zetaZeros_satisfies_structural_inputs_unconditional
#check MNF.Bridge78.euler_type_no_go_unconditional
