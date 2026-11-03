/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — UNCONDITIONAL LAYER  (MNF/RH/Unconditional.lean)
The θ = 7/8 instances, with the zero-free region discharged from OpenAI's
result `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`.
═══════════════════════════════════════════════════════════════════════
Lean:    leanprover/lean4:v4.34.1
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612   (the pin of openai/math)
Compiles ONLY inside the `lean/` tree of github.com/openai/math at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, after that tree has been built.

REGISTER: [WRAPPER].  No mathematics happens here; every proof is one
application of a theorem of MNF/RH/Gap.lean or Hypotheses.lean to

    zeroFree_seven_eighths : ZeroFreeRightOf (7/8)

These statements are exactly as reliable as OpenAI's theorem: cite them as
proved only together with a Comparator PASS for that theorem at that commit.
-/
import MNF.RH.Hypotheses
import OAI.NumberTheory.DirichletL.Nonvanishing

namespace MNF.RH

theorem zeroFree_seven_eighths : ZeroFreeRightOf (7/8) :=
  fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

theorem nontrivial_zero_re_le_seven_eighths {ρ : ℂ} (hρ : is_nontrivial_zero ρ) : ρ.re ≤ 7/8 :=
  re_le_of_zeroFree zeroFree_seven_eighths hρ

theorem shifted_bounded_three_eighths {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : |x| ≤ 3/8 := by
  have := shifted_bounded_of_zeroFree zeroFree_seven_eighths hx
  norm_num at this ⊢
  exact this

/-- RH ⟺ the MNF gap at any `Δ > 3/8`. -/
theorem riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3/8 < Δ) :
    RiemannHypothesis ↔ SpectralGapHyp Δ :=
  riemannHypothesis_iff_gap_of_zeroFree zeroFree_seven_eighths (by norm_num; exact hΔ)

/-- What is left of RH: no zeros with `1/2 < Re s ≤ 7/8`. -/
theorem riemannHypothesis_iff_remaining_strip_seven_eighths :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 7/8 → riemannZeta s ≠ 0 :=
  riemannHypothesis_iff_remaining_strip zeroFree_seven_eighths

theorem rh_of_gap_three_eighths {Δ : ℝ} (hΔ : 3/8 < Δ) (h : SpectralGapHyp Δ) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_gap_three_eighths hΔ).2 h

end MNF.RH

#print axioms MNF.RH.zeroFree_seven_eighths
#print axioms MNF.RH.shifted_bounded_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_gap_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths
#print axioms MNF.RH.rh_of_gap_three_eighths
