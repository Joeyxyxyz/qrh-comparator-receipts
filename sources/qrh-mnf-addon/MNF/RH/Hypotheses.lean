/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — NAMED HYPOTHESES  (MNF/RH/Hypotheses.lean)
Every assumption the corpus ever took as an `axiom` about ζ, restated as a
named `Prop` and used only as an explicit argument.  This file adds no
axiom to Lean: `#print axioms` of every theorem below lists only
propext, Classical.choice, Quot.sound.
═══════════════════════════════════════════════════════════════════════

Register of each hypothesis (what a reader should believe about it):

  SpectralGapHyp Δ        [OPEN]        the MNF gap at threshold Δ.  By Gap.lean it is
                                        RH itself for Δ ≥ 1/2 (or Δ > 3/8 with the 7/8
                                        region) and insufficient below that.
  AllZerosSimple          [OPEN]        conjectured; no known proof.
  SpeiserTheorem          [LITERATURE]  Speiser 1934: RH ⟺ ζ' ≠ 0 on 0 < Re s < 1/2.
                                        Not in Mathlib.  Was `axiom speiser_theorem` in
                                        output45/output83.
  DoubleZeroForcesLeftDerivZero
                          [UNSUPPORTED] was `axiom argument_principle_double_zero_forces_
                                        left_strip_zero` in output83.  Not a theorem of the
                                        literature; kept only so the corpus's output83
                                        argument can be stated with its assumptions visible.
  (Hilbert–Pólya)         [OPEN]        the corpus's HPContext / "operator realization": a
                                        symmetric operator whose eigenvalues are (ρ − 1/2)/i.
                                        Not a definition here; `rh_of_symmetric_operator`
                                        takes the operator as an explicit argument and shows
                                        the implication to RH is immediate (symmetric
                                        operators have real eigenvalues).  All content of
                                        that route is in constructing the operator.

What is NOT here, and why: output86's `axiom func_eq_deriv` (ζ'(1-s) = -F(s)ζ'(s) for
all s in the strip) is false as stated and is replaced by the proved `deriv_reflect`
(Core.lean), which holds at zeros.  output86's `rh_and_speiser_implies_simple` had a
`sorry`: Speiser's theorem concerns ζ' off the line and says nothing about the
multiplicity of zeros on it, so RH ∧ Speiser → AllZerosSimple is not a theorem.
-/
import MNF.RH.Gap
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MNF.RH

open Complex

/-! ### The hypotheses -/

def SpectralGapHyp (Δ : ℝ) : Prop := SpectralGapProperty ShiftedZeroSpectrum Δ

def LeftCriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1/2}

/-- Speiser (1934). -/
def SpeiserTheorem : Prop := RiemannHypothesis ↔ ∀ s ∈ LeftCriticalStrip, deriv riemannZeta s ≠ 0

/-- output83's extra assumption: a multiple nontrivial zero forces a zero of `ζ'` in the
left half of the strip. -/
def DoubleZeroForcesLeftDerivZero : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ∃ s ∈ LeftCriticalStrip, deriv riemannZeta s = 0

def MultiplicityBoundOne : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ ≤ 1

/-! ### Conditional theorems -/

/-- Gap at Δ ≥ 1/2 ⟹ RH (no other hypothesis). -/
theorem rh_of_gap {Δ : ℝ} (hΔ : 1/2 ≤ Δ) (h : SpectralGapHyp Δ) : RiemannHypothesis :=
  (riemannHypothesis_iff_gap_half hΔ).2 h

/-- Gap at Δ > θ − 1/2 ⟹ RH, given a zero-free region right of θ. -/
theorem rh_of_gap_of_zeroFree {θ Δ : ℝ} (hθ : ZeroFreeRightOf θ) (hΔ : θ - 1/2 < Δ)
    (h : SpectralGapHyp Δ) : RiemannHypothesis :=
  (riemannHypothesis_iff_gap_of_zeroFree hθ hΔ).2 h

/-- RH ⟹ gap at every Δ (the converse direction; shows the gap hypothesis is never
stronger than RH). -/
theorem gap_of_rh (h : RiemannHypothesis) (Δ : ℝ) : SpectralGapHyp Δ :=
  gap_of_subset_zero (riemannHypothesis_iff_shifted_subset_zero.1 h) Δ

theorem multiplicityBoundOne_iff_allZerosSimple : MultiplicityBoundOne ↔ AllZerosSimple :=
  ⟨fun h ρ hρ => le_antisymm (h ρ hρ) (zeta_order_ge_one hρ),
   fun h ρ hρ => (h ρ hρ).le⟩

/-- `ζ'` nonvanishing at zeros need only be checked on the left half of the strip
(and the line): symmetry (`deriv_reflect`) supplies the right half. -/
theorem derivativeNonvanishing_of_left
    (h : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re ≤ 1/2 → deriv riemannZeta ρ ≠ 0) :
    DerivativeNonvanishing := by
  intro ρ hρ
  by_cases hre : ρ.re ≤ 1/2
  · exact h ρ hρ hre
  · have hr := nontrivial_zero_reflect hρ
    have := h (1 - ρ) hr (by rw [re_one_sub]; linarith)
    exact (deriv_ne_zero_reflect_iff hρ).1 this

/-- The output83 argument with its assumptions visible:
RH + Speiser + "double zero forces a left-strip zero of ζ'" ⟹ all zeros simple. -/
theorem allZerosSimple_of_speiser_and_double_zero_hyp (hRH : RiemannHypothesis)
    (hSp : SpeiserTheorem) (hDZ : DoubleZeroForcesLeftDerivZero) : AllZerosSimple := by
  intro ρ hρ
  by_contra hne
  have h2 : 2 ≤ zeta_order ρ := by
    have := zeta_order_ge_one hρ; omega
  obtain ⟨s, hs, hs0⟩ := hDZ ρ hρ h2
  exact (hSp.1 hRH) s hs hs0

/-- Under Speiser's theorem, RH is equivalent to `ζ' ≠ 0` on the left strip; combined with
`derivativeNonvanishing_of_left`, RH + "ζ' ≠ 0 at zeros on the line" ⟹ all zeros simple.
(The second condition is AllZerosSimple itself under RH, so this is a restatement, recorded
to show that Speiser contributes nothing to simplicity.) -/
theorem allZerosSimple_of_rh_of_line (hRH : RiemannHypothesis)
    (hline : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re = 1/2 → deriv riemannZeta ρ ≠ 0) :
    AllZerosSimple := by
  rw [allZerosSimple_iff_derivativeNonvanishing]
  intro ρ hρ
  exact hline ρ hρ (riemannHypothesis_iff_strip.1 hRH ρ hρ)

/-- **The Hilbert–Pólya step, made exact.**  If some symmetric operator `T` on a complex inner
product space has `(ρ - 1/2) / i` among its eigenvalues for every nontrivial zero `ρ`, then RH
holds: eigenvalues of a symmetric operator are real, and `(ρ - 1/2) / i` is real iff
`Re ρ = 1/2`.  This is the whole of the implication; the operator is the open part. -/
theorem rh_of_symmetric_operator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ℂ, is_nontrivial_zero ρ → Module.End.HasEigenvalue T ((ρ - 1/2) / Complex.I)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_strip]
  intro ρ hρ
  have h := hT.conj_eigenvalue_eq_self (hspec ρ hρ)
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  have h0 : ((ρ - 1/2) / Complex.I).im = 0 := by linarith
  rw [Complex.div_I] at h0
  simp at h0
  linarith

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.rh_of_symmetric_operator
#print axioms MNF.RH.rh_of_gap
#print axioms MNF.RH.rh_of_gap_of_zeroFree
#print axioms MNF.RH.gap_of_rh
#print axioms MNF.RH.multiplicityBoundOne_iff_allZerosSimple
#print axioms MNF.RH.derivativeNonvanishing_of_left
#print axioms MNF.RH.allZerosSimple_of_speiser_and_double_zero_hyp
#print axioms MNF.RH.allZerosSimple_of_rh_of_line
