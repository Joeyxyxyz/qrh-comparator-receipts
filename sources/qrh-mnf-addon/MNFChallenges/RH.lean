/-
MNF × RIEMANN ZETA — COMPARATOR CHALLENGE  (MNFChallenges/RH.lean)
The statements of the MNF.RH library with every proof replaced by `sorry`, and the
definitions they refer to, copied verbatim from MNF/RH/*.lean by gen_challenge.py.
Comparator builds this file and the solution (MNF.RH.Unconditional), exports both, and
checks that every definition and every theorem statement agrees, and that the solution's
proofs use no axiom beyond propext, Quot.sound, Classical.choice.
-/
import Mathlib

namespace MNF.RH

open Complex Filter Topology
open scoped Real

def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def ZetaZeros : Set ℂ := {ρ | is_nontrivial_zero ρ}

noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

def ShiftedZeroSpectrum : Set ℝ := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}

def AllZerosSimple : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ = 1

def DerivativeNonvanishing : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → deriv riemannZeta ρ ≠ 0

noncomputable def feFactor (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2)

def SpectralGapProperty (S : Set ℝ) (Δ : ℝ) : Prop := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ

def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def Counter : Set ℂ := {ρ | (ρ.re = 1/4 ∨ ρ.re = 3/4) ∧ (ρ.im = 1 ∨ ρ.im = -1)}

def signGate (S : Set ℝ) : Set ℝ := {x ∈ S | -x ∉ S} ∪ {0}

noncomputable def nullify (Δ x : ℝ) : ℝ := if Δ ≤ |x| then x else 0

def SpectralGapHyp (Δ : ℝ) : Prop := SpectralGapProperty ShiftedZeroSpectrum Δ

def LeftCriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1/2}

def SpeiserTheorem : Prop := RiemannHypothesis ↔ ∀ s ∈ LeftCriticalStrip, deriv riemannZeta s ≠ 0

def DoubleZeroForcesLeftDerivZero : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ∃ s ∈ LeftCriticalStrip, deriv riemannZeta s = 0

def MultiplicityBoundOne : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ ≤ 1

theorem zeta_order_ge_one {ρ : ℂ} (h : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ := by
  sorry

theorem order_one_iff_deriv {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    zeta_order ρ = 1 ↔ deriv riemannZeta ρ ≠ 0 := by
  sorry

theorem deriv_zero_of_high_order {ρ : ℂ} (h : is_nontrivial_zero ρ) (h2 : 2 ≤ zeta_order ρ) :
    deriv riemannZeta ρ = 0 := by
  sorry

theorem allZerosSimple_iff_derivativeNonvanishing : AllZerosSimple ↔ DerivativeNonvanishing :=
  sorry

theorem nontrivial_zero_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) : is_nontrivial_zero (1 - ρ) := by
  sorry

theorem deriv_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    deriv riemannZeta (1 - ρ) = -(feFactor ρ * deriv riemannZeta ρ) := by
  sorry

theorem deriv_ne_zero_reflect_iff {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    deriv riemannZeta (1 - ρ) ≠ 0 ↔ deriv riemannZeta ρ ≠ 0 := by
  sorry

theorem analyticOrderAt_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
  sorry

theorem zeta_order_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    zeta_order (1 - ρ) = zeta_order ρ := by
  sorry

theorem shifted_symmetric {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : -x ∈ ShiftedZeroSpectrum := by
  sorry

theorem in_strip_of_zero {s : ℂ} (hs : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1))
    (h1 : s ≠ 1) : 0 < s.re ∧ s.re < 1 := by
  sorry

theorem riemannHypothesis_iff_strip :
    RiemannHypothesis ↔ ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re = 1/2 := by
  sorry

theorem riemannHypothesis_iff_shifted_subset_zero :
    RiemannHypothesis ↔ ShiftedZeroSpectrum ⊆ {0} := by
  sorry

theorem shifted_bounded {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : |x| < 1/2 := by
  sorry

theorem tau_threshold {S : Set ℝ} {Δ : ℝ} (hgap : SpectralGapProperty S Δ)
    (hbound : ∀ x ∈ S, |x| < Δ) : S ⊆ {0} := by
  sorry

theorem riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1/2 ≤ Δ) :
    RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ := by
  sorry

theorem shifted_bounded_of_zeroFree {θ : ℝ} (h : ZeroFreeRightOf θ) {x : ℝ}
    (hx : x ∈ ShiftedZeroSpectrum) : |x| ≤ θ - 1/2 := by
  sorry

theorem riemannHypothesis_iff_gap_of_zeroFree {θ Δ : ℝ} (h : ZeroFreeRightOf θ)
    (hΔ : θ - 1/2 < Δ) : RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ := by
  sorry

theorem riemannHypothesis_iff_remaining_strip {θ : ℝ} (h : ZeroFreeRightOf θ) :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ θ → riemannZeta s ≠ 0 := by
  sorry

theorem gap_below_bound_insufficient {b Δ : ℝ} (hΔ : 0 < Δ) (hb : Δ < b) :
    ∃ S : Set ℝ, S ⊆ Set.Ioo (-b) b ∧ (∀ x ∈ S, -x ∈ S) ∧ SpectralGapProperty S Δ ∧ S ≠ {0} := by
  sorry

theorem symmetric_bounded_not_on_line :
    ¬ ∀ Z : Set ℂ, (∀ ρ ∈ Z, (1 - ρ) ∈ Z) → (∀ ρ ∈ Z, ρ.re ≤ 7/8) → ∀ ρ ∈ Z, ρ.re = 1/2 :=
  sorry

theorem sign_gate_trivial {S : Set ℝ} (hS : ∀ x ∈ S, -x ∈ S) : signGate S = {0} := by
  sorry

theorem sign_gate_shifted : signGate ShiftedZeroSpectrum = {0} :=
  sorry

theorem nullify_dilation {l : ℝ} (hl : 0 < l) (Δ x : ℝ) :
    nullify (l * Δ) (l * x) = l * nullify Δ x := by
  sorry

theorem gap_iff_nullify_id (S : Set ℝ) (Δ : ℝ) :
    SpectralGapProperty S Δ ↔ ∀ x ∈ S, nullify Δ x = x := by
  sorry

theorem delta_from_ratio_38_insufficient :
    (1/2 : ℝ) * (3/8) = 3/16 ∧
    ∃ S : Set ℝ, S ⊆ Set.Ioo (-(3/8)) (3/8) ∧ (∀ x ∈ S, -x ∈ S) ∧
      SpectralGapProperty S (3/16) ∧ S ≠ {0} :=
  sorry

theorem rh_of_gap {Δ : ℝ} (hΔ : 1/2 ≤ Δ) (h : SpectralGapHyp Δ) : RiemannHypothesis :=
  sorry

theorem rh_of_gap_of_zeroFree {θ Δ : ℝ} (hθ : ZeroFreeRightOf θ) (hΔ : θ - 1/2 < Δ)
    (h : SpectralGapHyp Δ) : RiemannHypothesis :=
  sorry

theorem gap_of_rh (h : RiemannHypothesis) (Δ : ℝ) : SpectralGapHyp Δ :=
  sorry

theorem multiplicityBoundOne_iff_allZerosSimple : MultiplicityBoundOne ↔ AllZerosSimple :=
  sorry

theorem derivativeNonvanishing_of_left
    (h : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re ≤ 1/2 → deriv riemannZeta ρ ≠ 0) :
    DerivativeNonvanishing := by
  sorry

theorem allZerosSimple_of_speiser_and_double_zero_hyp (hRH : RiemannHypothesis)
    (hSp : SpeiserTheorem) (hDZ : DoubleZeroForcesLeftDerivZero) : AllZerosSimple := by
  sorry

theorem allZerosSimple_of_rh_of_line (hRH : RiemannHypothesis)
    (hline : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re = 1/2 → deriv riemannZeta ρ ≠ 0) :
    AllZerosSimple := by
  sorry

theorem rh_of_symmetric_operator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ℂ, is_nontrivial_zero ρ → Module.End.HasEigenvalue T ((ρ - 1/2) / Complex.I)) :
    RiemannHypothesis := by
  sorry

theorem zeroFree_seven_eighths : ZeroFreeRightOf (7/8) :=
  sorry

theorem nontrivial_zero_re_le_seven_eighths {ρ : ℂ} (hρ : is_nontrivial_zero ρ) : ρ.re ≤ 7/8 :=
  sorry

theorem shifted_bounded_three_eighths {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : |x| ≤ 3/8 := by
  sorry

theorem riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3/8 < Δ) :
    RiemannHypothesis ↔ SpectralGapHyp Δ :=
  sorry

theorem riemannHypothesis_iff_remaining_strip_seven_eighths :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 7/8 → riemannZeta s ≠ 0 :=
  sorry

theorem rh_of_gap_three_eighths {Δ : ℝ} (hΔ : 3/8 < Δ) (h : SpectralGapHyp Δ) :
    RiemannHypothesis :=
  sorry

end MNF.RH
