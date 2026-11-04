/-
W5.lean — STRIP_PLAN node W5: plan item W5 (`meanSquare_B_window`, Density/Window.lean).
Scratch file on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e).

Header and the DEFINITIONS block are copied verbatim from STRIP_PLAN.md §(C) (frozen; the
bodies of `Mx`, `fz`, `cm`, `dX`, `Leps`, `NSigma` are compared by Comparator and must not
change).  `open MNF.RH` is added before the block only so that `zeta_order` resolves; it does
not alter any definition body.  `norm_Mx_le` (W3, node G8W) is copied verbatim because scratch
files cannot be imported.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

open MNF.RH

namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius

/-- Möbius mollifier `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`. -/
noncomputable def Mx (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)
/-- the mollified zeta `f = ζ · M_X`. -/
noncomputable def fz (X : ℕ) (s : ℂ) : ℂ := riemannZeta s * Mx X s
/-- coefficient of `m^{-s}` in `S N · M_X`. -/
def cm (N X m : ℕ) : ℤ := ∑ d ∈ m.divisors.filter (· ≤ X), if m / d ≤ N then μ d else 0
/-- number of divisors of `m` that are `≤ X`. -/
def dX (X m : ℕ) : ℕ := (m.divisors.filter (· ≤ X)).card
/-- ε-majorant of `log ‖f‖` (replaces the tree's `Lz`, whose `1 +` kills every saving). -/
noncomputable def Leps (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ := (1 / 2) * Real.log (ε ^ 2 + ‖f z‖ ^ 2)
/-- zeros with `σ ≤ Re ρ`, `T₁ < Im ρ ≤ T₂`, with multiplicity (window form of `NRight`). -/
noncomputable def NSigma (σ T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ MNF.RH.zerosIn T₁ T₂ ∩ {ρ | σ ≤ ρ.re}, zeta_order ρ

/-! ### End of the frozen DEFINITIONS block. -/

open Zeta23.BL

/-! ## W3 (copied verbatim from node G8W) — pointwise bound for the mollifier -/

/-- `‖M_X(s)‖ ≤ 1 + X^{1-σ₁}/(1-σ₁)` for `Re s ≥ σ₁`, `1/2 < σ₁ < 1`. -/
theorem norm_Mx_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) {s : ℂ} (hs : σ₁ ≤ s.re)
    (X : ℕ) : ‖Mx X s‖ ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) := by
  unfold Mx
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Icc 1 X, ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-σ₁) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.1 hn).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, neg_re]
    have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-σ₁) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hpos : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc ‖((μ n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hμ hpos
      _ = (n : ℝ) ^ (-s.re) := one_mul _
      _ ≤ (n : ℝ) ^ (-σ₁) := hpow
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have h := M1.sum_Icc_rpow_le (N := X) (a := -σ₁) (by linarith) (by linarith)
  have e : -σ₁ + 1 = 1 - σ₁ := by ring
  rw [e] at h
  exact h

/-! ## W5 — the window mean square of `(ζ − S_N)·M_X` (`Density/Window.lean`) -/

/-- `t ↦ ‖(ζ − S_N)(σ+it)·M_X(σ+it)‖²` is continuous on `[a, b]`, `a > 0`
(the pole `s = 1` has `t = 0`). -/
lemma continuousOn_B_window (σ : ℝ) (N X : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ =>
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) (Set.Icc a b) := by
  have hline : Continuous (fun t : ℝ => (σ:ℂ) + t * I) := by fun_prop
  have hζ : ContinuousOn (fun t : ℝ => riemannZeta ((σ:ℂ) + t * I)) (Set.Icc a b) :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta (S := {z : ℂ | z ≠ 1}) (by simp)).continuousOn.comp
      hline.continuousOn (segment_mapsTo_ne_one ha)
  have hS : Continuous (fun t : ℝ => BLClosure.S N ((σ:ℂ) + t * I)) := by
    unfold BLClosure.S
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
  have hM : Continuous (fun t : ℝ => Mx X ((σ:ℂ) + t * I)) := by
    unfold Mx
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  exact ((hζ.sub hS.continuousOn).mul hM.continuousOn).norm.pow 2

/-- `∫_a^{a+ℓ} t⁻² dt ≤ 1/a` for `a > 0`, `ℓ ≥ 0` (pattern `integral_inv_sq_one`). -/
lemma integral_inv_sq_window {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) :
    ∫ t in a..(a + ℓ), (t ^ 2)⁻¹ ≤ 1 / a := by
  have hab : a ≤ a + ℓ := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a (a + ℓ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hderiv : ∀ x ∈ Set.uIcc a (a + ℓ), HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0:ℝ) < x).ne'
    have := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at this
    exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have : 0 < (a + ℓ)⁻¹ := by positivity
  rw [one_div]
  linarith

/-- **W5.** Window mean square of `(ζ − S_N)·M_X` on `Re s = σ ≥ σ₁`, `t ∈ [a, a+ℓ]`, `a ≥ 1`,
from the pointwise bound `‖M_X‖ ≤ 1 + X^{1−σ₁}/(1−σ₁)`, the main term `‖N^{1−s}/(s−1)‖ ≤
N^{1−σ₁}/t` (`M2.norm_P_le`) and the approximate-formula error `hE`. -/
theorem meanSquare_B_window {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ)
    {N X : ℕ} (hN : 1 ≤ N) {a ℓ : ℝ} (ha : 1 ≤ a) (hℓ : 0 ≤ ℓ) {C_G : ℝ} (hCG : 0 ≤ C_G)
    (hE : ∀ t ∈ Set.Icc a (a + ℓ),
      ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
        - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ)) :
    ∫ t in a..(a + ℓ), ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
  have hab : a ≤ a + ℓ := by linarith
  have ha0 : 0 < a := by linarith
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hB0 : 0 ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) := by
    have : 0 ≤ (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) (by linarith)
    linarith
  -- the pointwise bound on the window
  have hpt : ∀ t ∈ Set.Icc a (a + ℓ),
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
          * Mx X ((σ:ℂ) + t * I)‖ ^ 2
        ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hsre : σ₁ ≤ ((σ:ℂ) + t * I).re := by simpa using hσ
    have hM : ‖Mx X ((σ:ℂ) + t * I)‖ ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) :=
      norm_Mx_le h1 h1' hsre X
    have hP : ‖(N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
        ≤ (N:ℝ) ^ (1 - σ₁) / t := by
      have e : (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)
          = (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) := by
        rw [neg_div, ← div_neg, neg_sub]
      rw [e]
      exact M2.norm_P_le hσ ht0 hN
    have hR : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
        - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
        ≤ C_G * (N:ℝ) ^ (-σ₁) := by
      refine le_trans (hE t ht) (mul_le_mul_of_nonneg_left ?_ hCG)
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsplit : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
        ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := by
      calc ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
          = ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
              - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1))
              + (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
              - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
              + ‖(N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ := norm_add_le _ _
        _ ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := add_le_add hR hP
    have hζS0 : 0 ≤ ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖ :=
      norm_nonneg _
    have hM0 : 0 ≤ ‖Mx X ((σ:ℂ) + t * I)‖ := norm_nonneg _
    have hxy0 : 0 ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := by
      have := Real.rpow_nonneg hN0 (-σ₁)
      have := Real.rpow_nonneg hN0 (1 - σ₁)
      positivity
    have hprod : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
          * ‖Mx X ((σ:ℂ) + t * I)‖
        ≤ (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t)
          * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) :=
      mul_le_mul hsplit hM hM0 hxy0
    have hsq := pow_le_pow_left₀ (mul_nonneg hζS0 hM0) hprod 2
    rw [norm_mul]
    refine le_trans hsq ?_
    have e1 : ((N:ℝ) ^ (1 - σ₁) / t) ^ 2 = (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ := by
      rw [div_pow, M2.rpow_sq_eq hN0 (a := 1 - σ₁) (b := 2 - 2 * σ₁) (by ring), div_eq_mul_inv]
    have e2 : (C_G * (N:ℝ) ^ (-σ₁)) ^ 2 = C_G ^ 2 * (N:ℝ) ^ (-2 * σ₁) := by
      rw [mul_pow, M2.rpow_sq_eq hN0 (a := -σ₁) (b := -2 * σ₁) (by ring)]
    have key : (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t) ^ 2
        ≤ 2 * (((N:ℝ) ^ (1 - σ₁) / t) ^ 2 + (C_G * (N:ℝ) ^ (-σ₁)) ^ 2) := by
      nlinarith [sq_nonneg (C_G * (N:ℝ) ^ (-σ₁) - (N:ℝ) ^ (1 - σ₁) / t)]
    calc ((C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t)
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁))) ^ 2
        = (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t) ^ 2
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 := by ring
      _ ≤ 2 * (((N:ℝ) ^ (1 - σ₁) / t) ^ 2 + (C_G * (N:ℝ) ^ (-σ₁)) ^ 2)
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 :=
          mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) := by
          rw [e1, e2]; ring
  -- integrability of both sides
  have hfi : IntervalIntegrable (fun t : ℝ =>
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) :=
    (continuousOn_B_window σ N X ha0).intervalIntegrable_of_Icc hab
  have hinv : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a (a + ℓ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have h1i : IntervalIntegrable (fun t : ℝ => (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹)
      volume a (a + ℓ) := hinv.const_mul _
  have h2i : IntervalIntegrable (fun _ : ℝ => C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁))
      volume a (a + ℓ) := intervalIntegrable_const
  have hgi : IntervalIntegrable (fun t : ℝ =>
      2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)))
      volume a (a + ℓ) := (h1i.add h2i).const_mul _
  -- integrate
  calc ∫ t in a..(a + ℓ), ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
          * Mx X ((σ:ℂ) + t * I)‖ ^ 2
      ≤ ∫ t in a..(a + ℓ), 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) :=
        intervalIntegral.integral_mono_on hab hfi hgi hpt
    _ = 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) * (∫ t in a..(a + ℓ), (t ^ 2)⁻¹)
              + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1i h2i,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
          add_sub_cancel_left]
        ring
    _ ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
        have hI := integral_inv_sq_window ha0 hℓ
        have hNp : 0 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := Real.rpow_nonneg hN0 _
        have hmain : (N : ℝ) ^ (2 - 2 * σ₁) * (∫ t in a..(a + ℓ), (t ^ 2)⁻¹)
            ≤ (N : ℝ) ^ (2 - 2 * σ₁) / a := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left hI hNp
        have h2B : 0 ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h2B

end Zeta23.Density
