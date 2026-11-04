/-
FDT1.lean — node FDT1 of the Bohr–Landau closure (2026-11-03).

The first-derivative test (Titchmarsh Lemmas 4.2 / 4.3) in the SMOOTH form: the phase F is
twice differentiable on [a, b] with F'' ≥ 0 and F' ≥ λ > 0, the amplitude G is differentiable,
nonnegative and nonincreasing (G' ≤ 0).  Proof by integration by parts, exactly as prescribed:

  G e^{iF} = u · v'   with  u = −i · (G/F'),  v = e^{iF},  v' = i F' e^{iF},
  ∫ₐᵇ u v' = [u v]ₐᵇ − ∫ₐᵇ u' v,
  ‖u' v‖ = |(G/F')'| = −(G/F')'   (G/F' is nonincreasing since G' ≤ 0, G ≥ 0, F'' ≥ 0, F' > 0),
  so ∫ₐᵇ ‖u' v‖ = G(a)/F'(a) − G(b)/F'(b),

and the total is ≤ G(b)/F'(b) + G(a)/F'(a) + G(a)/F'(a) − G(b)/F'(b) = 2 G(a)/F'(a) ≤ 2 G(a)/λ
≤ 4 G(a)/λ.  The constant 4 of the contract is kept (we actually get 2).

Hypotheses added relative to the contract's A / A′ (which assumed only F' monotone and G
antitone): F' is itself differentiable with derivative F'' ≥ 0 continuous on [a, b]; G is
differentiable with derivative G' ≤ 0 continuous on [a, b].  Both hold for the downstream
application F(u) = 2πνu − t·log u, G(u) = u^{−σ−2} on [x, X] with x ≥ 1.
-/
import Mathlib

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace BLClosure

/-- A′ (smooth form).  `‖∫ₐᵇ G(x) e^{iF(x)} dx‖ ≤ 4 G(a)/λ` for F twice differentiable with
`F'' ≥ 0`, `F' ≥ λ > 0`, and `G ≥ 0` differentiable with `G' ≤ 0`, all on `[a, b]`. -/
theorem first_derivative_test_amp_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' G G' : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x)
    (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b))
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Set.Icc a b, G' x ≤ 0)
    (hG0 : ∀ x ∈ Set.Icc a b, 0 ≤ G x)
    (hGc : ContinuousOn G' (Set.Icc a b)) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hFpos : ∀ x ∈ Set.Icc a b, 0 < F' x := fun x hx => lt_of_lt_of_le hlam (hlow x hx)
  have hFne : ∀ x ∈ Set.Icc a b, F' x ≠ 0 := fun x hx => (hFpos x hx).ne'
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- continuity facts
  have hFc : ContinuousOn F' (Set.Icc a b) := fun x hx =>
    (hF' x hx).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (Set.Icc a b) := fun x hx =>
    (hG x hx).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn F (Set.Icc a b) := fun x hx =>
    (hF x hx).continuousAt.continuousWithinAt
  -- h = G / F' and its derivative h'
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ → ℝ, h = fun x => G x / F' x := ⟨_, rfl⟩
  obtain ⟨h', hh'_def⟩ : ∃ h' : ℝ → ℝ,
      h' = fun x => (G' x * F' x - G x * F'' x) / (F' x) ^ 2 := ⟨_, rfl⟩
  have hh : ∀ x ∈ Set.Icc a b, HasDerivAt h (h' x) x := by
    intro x hx
    rw [hh_def, hh'_def]
    exact (hG x hx).div (hF' x hx) (hFne x hx)
  have hh'c : ContinuousOn h' (Set.Icc a b) := by
    rw [hh'_def]
    apply ContinuousOn.div
    · exact (hGc.mul hFc).sub (hGcont.mul hcont)
    · exact hFc.pow 2
    · intro x hx; exact pow_ne_zero 2 (hFne x hx)
  have hh'le : ∀ x ∈ Set.Icc a b, h' x ≤ 0 := by
    intro x hx
    rw [hh'_def]
    apply div_nonpos_of_nonpos_of_nonneg
    · have h1 : G' x * F' x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hG' x hx) (hFpos x hx).le
      have h2 : 0 ≤ G x * F'' x := mul_nonneg (hG0 x hx) (hconv x hx)
      linarith
    · positivity
  have hhnn : ∀ x ∈ Set.Icc a b, 0 ≤ h x := by
    intro x hx
    rw [hh_def]
    exact div_nonneg (hG0 x hx) (hFpos x hx).le
  -- u = -I * h, v = exp (I F)
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ → ℂ, u = fun x => -Complex.I * (h x : ℂ) := ⟨_, rfl⟩
  obtain ⟨u', hu'_def⟩ : ∃ u' : ℝ → ℂ, u' = fun x => -Complex.I * (h' x : ℂ) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v : ℝ → ℂ, v = fun x => Complex.exp (Complex.I * (F x : ℂ)) :=
    ⟨_, rfl⟩
  obtain ⟨v', hv'_def⟩ : ∃ v' : ℝ → ℂ,
      v' = fun x => Complex.I * (F' x : ℂ) * Complex.exp (Complex.I * (F x : ℂ)) := ⟨_, rfl⟩
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    rw [huIcc] at hx
    rw [hu_def, hu'_def]
    exact ((hh x hx).ofReal_comp).const_mul (-Complex.I)
  have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x := by
    intro x hx
    rw [huIcc] at hx
    rw [hv_def, hv'_def]
    have h1 : HasDerivAt (fun y : ℝ => Complex.I * (F y : ℂ)) (Complex.I * (F' x : ℂ)) x :=
      ((hF x hx).ofReal_comp).const_mul Complex.I
    have h2 := h1.cexp
    convert h2 using 1
    ring
  have hu'int : IntervalIntegrable u' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc, hu'_def]
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hh'c)
  have hv'int : IntervalIntegrable v' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc, hv'_def]
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hFc)).mul
      (Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hFcont)))
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  -- the integrand is u * v'
  have hint_eq : ∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))
      = ∫ x in a..b, u x * v' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [huIcc] at hx
    simp only [hu_def, hv'_def, hh_def]
    have hne : (F' x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hFne x hx)
    have e1 : -Complex.I * ((G x : ℂ) / (F' x : ℂ))
        * (Complex.I * (F' x : ℂ) * Complex.exp (Complex.I * (F x : ℂ)))
        = (-(Complex.I * Complex.I)) * ((F' x : ℂ) / (F' x : ℂ))
          * ((G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))) := by ring
    rw [Complex.ofReal_div, e1, Complex.I_mul_I, div_self hne]
    ring
  -- norms of the boundary terms
  have hexp1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (F x : ℂ))‖ = 1 := by
    intro x
    rw [show Complex.I * (F x : ℂ) = (F x : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I]
  have hnorm_uv : ∀ x ∈ Set.Icc a b, ‖u x * v x‖ = h x := by
    intro x hx
    rw [hu_def, hv_def]
    simp only
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hhnn x hx), hexp1, mul_one]
  -- FTC for h and the integral of ‖u' v‖
  have hftc : ∫ x in a..b, h' x = h b - h a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx; rw [huIcc] at hx; exact hh x hx
    · apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hh'c
  have hnorm_u'v : ∫ x in a..b, ‖u' x * v x‖ = h a - h b := by
    have hpt : Set.EqOn (fun x => ‖u' x * v x‖) (fun x => -h' x) (Set.uIcc a b) := by
      intro x hx
      rw [huIcc] at hx
      simp only
      rw [hu'_def, hv_def]
      simp only
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (hh'le x hx), hexp1, mul_one]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg, hftc]
    ring
  have hbound : ‖∫ x in a..b, u' x * v x‖ ≤ h a - h b := by
    calc ‖∫ x in a..b, u' x * v x‖ ≤ ∫ x in a..b, ‖u' x * v x‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = h a - h b := hnorm_u'v
  -- assemble
  rw [hint_eq, hibp]
  have hGa : 0 ≤ G a := hG0 a ha_mem
  calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
      ≤ ‖u b * v b - u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ := norm_sub_le _ _
    _ ≤ ‖u b * v b‖ + ‖u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ h b + h a + (h a - h b) := by
        rw [hnorm_uv b hb_mem, hnorm_uv a ha_mem]
        gcongr
    _ = 2 * (G a / F' a) := by rw [hh_def]; ring
    _ ≤ 2 * (G a / lam) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left hGa hlam (hlow a ha_mem)
    _ ≤ 4 * G a / lam := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_right (by norm_num)
        exact div_nonneg hGa hlam.le

/-- A (smooth form).  `‖∫ₐᵇ e^{iF(x)} dx‖ ≤ 4/λ` for F twice differentiable with `F'' ≥ 0` and
`F' ≥ λ > 0` on `[a, b]`.  Special case `G = 1` of `first_derivative_test_amp_smooth`. -/
theorem first_derivative_test_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x)
    (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b)) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 / lam := by
  have key := first_derivative_test_amp_smooth hab hlam F F' F'' (fun _ => 1) (fun _ => 0)
    hF hF' hconv hlow hcont (fun x _ => hasDerivAt_const x (1 : ℝ)) (fun x _ => le_rfl)
    (fun x _ => zero_le_one) continuousOn_const
  simpa using key

end BLClosure
