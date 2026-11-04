/-
FDT2.lean — node FDT2 of the Bohr–Landau closure (2026-11-03).

The first-derivative test (Titchmarsh Lemmas 4.2 / 4.3) in the SMOOTH form needed by the
downstream nodes: the phase F is twice differentiable on [a, b] with F'' ≥ 0 and F' ≥ λ > 0,
and the amplitude G ≥ 0 is differentiable with G' ≤ 0.

Route (integration by parts).  With w := G / F' (real, nonnegative, nonincreasing because
w' = (G' F' − G F'')/F'^2 ≤ 0),

    I · ∫ₐᵇ G e^{iF} = ∫ₐᵇ w · (e^{iF})' = [w e^{iF}]ₐᵇ − ∫ₐᵇ w' e^{iF},

so ‖∫ₐᵇ G e^{iF}‖ ≤ w(b) + w(a) + ∫ₐᵇ |w'| = w(b) + w(a) + (w(a) − w(b)) = 2 w(a) ≤ 2 G(a)/λ,
which is ≤ 4 G(a)/λ.  (The plain version is the amplitude version with G ≡ 1.)

Hypotheses beyond the external-prover statement: `hcont : ContinuousOn F'' (Icc a b)` and
`hGc : ContinuousOn G' (Icc a b)` (used only to make w' interval-integrable).  No sorries.
-/
import Mathlib

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace BLClosure

/-- **First-derivative test with a nonnegative nonincreasing amplitude** (Titchmarsh Lemma 4.3),
smooth form: if on `[a, b]` the phase `F` has `F' ≥ lam > 0` and `F'' ≥ 0`, and the amplitude
`G ≥ 0` has `G' ≤ 0`, then `‖∫ₐᵇ G(x) e^{i F(x)} dx‖ ≤ 4 G(a) / lam`. -/
theorem first_derivative_test_amp_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x) (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b))
    (G G' : ℝ → ℝ) (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Set.Icc a b, G' x ≤ 0) (hG0 : ∀ x ∈ Set.Icc a b, 0 ≤ G x)
    (hGc : ContinuousOn G' (Set.Icc a b)) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hF'pos : ∀ x ∈ Icc a b, 0 < F' x := fun x hx => lt_of_lt_of_le hlam (hlow x hx)
  have hF'ne : ∀ x ∈ Icc a b, F' x ≠ 0 := fun x hx => (hF'pos x hx).ne'
  -- the real weight w = G / F' and its derivative w'
  set w : ℝ → ℝ := fun x => G x / F' x with hw_def
  set w' : ℝ → ℝ := fun x => (G' x * F' x - G x * F'' x) / F' x ^ 2 with hw'_def
  have hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x := fun x hx =>
    (hG x hx).div (hF' x hx) (hF'ne x hx)
  have hw'nonpos : ∀ x ∈ Icc a b, w' x ≤ 0 := by
    intro x hx
    simp only [hw'_def]
    apply div_nonpos_of_nonpos_of_nonneg
    · have h1 : G' x * F' x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hG' x hx) (hF'pos x hx).le
      have h2 : 0 ≤ G x * F'' x := mul_nonneg (hG0 x hx) (hconv x hx)
      linarith
    · positivity
  have hwnonneg : ∀ x ∈ Icc a b, 0 ≤ w x := fun x hx =>
    div_nonneg (hG0 x hx) (hF'pos x hx).le
  -- continuity facts
  have hFc : ContinuousOn F (Icc a b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' (Icc a b) := fun x hx =>
    (hF' x hx).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (Icc a b) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have hw'c : ContinuousOn w' (Icc a b) := by
    simp only [hw'_def]
    exact ((hGc.mul hF'c).sub (hGcont.mul hcont)).div (hF'c.pow 2)
      (fun x hx => pow_ne_zero 2 (hF'ne x hx))
  -- complex versions for integration by parts
  set u : ℝ → ℂ := fun x => ((w x : ℝ) : ℂ) with hu_def
  set u' : ℝ → ℂ := fun x => ((w' x : ℝ) : ℂ) with hu'_def
  set v : ℝ → ℂ := fun x => Complex.exp (Complex.I * (F x : ℂ)) with hv_def
  set v' : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (F x : ℂ)) * (Complex.I * (F' x : ℂ)) with hv'_def
  have hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    rw [hI] at hx
    exact (hw x hx).ofReal_comp
  have hv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x := by
    intro x hx
    rw [hI] at hx
    exact ((hF x hx).ofReal_comp.const_mul Complex.I).cexp
  have hu'int : IntervalIntegrable u' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hI]
    exact Complex.continuous_ofReal.comp_continuousOn hw'c
  have hv'int : IntervalIntegrable v' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hI]
    have h1 : ContinuousOn (fun x : ℝ => Complex.I * (F x : ℂ)) (Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hFc)
    have h2 : ContinuousOn (fun x : ℝ => Complex.I * (F' x : ℂ)) (Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF'c)
    exact h1.cexp.mul h2
  -- integration by parts
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  -- the left side of IBP is I times the integral we want
  have hkey : ∫ x in a..b, u x * v' x
      = Complex.I * ∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hI] at hx
    have hne : (F' x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hF'ne x hx)
    simp only [hu_def, hv'_def, hw_def]
    push_cast
    field_simp
  have hnorm_eq : ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖
      = ‖∫ x in a..b, u x * v' x‖ := by
    rw [hkey, norm_mul, Complex.norm_I, one_mul]
  rw [hnorm_eq, hibp]
  -- norms of the pieces
  have hvnorm : ∀ x, ‖v x‖ = 1 := fun x => Complex.norm_exp_I_mul_ofReal (F x)
  have hunorm : ∀ x ∈ Icc a b, ‖u x‖ = w x := by
    intro x hx
    simp only [hu_def, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hwnonneg x hx)
  have hu'norm : ∀ x ∈ Icc a b, ‖u' x * v x‖ = -(w' x) := by
    intro x hx
    rw [norm_mul, hvnorm, mul_one]
    simp only [hu'_def, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonpos (hw'nonpos x hx)
  -- ∫ ‖u' v‖ = w a − w b by the fundamental theorem of calculus
  have hint_norm : ∫ x in a..b, ‖u' x * v x‖ = w a - w b := by
    have h1 : ∫ x in a..b, ‖u' x * v x‖ = ∫ x in a..b, -(w' x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [hI] at hx
      exact hu'norm x hx
    have h2 : ∫ x in a..b, w' x = w b - w a := by
      apply integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [hI] at hx
        exact hw x hx
      · exact hw'c.intervalIntegrable_of_Icc hab
    rw [h1, intervalIntegral.integral_neg, h2]
    ring
  have hbound : ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖ ≤ w b + w a + (w a - w b) := by
    calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
        ≤ ‖u b * v b - u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ := norm_sub_le _ _
      _ ≤ (‖u b * v b‖ + ‖u a * v a‖) + ‖∫ x in a..b, u' x * v x‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (w b + w a) + ∫ x in a..b, ‖u' x * v x‖ := by
          apply add_le_add
          · apply add_le_add
            · rw [norm_mul, hvnorm, mul_one, hunorm b hb]
            · rw [norm_mul, hvnorm, mul_one, hunorm a ha]
          · exact intervalIntegral.norm_integral_le_integral_norm hab
      _ = w b + w a + (w a - w b) := by rw [hint_norm]
  have hwa : w a ≤ G a / lam := by
    simp only [hw_def]
    exact div_le_div_of_nonneg_left (hG0 a ha) hlam (hlow a ha)
  have hGa : 0 ≤ G a / lam := div_nonneg (hG0 a ha) hlam.le
  calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
      ≤ w b + w a + (w a - w b) := hbound
    _ = 2 * w a := by ring
    _ ≤ 2 * (G a / lam) := by linarith
    _ ≤ 4 * G a / lam := by rw [mul_div_assoc]; linarith

/-- **First-derivative test** (Titchmarsh Lemma 4.2), smooth form: if on `[a, b]` the phase
`F` has `F' ≥ lam > 0` and `F'' ≥ 0`, then `‖∫ₐᵇ e^{i F(x)} dx‖ ≤ 4 / lam`. -/
theorem first_derivative_test_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x) (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b)) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 / lam := by
  have h := first_derivative_test_amp_smooth hab hlam F F' F'' hF hF' hconv hlow hcont
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun x _ => hasDerivAt_const x (1 : ℝ))
    (fun _ _ => le_rfl) (fun _ _ => zero_le_one) continuousOn_const
  simpa using h

end BLClosure
