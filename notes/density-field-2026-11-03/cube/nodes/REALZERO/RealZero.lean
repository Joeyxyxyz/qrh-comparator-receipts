/-
REALZERO/RealZero.lean — ζ has no real zero in (0, 1), hence every nontrivial zero has
nonzero imaginary part.

Route: the tree's Euler–Maclaurin representation `Zeta0EqZeta` (PNT+ port,
Zeta23/FromPNTPlus/ZetaBounds.lean) with N = 1:

    ζ(s) = 1/2 − 1/(1 − s) + s · J(s),   J(s) = ∫_1^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx   (0 < Re s, s ≠ 1).

For real s = σ ∈ (0,1): |⌊x⌋ + 1/2 − x| ≤ 1/2 gives ‖J(σ)‖ ≤ (1/2)·∫_1^∞ x^{−σ−1} dx = 1/(2σ),
so ‖σ J(σ)‖ ≤ 1/2, while 1/(1−σ) − 1/2 > 1/2.  Hence ζ(σ) ≠ 0.
-/
import MNF.RH.ReservoirMass

open Complex Set MeasureTheory

namespace MNF.RH

/-- The N = 1 Euler–Maclaurin remainder of ζ on the real axis is bounded by `1/(2σ)`:
`‖∫_1^∞ (⌊x⌋ + 1/2 − x) / x^{σ+1} dx‖ ≤ 1/2/σ` for `0 < σ`. -/
lemma zeta_em_remainder_norm_le {σ : ℝ} (hσ : 0 < σ) :
    ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤ 1 / 2 / σ := by
  have hint : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
    Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (c := 1) (by linarith) one_pos) (1 / 2)
  have hval : ∫ x in Ioi (1 : ℝ), (1 / 2 : ℝ) * x ^ (-σ - 1) = 1 / 2 / σ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (a := -σ - 1) (c := 1) (by linarith) one_pos,
      Real.one_rpow, show -σ - 1 + 1 = -σ by ring, neg_div_neg_eq]
    ring
  refine le_trans (norm_integral_le_of_norm_le hint ?_) (le_of_eq hval)
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hpos : (0 : ℝ) < x ^ (σ + 1) := Real.rpow_pos_of_pos hx0 _
  have hre : ((σ : ℂ) + 1).re = σ + 1 := by simp
  have h1 : (1 / 2 : ℝ) * x ^ (-σ - 1) = 1 / 2 / x ^ (σ + 1) := by
    rw [show -σ - 1 = -(σ + 1) by ring, Real.rpow_neg hx0.le]
    ring
  rw [ZetaSum_aux1_4' x hx0 (σ : ℂ), hre, h1]
  exact div_le_div_of_nonneg_right (ZetaSum_aux1_3 x) hpos.le

/-- **ζ has no real zero in (0, 1).** -/
theorem riemannZeta_ofReal_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hre : (0 : ℝ) < (σ : ℂ).re := by simpa using h0
  have hs1 : (σ : ℂ) ≠ 1 := Complex.ofReal_ne_one.mpr h1.ne
  have hs0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  have hJ := zeta_em_remainder_norm_le h0
  rw [← Zeta0EqZeta (N := 1) one_pos hre hs1]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1) with hJdef
  intro h
  have hσJ : (σ : ℂ) * J = 1 / (1 - (σ : ℂ)) - 1 / 2 := by
    linear_combination h
  have hnorm : ‖(σ : ℂ) * J‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
    calc σ * ‖J‖ ≤ σ * (1 / 2 / σ) := mul_le_mul_of_nonneg_left hJ h0.le
      _ = 1 / 2 := by field_simp
  have hreal : (1 / (1 - (σ : ℂ)) - 1 / 2) = ((1 / (1 - σ) - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hσJ, hreal, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have h1σ : 0 < 1 - σ := by linarith
  have hgt : 1 < 1 / (1 - σ) := one_lt_one_div h1σ (by linarith)
  have := le_abs_self (1 / (1 - σ) - 1 / 2)
  linarith

/-- **Every nontrivial zero of ζ has nonzero imaginary part**: ζ has no zero on the real
segment (0, 1). -/
theorem nontrivial_zero_im_ne_zero : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.im ≠ 0 := by
  intro ρ ⟨hz, h0, h1⟩ him
  have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hρ] at hz
  exact riemannZeta_ofReal_ne_zero_of_mem_Ioo h0 h1 hz

end MNF.RH

#print axioms MNF.RH.nontrivial_zero_im_ne_zero
