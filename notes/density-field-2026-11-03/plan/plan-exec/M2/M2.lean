import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.BL.DPMV

/-!
# M2 — the tree's approximate formula specialised to vertical lines

Node M2 of `BOHR_LANDAU_PLAN.md` (§3, M2b/M2c/M2d).

For `s = σ + t*I` with `1/2 < σ₁ ≤ σ`, `t ≥ 1`, `N ≥ 1`, the tree's `Zeta0EqZeta` and the
definition of `riemannZeta0` give

  ζ(s) = S_N(s) + P + Q + R,   S_N(s) = ∑_{n < N+1} 1/n^s,
  P = -N^{1-s}/(1-s),  Q = -N^{-s}/2,  R = s ∫_N^∞ (⌊x⌋+1/2-x) x^{-s-1} dx,

and we prove the explicit bounds

  ‖P‖ ≤ N^{1-σ₁}/t,   ‖Q‖ ≤ N^{-σ₁}/2,   ‖R‖ ≤ (σ+t) N^{-σ₁}/σ₁     (M2b)
  (a+b+c+d)² ≤ 4(a²+b²+c²+d²)                                     (M2c)
  ‖ζ(s)‖² ≤ 4‖S_N(s)‖² + 4(N^{2-2σ₁}/t² + N^{-2σ₁}/4 + (σ+t)² N^{-2σ₁}/σ₁²)
  S_N(s) = ∑_{n ∈ Icc 1 N} (n^{-σ} : ℝ) · n^{-it}   (DPMV shape, needs t ≠ 0)   (M2d)
  S_N(s) = ∑_{n ∈ Icc 1 N} (n^{-σ} : ℝ) · exp(-(t log n) I)                    (M2d, exp shape)

All names from Mathlib / the tree were checked by grep; no `sorry`.
-/

set_option lang.lemmaCmd true

open Complex Set

namespace Zeta23.BL.M2

/-! ## M2c: the four-term square inequality -/

theorem norm_add4_sq_le (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
        have := norm_add₃_le (a := a) (b := b) (c := c)
        linarith
  have h0 : 0 ≤ ‖a + b + c + d‖ := norm_nonneg _
  calc ‖a + b + c + d‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
      nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
        sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-! ## Elementary facts about `s = σ + t*I` -/

lemma s_re (σ t : ℝ) : ((σ:ℂ) + t * I).re = σ := by simp

lemma s_im (σ t : ℝ) : ((σ:ℂ) + t * I).im = t := by simp

lemma one_sub_s_re (σ t : ℝ) : (1 - ((σ:ℂ) + t * I)).re = 1 - σ := by simp

lemma one_sub_s_im (σ t : ℝ) : (1 - ((σ:ℂ) + t * I)).im = -t := by simp

lemma neg_s_re (σ t : ℝ) : (-((σ:ℂ) + t * I)).re = -σ := by simp

lemma s_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ:ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma s_ne_zero {σ t : ℝ} (ht : t ≠ 0) : (σ:ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma norm_s_le {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) : ‖(σ:ℂ) + t * I‖ ≤ σ + t := by
  refine le_trans (norm_add_le _ _) ?_
  simp only [Complex.norm_of_nonneg hσ, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one, abs_of_nonneg ht]
  exact le_rfl

lemma norm_one_sub_s_ge {σ t : ℝ} (ht : 0 ≤ t) : t ≤ ‖1 - ((σ:ℂ) + t * I)‖ := by
  have := Complex.abs_im_le_norm (1 - ((σ:ℂ) + t * I))
  rw [one_sub_s_im, abs_neg, abs_of_nonneg ht] at this
  exact this

/-- `(x^a)^2 = x^b` when `b = a * 2`, for `x ≥ 0`. -/
lemma rpow_sq_eq {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (h : b = a * 2) : (x ^ a) ^ 2 = x ^ b := by
  rw [h, Real.rpow_mul hx a 2, Real.rpow_two]

/-! ## M2b: the three non-sum terms of `riemannZeta0` on the line `Re s = σ`, `t ≥ 1` -/

/-- `‖-N^{1-s}/(1-s)‖ ≤ N^{1-σ₁}/t`. -/
theorem norm_P_le {σ₁ σ t : ℝ} (hσ : σ₁ ≤ σ) (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) :
    ‖(-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I))‖ ≤ (N:ℝ) ^ (1 - σ₁) / t := by
  rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega), one_sub_s_re]
  apply div_le_div₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_ ht (norm_one_sub_s_ge ht.le)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- `‖-N^{1-s}/(1-s)‖ ≤ N^{1-σ₁}` (the `t ≥ 1` form). -/
theorem norm_P_le' {σ₁ σ t : ℝ} (hσ : σ₁ ≤ σ) (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    ‖(-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I))‖ ≤ (N:ℝ) ^ (1 - σ₁) := by
  refine le_trans (norm_P_le hσ (by linarith) hN) ?_
  rw [div_le_iff₀ (by linarith)]
  have := Real.rpow_nonneg (Nat.cast_nonneg N) (1 - σ₁)
  nlinarith

/-- `‖-N^{-s}/2‖ ≤ N^{-σ₁}/2`. -/
theorem norm_Q_le {σ₁ σ t : ℝ} (hσ : σ₁ ≤ σ) {N : ℕ} (hN : 1 ≤ N) :
    ‖(-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2‖ ≤ (N:ℝ) ^ (-σ₁) / 2 := by
  rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega), neg_s_re, Complex.norm_two]
  apply div_le_div_of_nonneg_right ?_ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- `‖-N^{-s}/2‖ ≤ 1/2` when `σ ≥ 0`. -/
theorem norm_Q_le' {σ t : ℝ} (hσ : 0 ≤ σ) {N : ℕ} (hN : 1 ≤ N) :
    ‖(-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2‖ ≤ 1 / 2 := by
  refine le_trans (norm_Q_le (σ₁ := σ) le_rfl hN) ?_
  apply div_le_div_of_nonneg_right ?_ (by norm_num)
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)

/-- The integral term, core form: `‖s ∫_N^∞ (⌊x⌋+1/2-x) x^{-s-1}‖ ≤ (σ+t) N^{-σ}/σ`
(via the tree's `ZetaBnd_aux1b : ‖∫ …‖ ≤ N^{-σ}/σ` and `‖s‖ ≤ σ + t`). -/
theorem norm_R_le_core {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    ‖((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1)‖
      ≤ (σ + t) * (N:ℝ) ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul (norm_s_le hσ.le ht) (ZetaBnd_aux1b N hN hσ) (norm_nonneg _) (by linarith)

/-- The integral term in the task's form: `≤ (σ+t) N^{-σ₁}/σ₁` for `σ ≥ σ₁ > 0`. -/
theorem norm_R_le {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 0 ≤ t) {N : ℕ} (hN : 1 ≤ N) :
    ‖((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1)‖
      ≤ (σ + t) * (N:ℝ) ^ (-σ₁) / σ₁ := by
  have hσ0 : 0 < σ := by linarith
  refine le_trans (norm_R_le_core hσ0 ht hN) ?_
  apply div_le_div₀ ?_ ?_ h1 hσ
  · exact mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · apply mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- The integral term, sharper uniform form: `≤ (1 + t/σ₁) N^{-σ₁}` for `σ ≥ σ₁ > 0`
(no upper bound on `σ` needed). -/
theorem norm_R_le_uniform {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 0 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1)‖
      ≤ (1 + t / σ₁) * (N:ℝ) ^ (-σ₁) := by
  have hσ0 : 0 < σ := by linarith
  refine le_trans (norm_R_le_core hσ0 ht hN) ?_
  have e : (σ + t) * (N:ℝ) ^ (-σ) / σ = (1 + t / σ) * (N:ℝ) ^ (-σ) := by
    field_simp
  rw [e]
  apply mul_le_mul ?_ ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
  · have : t / σ ≤ t / σ₁ := div_le_div_of_nonneg_left ht h1 hσ
    linarith
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  · have : 0 ≤ t / σ₁ := div_nonneg ht h1.le
    linarith

/-- The plan's form of the integral bound, `(1 + 1/σ₁) t N^{-σ₁}`, for `t ≥ 1`. -/
theorem norm_R_le' {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1)‖
      ≤ (1 + 1 / σ₁) * t * (N:ℝ) ^ (-σ₁) := by
  refine le_trans (norm_R_le_uniform h1 hσ (by linarith) hN) ?_
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have e : (1 + 1 / σ₁) * t = t + t / σ₁ := by ring
  rw [e]
  linarith

/-! ## M2a specialised: `ζ(s)` as the four terms of `riemannZeta0 N s` -/

/-- The tree's `Zeta0EqZeta` unfolded: on `Re s = σ > 0`, `t ≠ 0`, `N ≥ 1`,
`ζ(s) = S_N(s) + P + Q + R`. -/
theorem zeta_eq_four_terms {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta ((σ:ℂ) + t * I) =
      (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)) +
      (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) +
      (-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2 +
      ((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1) := by
  rw [← Zeta0EqZeta (N := N) (by omega) (by simp [hσ]) (s_ne_one ht)]
  rfl

/-- M2b assembled: the approximate formula with explicit error on the vertical line. -/
theorem zeta_sub_sum_le {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta ((σ:ℂ) + t * I) - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)‖
      ≤ (N:ℝ) ^ (1 - σ₁) / t + (N:ℝ) ^ (-σ₁) / 2 + (σ + t) * (N:ℝ) ^ (-σ₁) / σ₁ := by
  have ht0 : t ≠ 0 := by intro h; linarith
  rw [zeta_eq_four_terms (by linarith) ht0 hN]
  set S := ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I) with hS
  set P := (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) with hP
  set Q := (-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2 with hQ
  set R := ((σ:ℂ) + t * I) *
    ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1) with hR
  rw [show S + P + Q + R - S = P + Q + R by ring]
  refine le_trans (norm_add₃_le) ?_
  have hP' := norm_P_le hσ (by linarith : 0 < t) hN
  have hQ' := norm_Q_le (t := t) hσ hN
  have hR' := norm_R_le (t := t) h1 hσ (by linarith) hN
  linarith

/-- The pointwise square bound: for `s = σ + t*I`, `σ ≥ σ₁ > 0`, `t ≥ 1`, `N ≥ 1`,
`‖ζ(s)‖² ≤ 4‖S_N(s)‖² + 4 (N^{2-2σ₁}/t² + N^{-2σ₁}/4 + (σ+t)² N^{-2σ₁}/σ₁²)`. -/
theorem norm_zeta_sq_le {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      4 * ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)‖ ^ 2 +
      4 * ((N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 + (N:ℝ) ^ (-(2 * σ₁)) / 4
            + (σ + t) ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) / σ₁ ^ 2) := by
  have ht0 : t ≠ 0 := by intro h; linarith
  rw [zeta_eq_four_terms (by linarith) ht0 hN]
  set S := ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I) with hS
  set P := (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) with hP
  set Q := (-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2 with hQ
  set R := ((σ:ℂ) + t * I) *
    ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1) with hR
  refine le_trans (norm_add4_sq_le S P Q R) ?_
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hP2 : ‖P‖ ^ 2 ≤ (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 := by
    calc ‖P‖ ^ 2 ≤ ((N:ℝ) ^ (1 - σ₁) / t) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_P_le hσ (by linarith) hN) 2
      _ = (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 := by
          rw [div_pow, rpow_sq_eq hN0 (a := 1 - σ₁) (b := 2 - 2 * σ₁) (by ring)]
  have hQ2 : ‖Q‖ ^ 2 ≤ (N:ℝ) ^ (-(2 * σ₁)) / 4 := by
    calc ‖Q‖ ^ 2 ≤ ((N:ℝ) ^ (-σ₁) / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Q_le (t := t) hσ hN) 2
      _ = (N:ℝ) ^ (-(2 * σ₁)) / 4 := by
          rw [div_pow, rpow_sq_eq hN0 (a := -σ₁) (b := -(2 * σ₁)) (by ring)]; norm_num
  have hR2 : ‖R‖ ^ 2 ≤ (σ + t) ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) / σ₁ ^ 2 := by
    calc ‖R‖ ^ 2 ≤ ((σ + t) * (N:ℝ) ^ (-σ₁) / σ₁) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_R_le (t := t) h1 hσ (by linarith) hN) 2
      _ = (σ + t) ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) / σ₁ ^ 2 := by
          rw [div_pow, mul_pow, rpow_sq_eq hN0 (a := -σ₁) (b := -(2 * σ₁)) (by ring)]
  linarith

/-- The simpler form (drop `1/t²`, `t ≥ 1`): the shape quoted in the task statement. -/
theorem norm_zeta_sq_le' {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      4 * ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)‖ ^ 2 +
      4 * ((N:ℝ) ^ (2 - 2 * σ₁) + (N:ℝ) ^ (-(2 * σ₁)) / 4
            + (σ + t) ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) / σ₁ ^ 2) := by
  refine le_trans (norm_zeta_sq_le h1 hσ ht hN) ?_
  have hA : (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (2 - 2 * σ₁)
    exact le_mul_of_one_le_right this (by nlinarith)
  linarith

/-! ## M2d: the Dirichlet polynomial of `riemannZeta0` in the shape of `DPMV.dirichlet_mean_value` -/

/-- One term: `1/n^s = (n^{-σ} : ℝ) · n^{-it}` for `n ≥ 1`. -/
lemma one_div_cpow_eq_rpow_mul {σ t : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℂ) ^ ((σ:ℂ) + t * I) = (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I) := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [one_div, ← Complex.cpow_neg, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ hn']
  congr 1
  push_cast
  ring

/-- The `range (N+1)` sum of `riemannZeta0` equals the `Icc 1 N` Dirichlet polynomial with
coefficients `a n = n^{-σ}` and twist `n^{-it}` — exactly the shape consumed by
`DPMV.dirichlet_mean_value`. Needs `t ≠ 0` so that the `n = 0` term is `0^s = 0`. -/
theorem range_sum_eq_Icc {σ t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)
      = ∑ n ∈ Finset.Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I) := by
  rw [Finset.sum_range_succ']
  have h0 : 1 / ((0:ℕ) : ℂ) ^ ((σ:ℂ) + t * I) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow (s_ne_zero ht), div_zero]
  rw [h0, add_zero, Finset.Icc_eq_Ico, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n _
  rw [add_comm 1 n]
  exact one_div_cpow_eq_rpow_mul (by omega)

/-- The same, with the twist written as `exp(-(t log n) I)` (the plan's M1d shape). -/
theorem range_sum_eq_twist {σ t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)
      = ∑ n ∈ Finset.Icc 1 N,
          (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(t * Real.log n) * I) := by
  rw [range_sum_eq_Icc ht N]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [DPMV.cpow_neg_mul_I_eq_exp n hn0 t]
  congr 2
  push_cast
  ring

/-- Bridge to `DPMV.dirichlet_mean_value` on `[1, T]` (where `t ≠ 0` everywhere): the integrand
`‖S_N(σ+it)‖²` coincides with `‖∑ a n n^{-it}‖²` for `a n = n^{-σ}`. -/
theorem integral_range_sq_eq_Icc {σ T : ℝ} (hT : 1 ≤ T) (N : ℕ) :
    ∫ t in (1:ℝ)..T, ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)‖ ^ 2
      = ∫ t in (1:ℝ)..T,
          ‖∑ n ∈ Finset.Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT, mem_Icc] at ht
  have ht0 : t ≠ 0 := by intro h; linarith [ht.1]
  simp only
  rw [range_sum_eq_Icc ht0 N]

end Zeta23.BL.M2
