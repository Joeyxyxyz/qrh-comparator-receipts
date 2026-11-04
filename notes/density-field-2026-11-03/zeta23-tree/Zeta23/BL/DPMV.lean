import Mathlib

/-!
# Dirichlet-polynomial mean value (route 1: direct expansion)

For `a : ℕ → ℂ`, `N : ℕ`, `T > 0`,
  ∫_0^T ‖∑_{n=1}^N a n n^{-it}‖² dt
    ≤ T ∑ ‖a n‖² + ∑_{m≠n} ‖a m‖ ‖a n‖ · 2/|log(n/m)|.
-/

open Complex MeasureTheory intervalIntegral Finset

namespace DPMV

/-- `n^{-it}` as an exponential, for `n ≥ 1`. -/
lemma cpow_neg_mul_I_eq_exp (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n:ℂ) ^ (-(t:ℂ) * I) = Complex.exp (-(Real.log n : ℂ) * I * t) := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log]
  congr 1; ring

/-- Conjugate of `n^{-it}`. -/
lemma conj_cpow_neg_mul_I (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (starRingEnd ℂ) ((n:ℂ) ^ (-(t:ℂ) * I)) = Complex.exp ((Real.log n : ℂ) * I * t) := by
  rw [cpow_neg_mul_I_eq_exp n hn t, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `m^{-it} · conj(n^{-it}) = exp(i (log n − log m) t)`. -/
lemma prod_eq_exp (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    (m:ℂ) ^ (-(t:ℂ) * I) * (starRingEnd ℂ) ((n:ℂ) ^ (-(t:ℂ) * I)) =
      Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * I * t) := by
  rw [cpow_neg_mul_I_eq_exp m hm t, conj_cpow_neg_mul_I n hn t, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Closed form: `∫_0^T exp(i c t) dt = (exp(i c T) − 1)/(i c)` for `c ≠ 0`. -/
lemma integral_exp_I_mul (c : ℝ) (hc : c ≠ 0) (T : ℝ) :
    ∫ t in (0:ℝ)..T, Complex.exp ((c:ℂ) * I * t) =
      (Complex.exp ((c:ℂ) * I * T) - 1) / ((c:ℂ) * I) := by
  have hc' : (c:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hc) I_ne_zero
  rw [integral_exp_mul_complex hc']
  simp

/-- Degenerate case `c = 0`: the integral is `T`. -/
lemma integral_exp_I_mul_zero (T : ℝ) :
    ∫ t in (0:ℝ)..T, Complex.exp (((0:ℝ):ℂ) * I * t) = T := by
  simp

/-- `‖exp(i c T)‖ = 1`. -/
lemma norm_exp_I_mul_eq_one (c T : ℝ) : ‖Complex.exp ((c:ℂ) * I * T)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Off-diagonal bound: `‖∫_0^T exp(i c t) dt‖ ≤ 2/|c|`. -/
lemma norm_integral_exp_I_mul_le (c : ℝ) (hc : c ≠ 0) (T : ℝ) :
    ‖∫ t in (0:ℝ)..T, Complex.exp ((c:ℂ) * I * t)‖ ≤ 2 / |c| := by
  rw [integral_exp_I_mul c hc T, norm_div]
  have h1 : ‖(c:ℂ) * I‖ = |c| := by simp
  rw [h1]
  have h2 : ‖Complex.exp ((c:ℂ) * I * T) - 1‖ ≤ 2 := by
    calc ‖Complex.exp ((c:ℂ) * I * T) - 1‖
        ≤ ‖Complex.exp ((c:ℂ) * I * T)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_exp_I_mul_eq_one, norm_one]; norm_num
  gcongr


/-- The kernel integral `J T m n = ∫_0^T exp(i (log n − log m) t) dt`. -/
noncomputable def J (T : ℝ) (m n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..T, Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * I * t)

lemma J_self (T : ℝ) (n : ℕ) : J T n n = T := by
  unfold J; simp

lemma norm_J_le (T : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    ‖J T m n‖ ≤ 2 / |Real.log (n / m)| := by
  have hc : Real.log n - Real.log m ≠ 0 := by
    intro h
    apply hmn
    have h' : Real.log (m:ℝ) = Real.log (n:ℝ) := by linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hm))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hn)) h'
    exact_mod_cast this
  rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')]
  exact norm_integral_exp_I_mul_le _ hc T

/-- Termwise expansion of `‖∑ a n n^{-it}‖²` (as a complex number). -/
lemma normSq_sum_expand (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ((‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * (starRingEnd ℂ) (a n) *
        Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * I * t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro m hm
  apply Finset.sum_congr rfl; intro n hn
  have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [map_mul, ← prod_eq_exp m n hm0 hn0 t]
  ring

/-- Integrate the expansion termwise. -/
lemma integral_normSq_sum (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ((∫ t in (0:ℝ)..T, ‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * (starRingEnd ℂ) (a n) * J T m n := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [normSq_sum_expand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro n hn
      rw [intervalIntegral.integral_const_mul]
      rfl
    · intro n hn
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro m hm
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **Dirichlet-polynomial mean value**, route 1. -/
theorem dirichlet_mean_value (a : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * Complex.I)‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (n / m)|)) := by
  have hI : (∫ t in (0:ℝ)..T, ‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (a m * (starRingEnd ℂ) (a n) * J T m n).re := by
    have h2 := congrArg Complex.re (integral_normSq_sum a N T)
    rw [Complex.ofReal_re] at h2
    rw [h2]
    simp only [Complex.re_sum]
  have hterm : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      (a m * (starRingEnd ℂ) (a n) * J T m n).re ≤
        (if m = n then T * ‖a n‖ ^ 2 else 0) +
        (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (n / m)|)) := by
    intro m hm n hn
    have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
    by_cases hmn : m = n
    · subst hmn
      simp only [if_true, add_zero]
      rw [J_self, Complex.norm_of_nonneg hT.le]
      apply le_of_eq; ring
    · simp only [hmn, if_false, zero_add]
      exact mul_le_mul_of_nonneg_left (norm_J_le T m n hm0 hn0 hmn) (by positivity)
  calc _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (a m * (starRingEnd ℂ) (a n) * J T m n).re := hI
    _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ((if m = n then T * ‖a n‖ ^ 2 else 0) +
          (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (n / m)|))) := by
        apply Finset.sum_le_sum; intro m hm
        apply Finset.sum_le_sum; intro n hn
        exact hterm m hm n hn
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun m hm => if_pos hm)

end DPMV
