import Mathlib

/-!
# Dirichlet-polynomial mean value (route 2: inner-product expansion)

Target: for `a : ℕ → ℂ`, `N : ℕ`, `T > 0`,

  ∫ t in 0..T, ‖∑ n ∈ Icc 1 N, a n * exp (-(t) * I * log n)‖ ^ 2
    ≤ T * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2
      + ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |log n - log m|)).

Route: `‖S t‖² = S t * conj (S t)` (as a complex number), expand into a double sum of
`a m * conj (a n) * exp ((log n - log m) * t * I)`, integrate termwise with the closed form
`∫₀ᵀ exp (c t I) dt = (exp (c T I) - 1) / (c I)`, bound by the triangle inequality.
-/

open Complex Finset intervalIntegral MeasureTheory
open scoped ComplexConjugate

namespace DPMV2

/-- Closed form of `∫₀ᵀ exp (c t I) dt` for real `c ≠ 0`. -/
lemma integral_exp_mul_I (c : ℝ) (hc : c ≠ 0) (T : ℝ) :
    ∫ t in (0:ℝ)..T, Complex.exp ((c:ℂ) * t * I)
      = (Complex.exp ((c:ℂ) * T * I) - 1) / ((c:ℂ) * I) := by
  have h : ∀ t : ℝ, (c:ℂ) * t * I = ((c:ℂ) * I) * t := fun t => by ring
  simp_rw [h]
  have hcI : (c:ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hc) I_ne_zero
  rw [integral_exp_mul_complex hcI]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]

/-- The `c = 0` case: `∫₀ᵀ exp (0 · t · I) dt = T`. -/
lemma integral_exp_zero_mul_I (T : ℝ) :
    ∫ t in (0:ℝ)..T, Complex.exp (((0:ℝ):ℂ) * t * I) = T := by
  simp

/-- Key scalar lemma: `‖∫₀ᵀ exp (c t I) dt‖ ≤ 2 / |c|` for real `c ≠ 0`. -/
lemma norm_integral_exp_mul_I_le (c : ℝ) (hc : c ≠ 0) (T : ℝ) :
    ‖∫ t in (0:ℝ)..T, Complex.exp ((c:ℂ) * t * I)‖ ≤ 2 / |c| := by
  rw [integral_exp_mul_I c hc T, norm_div]
  have h1 : ‖(c:ℂ) * I‖ = |c| := by simp
  rw [h1]
  have h2 : ‖Complex.exp ((c:ℂ) * T * I) - 1‖ ≤ 2 := by
    calc ‖Complex.exp ((c:ℂ) * T * I) - 1‖
        ≤ ‖Complex.exp ((c:ℂ) * T * I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        have : ((c:ℂ) * T * I) = ((c * T : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, norm_exp_ofReal_mul_I]; norm_num
  gcongr

/-- `‖S t‖²` (as a complex number) is the double sum of
`a m * conj (a n) * exp ((log n - log m) * t * I)`. -/
lemma ofReal_norm_sq_dirichlet (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ((‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t:ℂ) * I * Real.log n)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * conj (a n) *
            Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * t * I) := by
  set S := ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t:ℂ) * I * Real.log n) with hS
  have h1 : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * conj S := by
    rw [← normSq_eq_norm_sq, mul_conj]
  rw [h1, hS, map_sum, sum_mul_sum]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [map_mul, ← exp_conj]
  simp only [map_neg, map_mul, conj_ofReal, conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Termwise integration of the expanded square. -/
lemma ofReal_integral_norm_sq_dirichlet (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ((∫ t in (0:ℝ)..T,
        ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t:ℂ) * I * Real.log n)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * conj (a n) *
            ∫ t in (0:ℝ)..T,
              Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * t * I) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [ofReal_norm_sq_dirichlet]
  have hcont : ∀ (c : ℝ) (z : ℂ),
      Continuous fun t : ℝ => z * Complex.exp ((c:ℂ) * t * I) := by
    intro c z
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun m _ => ?_)]
  · refine sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun n _ => ?_)]
    · refine sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · exact (hcont _ _).intervalIntegrable _ _
  · refine (continuous_finsetSum _ fun n _ => ?_).intervalIntegrable _ _
    exact hcont _ _

/-- For `1 ≤ m`, `1 ≤ n`, `m ≠ n`, the frequency `log n - log m` is nonzero. -/
lemma log_sub_log_ne_zero {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    Real.log n - Real.log m ≠ 0 := by
  intro heq
  apply h
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hn') (Set.mem_Ioi.mpr hm') (sub_eq_zero.mp heq)
  exact_mod_cast this.symm

/-- Per-term bound on `‖∫₀ᵀ exp ((log n - log m) t I) dt‖`. -/
lemma norm_integral_freq_le (T : ℝ) (hT : 0 < T) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ‖∫ t in (0:ℝ)..T, Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * t * I)‖
      ≤ if m = n then T else 2 / |Real.log n - Real.log m| := by
  split_ifs with h
  · subst h
    rw [sub_self]
    rw [integral_exp_zero_mul_I]
    simp [abs_of_pos hT]
  · exact norm_integral_exp_mul_I_le _ (log_sub_log_ne_zero hm hn h) T

/-- Rearrangement of the bound into diagonal and off-diagonal parts. -/
lemma sum_bound_split (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖a n‖ * (if m = n then T else 2 / |Real.log n - Real.log m|)
      = T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log n - Real.log m|)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_ite_eq_of_mem (Finset.Icc 1 N) m (fun _ => T * ‖a m‖ ^ 2) hm,
    ← Finset.sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · subst h; ring
  · ring

/-- **Dirichlet-polynomial mean value** (Montgomery–Vaughan-free, trivial version). -/
theorem dirichlet_mean_value (a : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0:ℝ)..T,
        ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t:ℂ) * I * Real.log n)‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log n - Real.log m|)) := by
  set Z : ℂ := ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      a m * conj (a n) *
        ∫ t in (0:ℝ)..T, Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * t * I) with hZ
  have hre : (∫ t in (0:ℝ)..T,
      ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t:ℂ) * I * Real.log n)‖ ^ 2) = Z.re := by
    rw [hZ, ← ofReal_integral_norm_sq_dirichlet, ofReal_re]
  rw [hre, ← sum_bound_split]
  calc Z.re ≤ ‖Z‖ := re_le_norm Z
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m * conj (a n) *
            ∫ t in (0:ℝ)..T, Complex.exp (((Real.log n - Real.log m : ℝ) : ℂ) * t * I)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun m _ => norm_sum_le _ _)
    _ ≤ _ := by
        refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
        rw [norm_mul, norm_mul, norm_conj]
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        gcongr
        exact norm_integral_freq_le T hT hm1 hn1

end DPMV2
