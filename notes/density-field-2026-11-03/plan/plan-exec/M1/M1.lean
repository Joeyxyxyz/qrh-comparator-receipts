import Mathlib
import Zeta23.BL.DPMV
import Zeta23.MV.Final

/-!
# M1 — Dirichlet-polynomial mean value for the mean-square assembly (BOHR_LANDAU_PLAN §3, M1a–M1d)

Route (B) of the task: the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen : MVDiag 13`
(sorry-free, standard axioms) applied twice to the termwise expansion already proved in
`Zeta23.BL.DPMV` (`DPMV.integral_normSq_sum`, `DPMV.integral_exp_I_mul`, `DPMV.prod_eq_exp`).

Main results (all sorry-free):
* `M1.log_nat_gap`            (M1c)  `1/(n+1) ≤ |log n − log m|` for `m ≠ n`, `m, n ≥ 1`.
* `M1.mv_Icc`                        `MVDiag 13` on the index set `Icc 1 N`, `freq n = log n`,
                                     `δ n = 1/(n+1)`.
* `M1.dirichlet_meanSquare_le` (M1d) `∫₀ᵀ ‖∑_{n≤N} a n n^{-it}‖² ≤ T ∑‖a n‖² + 26 ∑ (n+1)‖a n‖²`
                                     (no hypothesis on `T`).
* `M1.meanValue_pow`                 the requested statement, with the off-diagonal term
                                     `52 · N^{2−2σ} · (log N + 1)` — absolute constant `C(σ) = 52`.
* `M1.meanValue_pow_logfree`         for `1/2 < σ < 1` the log-free form
                                     `52 · (1 + N^{2−2σ}/(2−2σ))`.
* `M1.sum_rpow_neg_le`               `∑_{n≤N} n^{-2σ} ≤ 1 + 1/(2σ−1)` for `σ > 1/2`.
* `M1.sum_Icc_rpow_le`        (M3a)  `∑_{n≤N} n^a ≤ 1 + N^{a+1}/(a+1)` for `−1 < a ≤ 0`.
* `M1.meanValue_pow_explicit`        everything combined, `T ≥ 0`:
      `∫ ≤ T (1 + 1/(2σ−1)) + 52 N^{2−2σ} (log N + 1)`.
-/

open Complex Finset MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace M1

/-- M1c: gaps between logs of distinct positive integers: `|log n − log m| ≥ 1/(n+1)`. -/
theorem log_nat_gap {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    1 / ((n : ℝ) + 1) ≤ |Real.log n - Real.log m| := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · -- m < n
    have hmn : (m:ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have h1 : 0 ≤ Real.log n - Real.log m := by
      have := Real.log_le_log hm' (by linarith : (m:ℝ) ≤ n); linarith
    rw [abs_of_nonneg h1, ← Real.log_div hn'.ne' hm'.ne']
    have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
    rw [inv_div] at h2
    have h3 : 1 / ((n:ℝ) + 1) ≤ 1 / (n:ℝ) := one_div_le_one_div_of_le hn' (by linarith)
    have h4 : 1 / (n:ℝ) ≤ 1 - (m:ℝ) / n := by
      rw [div_le_iff₀ hn']
      have : (1 - (m:ℝ) / n) * n = n - m := by field_simp
      rw [this]; linarith
    exact le_trans h3 (le_trans h4 h2)
  · -- n < m
    have hmn : (n:ℝ) + 1 ≤ m := by exact_mod_cast hlt
    have h1 : Real.log n - Real.log m ≤ 0 := by
      have := Real.log_le_log hn' (by linarith : (n:ℝ) ≤ m); linarith
    rw [abs_of_nonpos h1, neg_sub, ← Real.log_div hm'.ne' hn'.ne']
    have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hm' hn')
    rw [inv_div] at h2
    have h4 : 1 / ((n:ℝ) + 1) ≤ 1 - (n:ℝ) / m := by
      rw [div_le_iff₀ (by linarith)]
      have : (1 - (n:ℝ) / m) * (n + 1) = (m - n) * (n + 1) / m := by field_simp
      rw [this, le_div_iff₀ hm']
      nlinarith [mul_nonneg hn'.le (sub_nonneg.2 hmn)]
    exact le_trans h4 h2

/-- The weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen` on the index set `Icc 1 N`
with frequencies `log n` and gaps `1/(n+1)`. -/
theorem mv_Icc (N : ℕ) (x : ℕ → ℂ) :
    ‖∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m = n then (0:ℂ) else x m * conj (x n) / ((Real.log m - Real.log n : ℝ) : ℂ))‖
      ≤ 13 * ∑ n ∈ Icc 1 N, ((n : ℝ) + 1) * ‖x n‖ ^ 2 := by
  classical
  have key := Zeta23.MV.mvDiag_thirteen (↥(Icc 1 N)) (fun r => Real.log (r : ℕ))
    (fun r => 1 / ((r : ℕ) + 1 : ℝ)) (fun r => x (r : ℕ)) ?_ ?_ ?_
  · have h1 : (∑ r : ↥(Icc 1 N), ∑ t : ↥(Icc 1 N), if r = t then (0:ℂ) else
          x r * conj (x t) / ((Real.log (r:ℕ) - Real.log (t:ℕ) : ℝ) : ℂ))
        = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (if m = n then (0:ℂ) else x m * conj (x n) / ((Real.log m - Real.log n : ℝ) : ℂ)) := by
      rw [← Finset.sum_coe_sort (Icc 1 N)]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_coe_sort (Icc 1 N)]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Subtype.ext_iff]
    have h2 : (∑ r : ↥(Icc 1 N), ‖x r‖ ^ 2 / (1 / ((r:ℕ) + 1 : ℝ)))
        = ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * ‖x n‖ ^ 2 := by
      rw [← Finset.sum_coe_sort (Icc 1 N)]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [div_div_eq_mul_div, div_one, mul_comm]
    rw [h1, h2] at key
    exact key
  · intro r t hrt
    have hr : (0:ℝ) < (r:ℕ) := by exact_mod_cast (Finset.mem_Icc.mp r.2).1
    have ht : (0:ℝ) < (t:ℕ) := by exact_mod_cast (Finset.mem_Icc.mp t.2).1
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr ht) hrt
    exact Subtype.ext (by exact_mod_cast this)
  · intro r; positivity
  · intro r t hrt
    exact log_nat_gap (Finset.mem_Icc.mp t.2).1 (Finset.mem_Icc.mp r.2).1
      (fun h => hrt (Subtype.ext h).symm)


/-- Frequencies of distinct positive integers differ. -/
theorem log_sub_log_ne_zero {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    Real.log n - Real.log m ≠ 0 := by
  intro heq
  apply h
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hn') (Set.mem_Ioi.mpr hm') (sub_eq_zero.mp heq)
  exact_mod_cast this.symm

/-- Termwise identity: `a m conj(a n) J T m n` as diagonal part plus two MV-shaped terms,
with `x n := a n * n^{-iT}`. -/
theorem term_eq (a : ℕ → ℂ) (T : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    a m * conj (a n) * DPMV.J T m n
      = (if m = n then (T:ℂ) * (a m * conj (a m)) else 0)
        + I * (if m = n then (0:ℂ) else
            (a m * (m:ℂ) ^ (-(T:ℂ) * I)) * conj (a n * (n:ℂ) ^ (-(T:ℂ) * I))
              / ((Real.log m - Real.log n : ℝ) : ℂ))
        - I * (if m = n then (0:ℂ) else
            a m * conj (a n) / ((Real.log m - Real.log n : ℝ) : ℂ)) := by
  by_cases hmn : m = n
  · subst hmn
    simp only [if_true, mul_zero, sub_zero, add_zero]
    rw [DPMV.J_self]; ring
  · simp only [hmn, if_false, zero_add]
    have hc : Real.log n - Real.log m ≠ 0 := log_sub_log_ne_zero hm hn hmn
    unfold DPMV.J
    rw [DPMV.integral_exp_I_mul _ hc]
    rw [map_mul, mul_mul_mul_comm, DPMV.prod_eq_exp m n hm hn T]
    have hc' : ((Real.log n - Real.log m : ℝ) : ℂ) ≠ 0 := by rwa [Complex.ofReal_ne_zero]
    have hrel : ((Real.log m - Real.log n : ℝ) : ℂ) = -((Real.log n - Real.log m : ℝ) : ℂ) := by
      push_cast; ring
    rw [hrel, div_neg, div_neg, div_mul_eq_div_div, div_I]
    ring

/-- The double sum of `DPMV.integral_normSq_sum`, rearranged. -/
theorem Z_eq (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * conj (a n) * DPMV.J T m n)
      = (T:ℂ) * ∑ n ∈ Icc 1 N, a n * conj (a n)
        + I * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n then (0:ℂ) else
            (a m * (m:ℂ) ^ (-(T:ℂ) * I)) * conj (a n * (n:ℂ) ^ (-(T:ℂ) * I))
              / ((Real.log m - Real.log n : ℝ) : ℂ))
        - I * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n then (0:ℂ) else
            a m * conj (a n) / ((Real.log m - Real.log n : ℝ) : ℂ)) := by
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn =>
    term_eq a T (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mul_sum]
  rw [sub_left_inj, add_left_inj]
  exact Finset.sum_congr rfl (fun m hm => if_pos hm)

/-- `‖n^{-iT}‖ = 1`. -/
theorem norm_cpow_neg_mul_I (n : ℕ) (hn : 0 < n) (T : ℝ) :
    ‖(n:ℂ) ^ (-(T:ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- **M1d. Dirichlet-polynomial mean value, Montgomery–Vaughan form** (constant 26 = 2·13):
`∫₀ᵀ ‖∑_{n≤N} a n n^{-it}‖² dt ≤ T ∑ ‖a n‖² + 26 ∑ (n+1) ‖a n‖²`. -/
theorem dirichlet_meanSquare_le (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2
      ≤ T * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 + 26 * ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * ‖a n‖ ^ 2 := by
  have hI : (∫ t in (0:ℝ)..T, ‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2)
      = (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, a m * conj (a n) * DPMV.J T m n).re := by
    have h2 := congrArg Complex.re (DPMV.integral_normSq_sum a N T)
    rwa [Complex.ofReal_re] at h2
  rw [hI, Z_eq, Complex.sub_re, Complex.add_re]
  have hdiag : ((T:ℂ) * ∑ n ∈ Icc 1 N, a n * conj (a n)).re = T * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 := by
    have : (∑ n ∈ Icc 1 N, a n * conj (a n)) = ((∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hdiag]
  set Sx : ℂ := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n then (0:ℂ) else
      (a m * (m:ℂ) ^ (-(T:ℂ) * I)) * conj (a n * (n:ℂ) ^ (-(T:ℂ) * I))
        / ((Real.log m - Real.log n : ℝ) : ℂ) with hSx
  set Sa : ℂ := ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n then (0:ℂ) else
      a m * conj (a n) / ((Real.log m - Real.log n : ℝ) : ℂ) with hSa
  have hx : ‖Sx‖ ≤ 13 * ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * ‖a n‖ ^ 2 := by
    have := mv_Icc N (fun n => a n * (n:ℂ) ^ (-(T:ℂ) * I))
    refine le_trans this (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [norm_mul, norm_cpow_neg_mul_I n (Finset.mem_Icc.mp hn).1, mul_one]
  have ha : ‖Sa‖ ≤ 13 * ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * ‖a n‖ ^ 2 := mv_Icc N a
  have hre : (I * Sx).re - (I * Sa).re ≤ ‖Sx‖ + ‖Sa‖ := by
    rw [← Complex.sub_re]
    refine le_trans (Complex.re_le_norm _) ?_
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  linarith


/-! ### Specialisation to `a n = n^{-σ}` -/

/-- `n^{-(σ+it)} = n^{-σ} · n^{-it}` for `n ≥ 1`. -/
theorem cpow_neg_add_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    (n:ℂ) ^ (-((σ:ℂ) + t * I)) = (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I) := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show -((σ:ℂ) + t * I) = ((-σ : ℝ) : ℂ) + (-(t:ℂ) * I) by push_cast; ring,
    Complex.cpow_add _ _ hn', Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  ring

/-- `‖n^{-σ}‖² = n^{-2σ}`. -/
theorem norm_sq_rpow (n : ℕ) (σ : ℝ) :
    ‖(((n:ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2 = (n:ℝ) ^ (-2 * σ) := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1; push_cast; ring

/-- The harmonic sum over `Icc 1 N`, bounded by `1 + log N`. -/
theorem sum_inv_le (N : ℕ) : ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  exact h

/-- Off-diagonal weight for `a n = n^{-σ}`, `σ ≤ 1`:
`∑_{n≤N} (n+1) n^{-2σ} ≤ 2 N^{2-2σ} (log N + 1)`. -/
theorem sum_weight_le (σ : ℝ) (hσ1 : σ ≤ 1) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  have hterm : ∀ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (N:ℝ) ^ (2 - 2 * σ) * (n:ℝ)⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hn' : (0:ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have e1 : (n:ℝ) ^ (-2 * σ) = (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ * (n:ℝ) ^ (2 - 2 * σ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn', ← Real.rpow_add hn']
      congr 1; ring
    have h2 : ((n:ℝ) + 1) * (n:ℝ)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hn']; linarith
    have h3 : (n:ℝ) ^ (2 - 2 * σ) ≤ (N:ℝ) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hn'.le (by exact_mod_cast hnN) (by linarith)
    calc ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
        = (((n:ℝ) + 1) * (n:ℝ)⁻¹) * (n:ℝ) ^ (2 - 2 * σ) * (n:ℝ)⁻¹ := by rw [e1]; ring
      _ ≤ 2 * (N:ℝ) ^ (2 - 2 * σ) * (n:ℝ)⁻¹ := by gcongr
  calc ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ ∑ n ∈ Icc 1 N, 2 * (N:ℝ) ^ (2 - 2 * σ) * (n:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = 2 * (N:ℝ) ^ (2 - 2 * σ) * ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * (N:ℝ) ^ (2 - 2 * σ) * (1 + Real.log N) := by
        gcongr
        exact sum_inv_le N
    _ = 2 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by ring

/-- The mean value for the coefficients `n^{-σ}`, raw form. -/
theorem meanValue_pow_raw (σ : ℝ) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
        + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ) := by
  have hfun : (fun t : ℝ => ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2)
      = fun t : ℝ => ‖∑ n ∈ Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2 := by
    funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    exact cpow_neg_add_eq n (Finset.mem_Icc.mp hn).1 σ t
  rw [hfun]
  have h := dirichlet_meanSquare_le (fun n => (((n:ℝ) ^ (-σ) : ℝ) : ℂ)) N T
  simp only [norm_sq_rpow] at h
  exact h

/-- **M1 (main deliverable).** Mean value of `∑_{n≤N} n^{-(σ+it)}` over `0 ≤ t ≤ T`, for
`1/2 < σ ≤ 1`, with the off-diagonal bounded by `52 N^{2-2σ} (log N + 1)` (absolute constant). -/
theorem meanValue_pow (σ : ℝ) (_hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) (T : ℝ) (_hT : 0 < T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
        + 52 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  have h := meanValue_pow_raw σ N T
  have h2 := sum_weight_le σ hσ1 N
  linarith

/-! ### Partial sums of `n^a` -/

/-- Integral comparison: for `a ≤ 0`, `a ≠ -1`, `1 ≤ N`,
`∑_{n=1}^N n^a ≤ 1 + (N^{a+1} − 1)/(a+1)`. -/
theorem sum_Icc_rpow_le_integral {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : a ≤ 0) (ha' : a ≠ -1) :
    ∑ n ∈ Icc 1 N, (n:ℝ) ^ a ≤ 1 + ((N:ℝ) ^ (a + 1) - 1) / (a + 1) := by
  rw [← Finset.sum_erase_add (Icc 1 N) _ (Finset.left_mem_Icc.mpr hN), Finset.Icc_erase_left,
    Nat.cast_one, Real.one_rpow, add_comm]
  gcongr
  have hanti : AntitoneOn (fun x : ℝ => x ^ a) (Set.Icc ((1:ℕ):ℝ) (N:ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos ha).mono ?_
    intro x hx
    simp only [Nat.cast_one] at hx
    exact Set.mem_Ioi.mpr (by linarith [hx.1])
  have hint := AntitoneOn.sum_le_integral_Ico hN hanti
  have hsum : ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ a = ∑ n ∈ Ioc 1 N, (n:ℝ) ^ a := by
    rw [Finset.sum_Ico_add' (fun x : ℕ => (x:ℝ) ^ a) 1 N 1]
    rfl
  rw [hsum] at hint
  refine le_trans hint (le_of_eq ?_)
  rw [Nat.cast_one, integral_rpow (Or.inr ⟨ha', ?_⟩), Real.one_rpow]
  rw [Set.uIcc_of_le (by exact_mod_cast hN)]
  intro h
  have := (Set.mem_Icc.mp h).1
  linarith

/-- Diagonal partial sum, `1/2 < σ`: `∑_{n≤N} n^{-2σ} ≤ 1 + 1/(2σ − 1)` (uniform in `N`). -/
theorem sum_rpow_neg_le (σ : ℝ) (hσ : 1/2 < σ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n:ℝ) ^ (-2 * σ) ≤ 1 + 1 / (2 * σ - 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty]
    have : 0 < 2 * σ - 1 := by linarith
    positivity
  · have h := sum_Icc_rpow_le_integral hN (a := -2 * σ) (by linarith) (by intro h; linarith)
    refine le_trans h (add_le_add le_rfl ?_)
    have e : (-2 * σ + 1) = -(2 * σ - 1) := by ring
    rw [e, div_neg, ← neg_div, neg_sub]
    have hNpow : 0 ≤ (N:ℝ) ^ (-(2 * σ - 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- M3a of the plan: for `−1 < a ≤ 0`, `∑_{n≤N} n^a ≤ 1 + N^{a+1}/(a+1)`. -/
theorem sum_Icc_rpow_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) :
    ∑ n ∈ Icc 1 N, (n:ℝ) ^ a ≤ 1 + (N:ℝ) ^ (a + 1) / (a + 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by linarith), zero_div, add_zero]
    exact zero_le_one
  · refine le_trans (sum_Icc_rpow_le_integral hN ha' (by intro h; linarith))
      (add_le_add le_rfl ?_)
    have : 0 < a + 1 := by linarith
    exact div_le_div_of_nonneg_right (by linarith) this.le

/-- Off-diagonal weight for `a n = n^{-σ}`, `1/2 < σ < 1`, log-free:
`∑_{n≤N} (n+1) n^{-2σ} ≤ 2 (1 + N^{2-2σ}/(2-2σ))`. -/
theorem sum_weight_le_logfree (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (1 + (N:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)) := by
  have hterm : ∀ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ) ≤ 2 * (n:ℝ) ^ (-2 * σ + 1) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn' : (0:ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
    rw [Real.rpow_add hn', Real.rpow_one]
    have hP : 0 ≤ (n:ℝ) ^ (-2 * σ) := Real.rpow_nonneg hn'.le _
    nlinarith [mul_nonneg hP (sub_nonneg.2 hn1')]
  calc ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ ∑ n ∈ Icc 1 N, 2 * (n:ℝ) ^ (-2 * σ + 1) := Finset.sum_le_sum hterm
    _ = 2 * ∑ n ∈ Icc 1 N, (n:ℝ) ^ (-2 * σ + 1) := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 + (N:ℝ) ^ (-2 * σ + 1 + 1) / (-2 * σ + 1 + 1)) := by
        gcongr
        exact sum_Icc_rpow_le (by linarith) (by linarith)
    _ = 2 * (1 + (N:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)) := by
        have e : -2 * σ + 1 + 1 = 2 - 2 * σ := by ring
        rw [e]

/-- **Log-free mean value** for `1/2 < σ < 1`: off-diagonal `52 (1 + N^{2−2σ}/(2−2σ))`. -/
theorem meanValue_pow_logfree (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
        + 52 * (1 + (N:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)) := by
  have h := meanValue_pow_raw σ N T
  have h2 := sum_weight_le_logfree σ hσ hσ1 N
  linarith

/-- **Fully explicit mean value**, `1/2 < σ ≤ 1`, `0 ≤ T`:
`∫₀ᵀ ‖∑_{n≤N} n^{-(σ+it)}‖² ≤ T (1 + 1/(2σ−1)) + 52 N^{2−2σ} (log N + 1)`. -/
theorem meanValue_pow_explicit (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) (T : ℝ)
    (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2
      ≤ T * (1 + 1 / (2 * σ - 1)) + 52 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  have h := meanValue_pow_raw σ N T
  have h2 := sum_weight_le σ hσ1 N
  have h3 := mul_le_mul_of_nonneg_left (sum_rpow_neg_le σ hσ N) hT
  linarith

end M1
