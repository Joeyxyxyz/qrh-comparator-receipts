import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.BL.DPMV
import Zeta23.MV.Final

/-!
# M3 — the uniform mean square `∫₁ᵀ ‖ζ(σ+it)‖² ≤ C·T` for `σ ≥ σ₁ ≥ 2/3` (plan nodes M3b, M3c)

Upstream nodes M1 (`namespace M1`) and M2 (`namespace Zeta23.BL.M2`) are scratch files that
cannot be imported with the prescribed compile command, so the text actually used here is copied
verbatim below (sections `M1copy`, `M2copy`), with the same declaration names.  A downstream
assembly that imports the originals should delete those two sections.

New material is in `namespace Zeta23.BL.M3`:

* `Dpoly σ N t = ∑_{n=1}^N n^{-σ} n^{-it}` and `continuous_Dpoly`;
* `norm_zeta_sq_le_unif` — pointwise, for `σ ≥ σ₁ > 0`, `t ≥ 1`, `N ≥ 1` (no upper bound on `σ`):
  `‖ζ(σ+it)‖² ≤ 4‖Dpoly σ N t‖² + 4 (N^{2-2σ₁}/t² + N^{-2σ₁}/4 + (1+1/σ₁)² t² N^{-2σ₁})`;
* `integral_bound_abstract` — the integration step with the error terms abstracted;
* `meanSquare_param` (M3b) — the parametric mean square, `1/2 < σ₁ < 1 ≤ T`, `σ ≥ σ₁`, `N ≥ 1`:
  `∫₁ᵀ ‖ζ‖² ≤ 4T(1+1/(2σ₁−1)) + 208(1 + N^{2−2σ₁}/(2−2σ₁)) + 4N^{2−2σ₁} + T N^{−2σ₁}
               + 4(1+1/σ₁)² T³ N^{−2σ₁}`;
* `meanSquareUnif_explicit` (M3c) — with `N = ⌊T^{3/2}⌋₊ + 1`, for `2/3 ≤ σ₁ < 1`, all `σ ≥ σ₁`,
  `T ≥ 1`: `∫₁ᵀ ‖ζ(σ+it)‖² ≤ C(σ₁) · T` with the explicit
  `C(σ₁) = 4(1 + 1/(2σ₁−1)) + 208(1 + 4/(2−2σ₁)) + 17 + 4(1+1/σ₁)²`;
* `MeanSquareUnifFrom`, `meanSquareUnif_naive` — the plan's definition and statement verbatim;
* `meanSquareUnif_task` — the task's shape (with the redundant `σ ≤ 1`, `T ≥ 2`).
-/

set_option lang.lemmaCmd true

/-! ## Verbatim copy of M1 (`…/plan-exec/M1/M1.lean`) -/

section M1copy

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

end M1copy

/-! ## Verbatim copy of M2 (`…/plan-exec/M2/M2.lean`) -/

section M2copy

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

end M2copy

/-! ## M3: the uniform mean square -/

open Complex Set MeasureTheory intervalIntegral

namespace Zeta23.BL.M3

/-- The Dirichlet polynomial `∑_{n=1}^N n^{-σ} n^{-it}` of the approximate formula, in the
shape consumed by `M1.dirichlet_meanSquare_le`. -/
noncomputable def Dpoly (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I)

lemma continuous_Dpoly (σ : ℝ) (N : ℕ) : Continuous (Dpoly σ N) := by
  unfold Dpoly
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn0 : (n:ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-- The mean value of `Dpoly` over `[0, T]` (M1d with `a n = n^{-σ}`). -/
lemma meanValue_Dpoly (σ : ℝ) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖Dpoly σ N t‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
        + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ) := by
  have h := M1.dirichlet_meanSquare_le (fun n => (((n:ℝ) ^ (-σ) : ℝ) : ℂ)) N T
  simp only [M1.norm_sq_rpow] at h
  exact h

/-- **Pointwise bound, uniform in `σ ≥ σ₁`** (no upper bound on `σ`): for `t ≥ 1`, `N ≥ 1`,
`‖ζ(σ+it)‖² ≤ 4‖Dpoly σ N t‖² + 4 (N^{2-2σ₁}/t² + N^{-2σ₁}/4 + (1+1/σ₁)² t² N^{-2σ₁})`. -/
theorem norm_zeta_sq_le_unif {σ₁ σ t : ℝ} (h1 : 0 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      4 * ‖Dpoly σ N t‖ ^ 2 +
      4 * ((N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 + (N:ℝ) ^ (-(2 * σ₁)) / 4
            + (1 + 1 / σ₁) ^ 2 * t ^ 2 * (N:ℝ) ^ (-(2 * σ₁))) := by
  have ht0 : t ≠ 0 := by intro h; linarith
  rw [M2.zeta_eq_four_terms (by linarith) ht0 hN, M2.range_sum_eq_Icc ht0 N]
  set S := ∑ n ∈ Finset.Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I) with hS
  set P := (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) with hP
  set Q := (-(N:ℂ) ^ (-((σ:ℂ) + t * I))) / 2 with hQ
  set R := ((σ:ℂ) + t * I) *
    ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1) with hR
  have hSD : S = Dpoly σ N t := rfl
  refine le_trans (M2.norm_add4_sq_le S P Q R) ?_
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hP2 : ‖P‖ ^ 2 ≤ (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 := by
    calc ‖P‖ ^ 2 ≤ ((N:ℝ) ^ (1 - σ₁) / t) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (M2.norm_P_le hσ (by linarith) hN) 2
      _ = (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 := by
          rw [div_pow, M2.rpow_sq_eq hN0 (a := 1 - σ₁) (b := 2 - 2 * σ₁) (by ring)]
  have hQ2 : ‖Q‖ ^ 2 ≤ (N:ℝ) ^ (-(2 * σ₁)) / 4 := by
    calc ‖Q‖ ^ 2 ≤ ((N:ℝ) ^ (-σ₁) / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (M2.norm_Q_le (t := t) hσ hN) 2
      _ = (N:ℝ) ^ (-(2 * σ₁)) / 4 := by
          rw [div_pow, M2.rpow_sq_eq hN0 (a := -σ₁) (b := -(2 * σ₁)) (by ring)]; norm_num
  have hR2 : ‖R‖ ^ 2 ≤ (1 + 1 / σ₁) ^ 2 * t ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) := by
    calc ‖R‖ ^ 2 ≤ ((1 + 1 / σ₁) * t * (N:ℝ) ^ (-σ₁)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (M2.norm_R_le' (t := t) h1 hσ ht hN) 2
      _ = (1 + 1 / σ₁) ^ 2 * t ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) := by
          rw [mul_pow, mul_pow, M2.rpow_sq_eq hN0 (a := -σ₁) (b := -(2 * σ₁)) (by ring)]
  rw [hSD]
  linarith

/-- `t ↦ ‖ζ(σ+it)‖²` is continuous on `[1, T]` (the pole `s = 1` has `t = 0`). -/
lemma continuousOn_norm_zeta_sq (σ T : ℝ) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2) (Icc 1 T) := by
  intro t ht
  have hne : (σ:ℂ) + t * I ≠ 1 := M2.s_ne_one (by linarith [ht.1])
  have h2 : ContinuousAt (fun t : ℝ => (σ:ℂ) + t * I) t := by fun_prop
  have hc : ContinuousAt (riemannZeta ∘ fun t : ℝ => (σ:ℂ) + t * I) t :=
    ContinuousAt.comp (differentiableAt_riemannZeta hne).continuousAt h2
  exact (hc.norm.pow 2).continuousWithinAt

/-- `∫₁ᵀ t⁻² dt = 1 − T⁻¹`. -/
lemma integral_inv_sq_one {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, (t ^ 2)⁻¹ = 1 - T⁻¹ := by
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hderiv : ∀ x ∈ uIcc (1:ℝ) T, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hT] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0:ℝ) < x).ne'
    have := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at this
    exact this
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The integration step, with the error terms abstracted: if on `[1, T]`
`‖ζ(σ+it)‖² ≤ 4‖Dpoly σ N t‖² + 4A/t² + K` with `A, K ≥ 0`, then
`∫₁ᵀ ‖ζ‖² ≤ 4 (T ∑ n^{-2σ} + 26 ∑ (n+1) n^{-2σ}) + 4A + K T`. -/
lemma integral_bound_abstract {σ : ℝ} {N : ℕ} {T : ℝ} (hT : 1 ≤ T) {A K : ℝ}
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hpt : ∀ t ∈ Icc (1:ℝ) T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 4 * ‖Dpoly σ N t‖ ^ 2 + 4 * A * (t ^ 2)⁻¹ + K) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      4 * (T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
          + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)) + 4 * A + K * T := by
  have hDc : Continuous (Dpoly σ N) := continuous_Dpoly σ N
  have hζ : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2) volume 1 T :=
    (continuousOn_norm_zeta_sq σ T).intervalIntegrable_of_Icc hT
  have hDi : IntervalIntegrable (fun t : ℝ => 4 * ‖Dpoly σ N t‖ ^ 2) volume 1 T :=
    Continuous.intervalIntegrable (by fun_prop) 1 T
  have hinv : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hAi : IntervalIntegrable (fun t : ℝ => 4 * A * (t ^ 2)⁻¹) volume 1 T :=
    hinv.const_mul (4 * A)
  have hKi : IntervalIntegrable (fun _ : ℝ => K) volume 1 T := intervalIntegrable_const
  have step1 : ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2
      ≤ ∫ t in (1:ℝ)..T, (4 * ‖Dpoly σ N t‖ ^ 2 + 4 * A * (t ^ 2)⁻¹ + K) :=
    integral_mono_on hT hζ ((hDi.add hAi).add hKi) hpt
  rw [intervalIntegral.integral_add (hDi.add hAi) hKi, intervalIntegral.integral_add hDi hAi,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at step1
  have hD1 : ∫ t in (1:ℝ)..T, ‖Dpoly σ N t‖ ^ 2 ≤ ∫ t in (0:ℝ)..T, ‖Dpoly σ N t‖ ^ 2 :=
    integral_mono_interval (by norm_num) hT le_rfl
      (Filter.Eventually.of_forall (fun t => by positivity))
      (Continuous.intervalIntegrable (by fun_prop) 0 T)
  have hD2 := meanValue_Dpoly σ N T
  have hinv_le : ∫ t in (1:ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
    rw [integral_inv_sq_one hT]
    have : 0 ≤ T⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  have hAinv : 4 * A * ∫ t in (1:ℝ)..T, (t ^ 2)⁻¹ ≤ 4 * A * 1 :=
    mul_le_mul_of_nonneg_left hinv_le (by linarith)
  have hKT : (T - 1) * K ≤ T * K := by nlinarith
  linarith

/-- **M3b. The parametric mean square** (`N` free), uniform in `σ ≥ σ₁`:
for `1/2 < σ₁ < 1`, `σ₁ ≤ σ`, `N ≥ 1`, `T ≥ 1`,
`∫₁ᵀ ‖ζ(σ+it)‖² ≤ 4T(1 + 1/(2σ₁−1)) + 208(1 + N^{2−2σ₁}/(2−2σ₁)) + 4N^{2−2σ₁} + T N^{−2σ₁}
    + 4(1+1/σ₁)² T³ N^{−2σ₁}`. -/
theorem meanSquare_param {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hσ : σ₁ ≤ σ)
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      4 * T * (1 + 1 / (2 * σ₁ - 1))
      + 208 * (1 + (N:ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁))
      + 4 * (N:ℝ) ^ (2 - 2 * σ₁)
      + T * (N:ℝ) ^ (-(2 * σ₁))
      + 4 * (1 + 1 / σ₁) ^ 2 * T ^ 3 * (N:ℝ) ^ (-(2 * σ₁)) := by
  have h1pos : 0 < σ₁ := by linarith
  have hA0 : 0 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hB0 : 0 ≤ (N:ℝ) ^ (-(2 * σ₁)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW0 : 0 ≤ (1 + 1 / σ₁) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ (N:ℝ) ^ (-(2 * σ₁))
      + 4 * (1 + 1 / σ₁) ^ 2 * T ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) := by positivity
  have hpt : ∀ t ∈ Icc (1:ℝ) T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 4 * ‖Dpoly σ N t‖ ^ 2 + 4 * (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹
        + ((N:ℝ) ^ (-(2 * σ₁)) + 4 * (1 + 1 / σ₁) ^ 2 * T ^ 2 * (N:ℝ) ^ (-(2 * σ₁))) := by
    intro t ht
    have key := norm_zeta_sq_le_unif h1pos hσ ht.1 hN
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ht2 : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    have hRt : (1 + 1 / σ₁) ^ 2 * t ^ 2 * (N:ℝ) ^ (-(2 * σ₁))
        ≤ (1 + 1 / σ₁) ^ 2 * T ^ 2 * (N:ℝ) ^ (-(2 * σ₁)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht2 hW0) hB0
    have e1 : (N:ℝ) ^ (2 - 2 * σ₁) / t ^ 2 = (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ :=
      div_eq_mul_inv _ _
    linarith
  have hmain := integral_bound_abstract hT hA0 hK0 hpt
  have hs1 : ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) ≤ 1 + 1 / (2 * σ₁ - 1) := by
    refine le_trans ?_ (M1.sum_rpow_neg_le σ₁ h1 N)
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hs2 : ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (1 + (N:ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁)) := by
    refine le_trans ?_ (M1.sum_weight_le_logfree σ₁ h1 h2 N)
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (by linarith)
  have hT0 : 0 ≤ T := by linarith
  have hTs1 := mul_le_mul_of_nonneg_left hs1 hT0
  have hKT : ((N:ℝ) ^ (-(2 * σ₁)) + 4 * (1 + 1 / σ₁) ^ 2 * T ^ 2 * (N:ℝ) ^ (-(2 * σ₁))) * T
      = T * (N:ℝ) ^ (-(2 * σ₁)) + 4 * (1 + 1 / σ₁) ^ 2 * T ^ 3 * (N:ℝ) ^ (-(2 * σ₁)) := by
    ring
  rw [hKT] at hmain
  linarith

/-! ### M3c: the choice `N = ⌊T^{3/2}⌋₊ + 1` -/

/-- `N := ⌊T^{3/2}⌋₊ + 1` satisfies `1 ≤ N` and `T^{3/2} ≤ N ≤ 2 T^{3/2}` (for `T ≥ 1`). -/
lemma N_choice {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ ⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 ∧
    T ^ ((3:ℝ) / 2) ≤ ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ∧
    ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T ^ ((3:ℝ) / 2) := by
  have hx1 : 1 ≤ T ^ ((3:ℝ) / 2) := Real.one_le_rpow hT (by norm_num)
  refine ⟨by omega, ?_, ?_⟩
  · push_cast
    exact (Nat.lt_floor_add_one _).le
  · push_cast
    have := Nat.floor_le (by linarith : (0:ℝ) ≤ T ^ ((3:ℝ) / 2))
    linarith

/-- If `T^{3/2} ≤ N` and `σ₁ ≥ 2/3` then `N^{-2σ₁} ≤ T^{-2}`. -/
lemma rpow_neg_le_of_choice {T : ℝ} (hT : 1 ≤ T) {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) {N : ℕ}
    (hN : T ^ ((3:ℝ) / 2) ≤ N) :
    (N:ℝ) ^ (-(2 * σ₁)) ≤ (T ^ 2)⁻¹ := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < T ^ ((3:ℝ) / 2) := Real.rpow_pos_of_pos hT0 _
  calc (N:ℝ) ^ (-(2 * σ₁)) ≤ (T ^ ((3:ℝ) / 2)) ^ (-(2 * σ₁)) :=
        Real.rpow_le_rpow_of_nonpos hx0 hN (by linarith)
    _ = T ^ ((3:ℝ) / 2 * (-(2 * σ₁))) := by rw [← Real.rpow_mul hT0.le]
    _ ≤ T ^ (-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = (T ^ 2)⁻¹ := by rw [Real.rpow_neg hT0.le, Real.rpow_two]

/-- If `N ≤ 2 T^{3/2}` and `2/3 ≤ σ₁ ≤ 1` then `N^{2-2σ₁} ≤ 4T`. -/
lemma rpow_pos_le_of_choice {T : ℝ} (hT : 1 ≤ T) {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) (h2 : σ₁ ≤ 1)
    {N : ℕ} (hN : (N:ℝ) ≤ 2 * T ^ ((3:ℝ) / 2)) :
    (N:ℝ) ^ (2 - 2 * σ₁) ≤ 4 * T := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ T ^ ((3:ℝ) / 2) := Real.rpow_nonneg hT0.le _
  have he : 0 ≤ 2 - 2 * σ₁ := by linarith
  calc (N:ℝ) ^ (2 - 2 * σ₁) ≤ (2 * T ^ ((3:ℝ) / 2)) ^ (2 - 2 * σ₁) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hN he
    _ = 2 ^ (2 - 2 * σ₁) * (T ^ ((3:ℝ) / 2)) ^ (2 - 2 * σ₁) := Real.mul_rpow (by norm_num) hx0
    _ = 2 ^ (2 - 2 * σ₁) * T ^ ((3:ℝ) / 2 * (2 - 2 * σ₁)) := by rw [← Real.rpow_mul hT0.le]
    _ ≤ 2 ^ (2:ℝ) * T ^ (1:ℝ) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
        · exact Real.rpow_nonneg hT0.le _
        · exact Real.rpow_nonneg (by norm_num) _
    _ = 4 * T := by rw [Real.rpow_two, Real.rpow_one]; norm_num

/-- **M3c, explicit form.** For `2/3 ≤ σ₁ < 1`, every `σ ≥ σ₁` and every `T ≥ 1`,
`∫₁ᵀ ‖ζ(σ+it)‖² ≤ C(σ₁) T` with
`C(σ₁) = 4(1 + 1/(2σ₁−1)) + 208(1 + 4/(2−2σ₁)) + 17 + 4(1+1/σ₁)²`
(independent of `σ` and `T`). -/
theorem meanSquareUnif_explicit {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) (h2 : σ₁ < 1) {σ : ℝ} (hσ : σ₁ ≤ σ)
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤
      (4 * (1 + 1 / (2 * σ₁ - 1)) + 208 * (1 + 4 / (2 - 2 * σ₁)) + 17
        + 4 * (1 + 1 / σ₁) ^ 2) * T := by
  have h1' : 1 / 2 < σ₁ := by linarith
  obtain ⟨hN1, hNlo, hNhi⟩ := N_choice hT
  have hmain := meanSquare_param h1' h2 hσ hN1 hT
  have hA := rpow_pos_le_of_choice hT h1 h2.le hNhi
  have hB := rpow_neg_le_of_choice hT h1 hNlo
  have hT0 : 0 < T := by linarith
  have hT0' : T ≠ 0 := hT0.ne'
  have hB1 : ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ^ (-(2 * σ₁)) ≤ 1 := by
    refine le_trans hB (inv_le_one_of_one_le₀ ?_)
    nlinarith
  have hT3B : T ^ 3 * ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ^ (-(2 * σ₁)) ≤ T := by
    calc T ^ 3 * ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ^ (-(2 * σ₁)) ≤ T ^ 3 * (T ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = T := by
          rw [show T ^ 3 = T * T ^ 2 by ring, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hT0'),
            mul_one]
  have hAE : ((⌊T ^ ((3:ℝ) / 2)⌋₊ + 1 : ℕ) : ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁)
      ≤ 4 * T / (2 - 2 * σ₁) :=
    div_le_div_of_nonneg_right hA (by linarith)
  have hE : 4 * T / (2 - 2 * σ₁) = (4 / (2 - 2 * σ₁)) * T := by ring
  have hW0 : 0 ≤ (1 + 1 / σ₁) ^ 2 := sq_nonneg _
  have hWT := mul_le_mul_of_nonneg_left hT3B (by positivity : (0:ℝ) ≤ 4 * (1 + 1 / σ₁) ^ 2)
  have hTB := mul_le_mul_of_nonneg_left hB1 hT0.le
  nlinarith

/-- The plan's definition (M3c), verbatim. -/
def MeanSquareUnifFrom (σ₁ : ℝ) : Prop := ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
    ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T

/-- **M3c (partial result (ii) of the plan).** The uniform mean square holds from every
`σ₁ ∈ [2/3, 1)`. -/
theorem meanSquareUnif_naive {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) (h2 : σ₁ < 1) : MeanSquareUnifFrom σ₁ :=
  ⟨_, fun _ hσ _ hT => meanSquareUnif_explicit h1 h2 hσ (by linarith)⟩

/-- The task's shape: `∃ C, ∀ σ, σ₁ ≤ σ → σ ≤ 1 → ∀ T ≥ 2, ∫₁ᵀ ‖ζ(σ+it)‖² ≤ C T`
(the hypothesis `σ ≤ 1` is not needed). -/
theorem meanSquareUnif_task {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) (h2 : σ₁ < 1) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 1 → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T :=
  ⟨_, fun _ hσ _ _ hT => meanSquareUnif_explicit h1 h2 hσ (by linarith)⟩

end Zeta23.BL.M3
