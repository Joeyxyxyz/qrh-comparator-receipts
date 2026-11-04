/-
BohrLandauPartial.lean — merged assembly of the plan-exec nodes
J023, M1, M2, M3a, J45, M3, J67, J89, M45 (density-work, 2026-11-03).

Every block below is the VERBATIM text of the corresponding node file, with the copies that
the later nodes carried of earlier nodes removed (M3 carried M1/M2; J67 carried J023/J45;
J89 carried M3/J67 and two J023 lemmas; M45 carried M3).  Duplicates removed:
  * J45's `divisor_riemannZeta_eq`, `Rout`, `rin`, `hwin`, `geom_facts` (identical to J023's).
Each node sits in its own `section` so that its `open`s stay local.  No `sorry` anywhere.

Headline results (all sorry-free, standard axioms — see the `#print axioms` block at the end):
  * `Zeta23.BL.M3.meanSquareUnif_naive`   : MeanSquareUnifFrom σ₁ for 2/3 ≤ σ₁ < 1
  * `Zeta23.BL.M45.meanSquare_strip_of`   : ∫₀ᵀ‖ζ(σ+it)‖² ≤ C T for 2/3 ≤ σ ≤ 1
  * `Zeta23.BL.rightHalf_of_meanSquareUnif` : J8, generic in σ₁
  * `Zeta23.BL.rightHalf_gt_sixth`         : NRight δ T = O(T) for every δ > 1/6
  * `Zeta23.BL.bohrLandau_gt_sixth`        : NOff δ 0 T = O(T) for every δ > 1/6
-/
import Mathlib
import Zeta23.BohrLandau
import Zeta23.RvM.ZetaGrowth
import Zeta23.BL.JensenDisc
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.BL.DPMV
import Zeta23.MV.Final

set_option lang.lemmaCmd true


/-! # M1 — Dirichlet-polynomial mean value (weighted Hilbert inequality) -/

section M1part

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

end M1part


/-! # M2 — approximate functional equation terms -/

section M2part

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

end M2part


/-! # M3a — partial sums of n^a -/

section M3apart

open Finset Real

namespace M3a

/-- Rewrite `∑ n ∈ Icc 1 N, f n` as `f 1 + ∑ i ∈ Ico 1 N, f (i + 1)` (for `1 ≤ N`). -/
lemma sum_Icc_one_eq (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, f n = f 1 + ∑ i ∈ Ico 1 N, f (i + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_eq_sum_Ico_succ_bot (by omega), sum_Ico_add' f 1 N 1]

lemma antitoneOn_rpow_Icc {a : ℝ} (ha' : a ≤ 0) (N : ℕ) :
    AntitoneOn (fun x : ℝ => x ^ a) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) :=
  (antitoneOn_rpow_Ioi_of_exponent_nonpos ha').mono
    (fun x hx => lt_of_lt_of_le (by norm_num) hx.1)

/-- The integral comparison for the tail `∑ i ∈ Ico 1 N, (i+1)^a`. -/
lemma sum_Ico_rpow_succ_le_integral {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) (hN : 1 ≤ N) :
    ∑ i ∈ Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ a ≤ ((N : ℝ) ^ (a + 1) - 1) / (a + 1) := by
  have h := (antitoneOn_rpow_Icc ha' N).sum_le_integral_Ico hN
  rw [Nat.cast_one, integral_rpow (Or.inl ha), one_rpow] at h
  exact h

/-- M3a, main statement: partial sums of `n ^ a` for `-1 < a ≤ 0`. -/
theorem sum_Icc_rpow_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a ≤ 1 + (N : ℝ) ^ (a + 1) / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [zero_rpow ha1.ne']
  rw [sum_Icc_one_eq (fun n : ℕ => (n : ℝ) ^ a) hN]
  simp only [Nat.cast_one, one_rpow]
  have h := sum_Ico_rpow_succ_le_integral ha ha' hN
  have h2 : ((N : ℝ) ^ (a + 1) - 1) / (a + 1) ≤ (N : ℝ) ^ (a + 1) / (a + 1) :=
    div_le_div_of_nonneg_right (by linarith) ha1.le
  linarith

/-- M3a with an explicit constant `C(a) = 1 + 1/(a+1)` (needs `1 ≤ N` so that `1 ≤ N^(a+1)`). -/
theorem sum_Icc_rpow_le_mul {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a ≤ (1 + 1 / (a + 1)) * (N : ℝ) ^ (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (a + 1) :=
    one_le_rpow (by exact_mod_cast hN) ha1.le
  calc ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a
      ≤ 1 + (N : ℝ) ^ (a + 1) / (a + 1) := sum_Icc_rpow_le ha ha'
    _ ≤ (N : ℝ) ^ (a + 1) + (N : ℝ) ^ (a + 1) / (a + 1) := by linarith
    _ = (1 + 1 / (a + 1)) * (N : ℝ) ^ (a + 1) := by ring

/-- For `a < -1` the partial sums are bounded by the convergent series `∑' n, n^a`. -/
theorem sum_Icc_rpow_le_tsum {a : ℝ} (ha : a < -1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a ≤ ∑' n : ℕ, (n : ℝ) ^ a :=
  (Real.summable_nat_rpow.2 ha).sum_le_tsum _
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) a)

/-- The "diagonal" form used in M3b: for `1 < p`,
`∑ n ∈ Icc 1 N, n^(-p) ≤ ∑' n, 1 / n^p`. -/
theorem sum_Icc_rpow_neg_le_tsum_one_div {p : ℝ} (hp : 1 < p) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-p) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ p := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := Real.summable_one_div_nat_rpow.2 hp
  have h := hs.sum_le_tsum (Finset.Icc 1 N)
    (fun n _ => by positivity)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- Mixed sum with a logarithm, general exponent: for `-1 < a < 0` (the case `a = 0` is also
allowed) and `1 ≤ N`,
`∑ n ∈ Icc 1 N, n^a (log n + 1) ≤ (1 + 1/(a+1)) * N^(a+1) * (log N + 1)`. -/
theorem sum_Icc_rpow_mul_log_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a * (Real.log n + 1) ≤
      (1 + 1 / (a + 1)) * (N : ℝ) ^ (a + 1) * (Real.log N + 1) := by
  have hlogN : 0 ≤ Real.log N + 1 := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  calc ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a * (Real.log n + 1)
      ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a * (Real.log N + 1) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) a)
        have h1 : (0 : ℝ) < n := by exact_mod_cast hn.1
        have h2 : (n : ℝ) ≤ N := by exact_mod_cast hn.2
        linarith [Real.log_le_log h1 h2]
    _ = (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a) * (Real.log N + 1) := by
        rw [Finset.sum_mul]
    _ ≤ ((1 + 1 / (a + 1)) * (N : ℝ) ^ (a + 1)) * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_right (sum_Icc_rpow_le_mul ha ha' hN) hlogN

/-- Mixed sum in the σ-form of the plan, for `1/2 < σ < 1`:
`∑ n ∈ Icc 1 N, n^(1-2σ) (log n + 1) ≤ (1 + 1/(2-2σ)) * N^(2-2σ) * (log N + 1)`.
(For `σ = 1` the statement of the plan is false: the left side is `∑ (log n + 1)/n ≍ (log N)^2`,
so the endpoint is excluded.) -/
theorem sum_Icc_rpow_mul_log_le_of_sigma {N : ℕ} {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1)
    (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n + 1) ≤
      (1 + 1 / (2 - 2 * σ)) * (N : ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  have h := sum_Icc_rpow_mul_log_le (N := N) (a := 1 - 2 * σ) (by linarith) (by linarith) hN
  have e : (1 - 2 * σ) + 1 = 2 - 2 * σ := by ring
  rw [e] at h
  exact h

/-- The plain partial-sum bound in the σ-form, `1/2 < σ < 1`:
`∑ n ∈ Icc 1 N, n^(1-2σ) ≤ 1 + N^(2-2σ)/(2-2σ)`. -/
theorem sum_Icc_rpow_le_of_sigma {N : ℕ} {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) ≤ 1 + (N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) := by
  have h := sum_Icc_rpow_le (N := N) (a := 1 - 2 * σ) (by linarith) (by linarith)
  have e : (1 - 2 * σ) + 1 = 2 - 2 * σ := by ring
  rw [e] at h
  exact h

end M3a

end M3apart


/-! # M3 — the uniform mean square (M3b/M3c) -/

section M3part

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

end M3part


/-! # J023 — J0 trivialities, J2 divisor of ζ, J3 geometry -/

section J023part

open Set Complex Metric

namespace Zeta23.BL
open MNF.RH

/-! ## J0 — trivialities about `NRight` -/

/-- δ ≥ 1/2: no nontrivial zero has `Re ρ - 1/2 ≥ δ` (since `Re ρ < 1`), so the count is 0. -/
theorem NRight_eq_zero_of_half_le {δ T : ℝ} (hδ : 1 / 2 ≤ δ) : NRight δ T = 0 := by
  unfold NRight
  have h : MNF.RH.zerosIn 0 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2} = ∅ := by
    ext ρ
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hz, _, _⟩ hδρ
    linarith [hz.2.2]
  rw [h, finsum_mem_empty]

/-- Window splitting for MNF's `zerosIn` (copy of `Zeta23.zerosIn_union`). -/
theorem MNF_zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    MNF.RH.zerosIn a c = MNF.RH.zerosIn a b ∪ MNF.RH.zerosIn b c := by
  ext ρ
  simp only [MNF.RH.zerosIn, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

/-- `NRight` splits at any intermediate height `a`. -/
theorem NRight_add {δ a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    NRight δ T
      = NRight δ a + ∑ᶠ ρ ∈ MNF.RH.zerosIn a T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ := by
  unfold NRight
  rw [MNF_zerosIn_union ha haT, union_inter_distrib_right]
  refine finsum_mem_union ?_ ((MNF.RH.zerosIn_finite 0 a).subset inter_subset_left)
    ((MNF.RH.zerosIn_finite a T).subset inter_subset_left)
  rw [disjoint_left]
  rintro ρ ⟨⟨_, _, hb⟩, _⟩ ⟨⟨_, ha', _⟩, _⟩
  exact absurd hb (not_le.2 ha')

/-- The plan's J0 statement: the count between heights 4 and `T`, as a real finsum. -/
theorem NRight_sub_eq {δ T : ℝ} (hT : 4 ≤ T) :
    (NRight δ T : ℝ) - NRight δ 4
      = ∑ᶠ ρ ∈ MNF.RH.zerosIn 4 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, (zeta_order ρ : ℝ) := by
  rw [NRight_add (by norm_num : (0:ℝ) ≤ 4) hT, Nat.cast_add,
    Nat.cast_finsum_mem ((MNF.RH.zerosIn_finite 4 T).subset inter_subset_left)]
  ring

/-- `NRight δ T` is monotone in `T` (needed by J8 for `2 ≤ T < 4`). -/
theorem NRight_mono {δ T T' : ℝ} (h : T ≤ T') : NRight δ T ≤ NRight δ T' := by
  unfold NRight
  rw [finsum_mem_eq_finite_toFinset_sum _ ((MNF.RH.zerosIn_finite 0 T).subset inter_subset_left),
    finsum_mem_eq_finite_toFinset_sum _ ((MNF.RH.zerosIn_finite 0 T').subset inter_subset_left)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Finite.mem_toFinset] at hρ ⊢
  exact ⟨MNF.RH.zerosIn_mono le_rfl h hρ.1, hρ.2⟩

/-! ## J2 — the divisor of ζ on a closed ball avoiding the pole -/

/-- At a point `ρ ≠ 1` where ζ does not vanish, `zeta_order ρ = 0`. -/
theorem zeta_order_eq_zero_of_ne_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (h : riemannZeta ρ ≠ 0) :
    zeta_order ρ = 0 := by
  unfold zeta_order
  rw [(MNF.RH.analyticAt_riemannZeta hρ1).analyticOrderAt_eq_zero.2 h]
  rfl

/-- The divisor of ζ on a closed ball not containing 1 is `zeta_order` (ℤ-valued form). -/
theorem divisor_riemannZeta_eq_int {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    MeromorphicOn.divisor riemannZeta (closedBall c r) ρ = (zeta_order ρ : ℤ) := by
  have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hρ)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (Zeta23.RvM.analyticOnNhd_riemannZeta h1) hρ]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1)
  unfold zeta_order
  rw [← hn, ENat.map_natCast, ENat.toNat_natCast]
  simp

/-- The plan's J2 statement (ℝ-valued form). -/
theorem divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    (MeromorphicOn.divisor riemannZeta (closedBall c r) ρ : ℝ) = (zeta_order ρ : ℝ) := by
  rw [divisor_riemannZeta_eq_int h1 hρ]
  push_cast
  rfl

/-- A finite set of points of the ball contributes at most the full divisor sum
(this is the form J4 consumes: `S ⊆ ball`, no support bookkeeping needed). -/
theorem sum_zeta_order_le_finsum_divisor {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ closedBall c r) :
    ∑ ρ ∈ S, (zeta_order ρ : ℝ)
      ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) := by
  set D := MeromorphicOn.divisor riemannZeta (closedBall c r) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  have hnn : ∀ u, (0:ℝ) ≤ (D u : ℝ) := fun u => by
    have h0 : (0:ℤ) ≤ D u := by
      simpa using
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg (Zeta23.RvM.analyticOnNhd_riemannZeta h1) u
    exact_mod_cast h0
  have hsupp : Function.support (fun u => (D u : ℝ)) ⊆ ↑(S ∪ hfin.toFinset) := by
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Finset.coe_union, Finite.coe_toFinset, mem_union, Function.mem_support]
    exact Or.inr (fun h => hu (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc ∑ ρ ∈ S, (zeta_order ρ : ℝ) = ∑ ρ ∈ S, (D ρ : ℝ) :=
        Finset.sum_congr rfl fun ρ hρ => (divisor_riemannZeta_eq h1 (hS ρ hρ)).symm
    _ ≤ ∑ ρ ∈ S ∪ hfin.toFinset, (D ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun u _ _ => hnn u

/-- The divisor sum over a ball in `Re s > 0`, `s ≠ 1` is the multiplicity-weighted count of the
nontrivial zeros in the ball (zeros with `Re ≥ 1` do not exist). -/
theorem finsum_divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (hre : ∀ s ∈ closedBall c r, 0 < s.re) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)
      = ∑ᶠ ρ ∈ ZetaZeros ∩ closedBall c r, (zeta_order ρ : ℝ) := by
  rw [finsum_mem_def]
  congr 1
  ext u
  by_cases hu : u ∈ closedBall c r
  · rw [divisor_riemannZeta_eq h1 hu]
    by_cases hz : riemannZeta u = 0
    · have hmem : u ∈ ZetaZeros ∩ closedBall c r := by
        refine ⟨⟨hz, hre u hu, ?_⟩, hu⟩
        by_contra hlt
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hlt) hz
      rw [indicator_of_mem hmem]
    · have hmem : u ∉ ZetaZeros ∩ closedBall c r := fun h => hz h.1.1
      rw [indicator_of_notMem hmem, zeta_order_eq_zero_of_ne_zero (fun h => h1 (h ▸ hu)) hz]
      simp
  · have hmem : u ∉ ZetaZeros ∩ closedBall c r := fun h => hu h.2
    rw [indicator_of_notMem hmem, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
    simp

/-- Same, with the zeros indexed by a `zerosIn` window containing the ball's ordinates. -/
theorem finsum_divisor_riemannZeta_eq_zerosIn {c : ℂ} {r a b : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) (hre : ∀ s ∈ closedBall c r, 0 < s.re)
    (him : ∀ s ∈ closedBall c r, a < s.im ∧ s.im ≤ b) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)
      = ∑ᶠ ρ ∈ MNF.RH.zerosIn a b ∩ closedBall c r, (zeta_order ρ : ℝ) := by
  rw [finsum_divisor_riemannZeta_eq h1 hre]
  refine finsum_mem_congr ?_ (fun _ _ => rfl)
  ext ρ
  constructor
  · rintro ⟨hz, hρ⟩; exact ⟨⟨hz, him ρ hρ⟩, hρ⟩
  · rintro ⟨⟨hz, _⟩, hρ⟩; exact ⟨hz, hρ⟩

/-! ## J3 — geometry constants -/

/-- outer radius, inner radius, half-window; valid for 1/2 < σ₁ < 1/2 + δ, δ ≤ 1/2 -/
noncomputable def Rout (σ₁ : ℝ) : ℝ := 2 - σ₁
noncomputable def rin (σ₁ δ : ℝ) : ℝ := (Rout σ₁ + (3 / 2 - δ)) / 2
noncomputable def hwin (σ₁ δ : ℝ) : ℝ := Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2

/-- Membership in a closed ball of ℂ, in coordinates. -/
theorem mem_closedBall_iff_sq {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    z ∈ closedBall c r ↔ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 ≤ r ^ 2 := by
  rw [mem_closedBall, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_le_left hr]
  simp [sub_re, sub_im]

/-- Coordinate bounds from membership in a closed ball. -/
theorem abs_re_im_sub_le_of_mem_closedBall {c z : ℂ} {r : ℝ} (hz : z ∈ closedBall c r) :
    |z.re - c.re| ≤ r ∧ |z.im - c.im| ≤ r := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h1 : |z.re - c.re| ≤ ‖z - c‖ := by simpa using Complex.abs_re_le_norm (z - c)
  have h2 : |z.im - c.im| ≤ ‖z - c‖ := by simpa using Complex.abs_im_le_norm (z - c)
  exact ⟨h1.trans hz, h2.trans hz⟩

/-- Coordinate bounds for the discs centred `2 + t*I`. -/
theorem bounds_of_mem_closedBall_two {t R : ℝ} {s : ℂ} (hs : s ∈ closedBall (2 + t * I) R) :
    2 - R ≤ s.re ∧ s.re ≤ 2 + R ∧ t - R ≤ s.im ∧ s.im ≤ t + R := by
  obtain ⟨h1, h2⟩ := abs_re_im_sub_le_of_mem_closedBall hs
  simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, im_ofNat, mul_im, zero_add] at h1 h2
  rw [abs_le] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The pole is outside every disc centred `2 + t*I` of radius `R < t`. -/
theorem one_notMem_closedBall_two {t R : ℝ} (hRt : R < t) :
    (1 : ℂ) ∉ closedBall (2 + t * I) R := by
  intro h
  have := (bounds_of_mem_closedBall_two h).2.2.1
  simp at this
  linarith

/-- `closedBall (2 + t*I) (Rout σ₁) ⊆ {s | σ₁ ≤ s.re}`. -/
theorem re_ge_of_mem_closedBall_Rout {σ₁ t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + t * I) (Rout σ₁)) : σ₁ ≤ s.re := by
  have := (bounds_of_mem_closedBall_two hs).1
  unfold Rout at this
  linarith

/-- The outer disc for `t ≥ 3`, `1/2 < σ₁`: contained in `{Re s ≥ σ₁} ∩ {s ≠ 1}`, and avoids 1. -/
theorem outer_disc_facts {σ₁ t : ℝ} (h1 : 1 / 2 < σ₁) (ht : 3 ≤ t) :
    (1 : ℂ) ∉ closedBall (2 + t * I) (Rout σ₁) ∧
    closedBall (2 + t * I) (Rout σ₁) ⊆ {s : ℂ | σ₁ ≤ s.re ∧ s ≠ 1} := by
  have hR : Rout σ₁ < 3 / 2 := by unfold Rout; linarith
  have hnot : (1 : ℂ) ∉ closedBall (2 + t * I) (Rout σ₁) :=
    one_notMem_closedBall_two (by linarith)
  exact ⟨hnot, fun s hs => ⟨re_ge_of_mem_closedBall_Rout hs, fun h => hnot (h ▸ hs)⟩⟩

/-- The plan's J3 statement. -/
theorem geom_facts {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧
    ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ →
      ρ ∈ closedBall (2 + t * I) (rin σ₁ δ) := by
  set A : ℝ := 3 / 2 - δ with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hrA : A < rin σ₁ δ := by unfold rin Rout; rw [hA]; linarith
  have hrin_pos : 0 < rin σ₁ δ := by linarith
  have hrin_lt : rin σ₁ δ < Rout σ₁ := by unfold rin Rout; linarith
  have hRout : Rout σ₁ < 3 / 2 := by unfold Rout; linarith
  have hsq_pos : 0 < rin σ₁ δ ^ 2 - A ^ 2 := by nlinarith
  have hhwin_sq : hwin σ₁ δ ^ 2 = (rin σ₁ δ ^ 2 - A ^ 2) / 4 := by
    unfold hwin
    rw [div_pow, Real.sq_sqrt hsq_pos.le]
    norm_num
  have hwin_pos : 0 < hwin σ₁ δ := by
    unfold hwin
    exact div_pos (Real.sqrt_pos.2 hsq_pos) (by norm_num)
  have hwin_le : hwin σ₁ δ ≤ 1 := by
    unfold hwin
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), one_mul, Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ⟨hrin_pos, hrin_lt, hRout, hwin_pos, hwin_le, fun ρ hρ1 hρ2 t ht => ?_⟩
  rw [mem_closedBall_iff_sq hrin_pos.le]
  simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, im_ofNat, mul_im, zero_add]
  have hre_sq : (ρ.re - 2) ^ 2 ≤ A ^ 2 := sq_le_sq' (by rw [hA]; linarith) (by linarith)
  have him_sq : (ρ.im - t) ^ 2 ≤ hwin σ₁ δ ^ 2 := by
    have : (ρ.im - t) ^ 2 = |t - ρ.im| ^ 2 := by rw [sq_abs]; ring
    rw [this]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [hhwin_sq] at him_sq
  linarith

end Zeta23.BL

end J023part


/-! # J45 — J4 per-t count, J5 majorant Lz (J2/J3 duplicates dropped) -/

section J45part

open Set Complex MeasureTheory Metric MeromorphicOn
open Real (circleAverage circleAverage_mono circleAverage_eq_intervalAverage)
open scoped Real

namespace Zeta23.BL
open MNF.RH

/-! ## Geometry: the pole is outside every disc centred `2 + t I` of radius `< 3` when `t ≥ 3` -/

theorem one_notMem_closedBall_two_add {t R : ℝ} (ht : 3 ≤ t) (hR : R < 3) :
    (1 : ℂ) ∉ closedBall (2 + t * I) R := by
  intro h
  rw [mem_closedBall, dist_eq_norm] at h
  have him := Complex.abs_im_le_norm ((1 : ℂ) - (2 + t * I))
  have : ((1 : ℂ) - (2 + t * I)).im = -t := by simp
  rw [this, abs_neg, abs_of_pos (by linarith)] at him
  linarith

theorem one_notMem_sphere_two_add {t R : ℝ} (ht : 3 ≤ t) (hR : R < 3) :
    (1 : ℂ) ∉ sphere (2 + t * I) R :=
  fun h => one_notMem_closedBall_two_add ht hR (sphere_subset_closedBall h)

/-! ## J4: per-t count in divisor form and in Finset form -/

/-- `-log ‖ζ(2 + t I)‖ ≤ log 3`, from `zeta_lower_bound_two`. -/
theorem neg_log_norm_riemannZeta_two_add_le (t : ℝ) :
    -Real.log ‖riemannZeta (2 + t * I)‖ ≤ Real.log 3 := by
  have h := Zeta23.RvM.zeta_lower_bound_two t
  have h' : Real.log (1 / 3) ≤ Real.log ‖riemannZeta (2 + t * I)‖ :=
    Real.log_le_log (by norm_num) h
  rw [one_div, Real.log_inv] at h'
  linarith

/-- J4, divisor form: Jensen's disc inequality for ζ on `closedBall (2 + t I) R`, `t ≥ 3`. -/
theorem count_disc_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3) :
    (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall (2 + t * I) r) u : ℝ))
        * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
          - Real.log ‖riemannZeta (2 + t * I)‖ :=
  sum_divisor_mul_log_le (2 + t * I) r R riemannZeta hr hrR
    (Zeta23.RvM.analyticOnNhd_riemannZeta (one_notMem_closedBall_two_add ht hR))
    (Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re (by simp))

/-- A finite set of nontrivial zeros inside the inner ball is dominated by the divisor sum. -/
theorem finset_sum_zeta_order_le_finsum_divisor {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall c r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ))
      ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) := by
  set D : ℂ → ℝ := fun u => (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) with hD
  have hζ := Zeta23.RvM.analyticOnNhd_riemannZeta h1
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor riemannZeta (closedBall c r)).finiteSupport (isCompact_closedBall ..)
      |>.subset fun _ _ ↦ (by simp_all)
  have hnn : ∀ u, 0 ≤ D u := fun u => by
    simp only [hD]
    exact_mod_cast hζ.divisor_nonneg u
  have h1' : ∑ ρ ∈ S, (zeta_order ρ : ℝ) = ∑ ρ ∈ S, D ρ := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [hD]
    exact (divisor_riemannZeta_eq h1 (hS ρ hρ).2).symm
  have h2 : ∑ᶠ u, D u = ∑ u ∈ S ∪ hfin.toFinset, D u :=
    finsum_eq_sum_of_support_subset D (by
      intro u hu
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inr hu)
  rw [h1', h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun u _ _ => hnn u)

/-- J4, Finset form (the plan's `count_window_le` with the ball membership as hypothesis):
for `t ≥ 3`, `0 < r < R < 3` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + t I) r`,
`(∑ ρ ∈ S, zeta_order ρ) · log (R/r) ≤ circleAverage (log ‖ζ‖) (2 + t I) R + log 3`. -/
theorem count_finset_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R + Real.log 3 := by
  have hlog : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).mpr hrR.le)
  have h1 := finset_sum_zeta_order_le_finsum_divisor
    (one_notMem_closedBall_two_add ht (hrR.trans hR)) S hS
  have h2 := count_disc_le ht hr hrR hR
  have h3 := neg_log_norm_riemannZeta_two_add_le t
  calc (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall (2 + t * I) r) u : ℝ))
          * Real.log (R / r) := mul_le_mul_of_nonneg_right h1 hlog
    _ ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
          - Real.log ‖riemannZeta (2 + t * I)‖ := h2
    _ ≤ _ := by linarith

/-! ## J5: the majorant `Lz` -/

/-- `Lz z = (1/2) log (1 + ‖ζ z‖²)`: a continuous, nonnegative majorant of `log ‖ζ z‖`. -/
noncomputable def Lz (z : ℂ) : ℝ := (1 / 2) * Real.log (1 + ‖riemannZeta z‖ ^ 2)

theorem Lz_nonneg (z : ℂ) : 0 ≤ Lz z := by
  unfold Lz
  have : (1 : ℝ) ≤ 1 + ‖riemannZeta z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have := Real.log_nonneg this
  positivity

/-- `log x ≤ (1/2) log (1 + x²)` for `x ≥ 0` (with the convention `log 0 = 0`). -/
theorem log_le_half_log_one_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ (1 / 2) * Real.log (1 + x ^ 2) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    simp only [Real.log_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.log_one, mul_zero, le_refl]
  · have h1 : Real.log (x ^ 2) ≤ Real.log (1 + x ^ 2) :=
      Real.log_le_log (pow_pos h 2) (le_add_of_nonneg_left zero_le_one)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

theorem log_norm_le_Lz (z : ℂ) : Real.log ‖riemannZeta z‖ ≤ Lz z :=
  log_le_half_log_one_add_sq (norm_nonneg _)

theorem continuousOn_Lz {U : Set ℂ} (hU : (1 : ℂ) ∉ U) : ContinuousOn Lz U := by
  have hζ : ContinuousOn riemannZeta U :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta hU).continuousOn
  unfold Lz
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · exact continuousOn_const.add (hζ.norm.pow 2)
  · intro z _
    positivity

theorem circleIntegrable_Lz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h1 : (1 : ℂ) ∉ sphere c R) :
    CircleIntegrable Lz c R :=
  (continuousOn_Lz h1).circleIntegrable hR

/-- J5 (first half): `circleAverage (log ‖ζ‖) c R ≤ circleAverage Lz c R` on pole-free circles. -/
theorem circleAverage_log_norm_le_Lz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h1 : (1 : ℂ) ∉ sphere c R) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) c R ≤ circleAverage Lz c R :=
  circleAverage_mono
    ((Zeta23.RvM.analyticOnNhd_riemannZeta h1).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR)
    (circleIntegrable_Lz hR h1)
    (fun z _ => log_norm_le_Lz z)

/-- `x ↦ (1/2) log (1 + x)` is concave on `Ici 0`. -/
theorem concaveOn_half_log_one_add :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => (1 / 2) * Real.log (1 + x)) := by
  have h1 : ConcaveOn ℝ ((fun z : ℝ => (1 : ℝ) + z) ⁻¹' Ioi 0) (Real.log ∘ fun z : ℝ => 1 + z) :=
    strictConcaveOn_log_Ioi.concaveOn.translate_right 1
  have h2 : ConcaveOn ℝ (Ici (0 : ℝ)) (Real.log ∘ fun z : ℝ => 1 + z) :=
    h1.subset (fun x hx => by simp only [mem_preimage, mem_Ioi]; linarith [mem_Ici.mp hx])
      (convex_Ici 0)
  have h3 := h2.smul (c := (1 / 2 : ℝ)) (by norm_num)
  simpa [smul_eq_mul, Function.comp] using h3

/-- J5 (second half): Jensen's inequality for the concave function `x ↦ (1/2) log (1 + x)`:
`circleAverage Lz c R ≤ (1/2) log (1 + circleAverage ‖ζ‖² c R)` on pole-free circles. -/
theorem circleAverage_Lz_le {c : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ sphere c R) :
    circleAverage Lz c R
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) c R) := by
  have hI : uIoc (0:ℝ) (2 * π) = Ioc 0 (2 * π) := uIoc_of_le (by positivity)
  have : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) (2 * π))) := by
    rw [hI]; infer_instance
  have : NeZero (volume (uIoc (0:ℝ) (2 * π))) := ⟨by simp⟩
  have hζ : ContinuousOn riemannZeta (sphere c R) :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta h1).continuousOn
  have hcont : Continuous (fun θ : ℝ ↦ ‖riemannZeta (circleMap c R θ)‖ ^ 2) :=
    ((hζ.comp_continuous (continuous_circleMap c R)
      (fun θ ↦ circleMap_mem_sphere c hR.le θ)).norm).pow 2
  have hcont2 : Continuous (fun θ : ℝ ↦ (1 / 2) * Real.log (1 + ‖riemannZeta (circleMap c R θ)‖ ^ 2)) :=
    continuous_const.mul ((continuous_const.add hcont).log (fun θ => by
      show (1 : ℝ) + ‖riemannZeta (circleMap c R θ)‖ ^ 2 ≠ 0
      positivity))
  rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
  have key := concaveOn_half_log_one_add.le_map_average
    (μ := volume.restrict (uIoc (0:ℝ) (2 * π)))
    (f := fun θ : ℝ ↦ ‖riemannZeta (circleMap c R θ)‖ ^ 2)
    (by
      refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
      · exact continuousOn_const.add continuousOn_id
      · intro x hx; have := mem_Ici.mp hx; positivity)
    isClosed_Ici
    (by filter_upwards; simp)
    hcont.integrableOn_uIoc
    hcont2.integrableOn_uIoc
  exact key

/-- J4 + J5 combined: the per-t count against the log of the mean square on the outer circle.
For `t ≥ 3`, `0 < r < R < 3` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + t I) r`. -/
theorem count_finset_le_log_meanSq {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R)
    (hR : R < 3) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) R)
          + Real.log 3 := by
  have h1 := count_finset_le ht hr hrR hR S hS
  have h2 := circleAverage_log_norm_le_Lz (hr.trans hrR).le (one_notMem_sphere_two_add ht hR)
    (c := 2 + t * I)
  have h3 := circleAverage_Lz_le (hr.trans hrR) (one_notMem_sphere_two_add ht hR) (c := 2 + t * I)
  linarith

/-- the closed outer ball lies in the half-plane `Re s ≥ σ₁`. -/
theorem closedBall_Rout_subset {σ₁ t : ℝ} :
    Metric.closedBall (2 + t * I) (Rout σ₁) ⊆ {s : ℂ | σ₁ ≤ s.re} := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - (2 + t * I))
  have hre : (z - (2 + t * I)).re = z.re - 2 := by simp
  rw [hre] at h
  have := (abs_le.mp (h.trans hz)).1
  show σ₁ ≤ z.re
  unfold Rout at this
  linarith

/-- J4 in the plan's window form (`count_window_le` of BOHR_LANDAU_PLAN §3). -/
theorem count_window_le {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) (Rout σ₁)
          + Real.log 3 := by
  obtain ⟨hr, hrR, hR, -, -, hmem⟩ := geom_facts h1 hδσ hδ
  refine count_finset_le ht hr hrR (by linarith) S fun ρ hρ => ?_
  obtain ⟨hz, hδρ, hwt⟩ := hS ρ hρ
  exact ⟨hz, hmem ρ (by linarith) hz.2.2 t hwt⟩

/-- J4 + J5 in the plan's window form, with the outer circle average of `log ‖ζ‖` replaced by
`(1/2) log (1 + circleAverage ‖ζ‖²)`. -/
theorem count_window_le_log_meanSq {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) (Rout σ₁))
          + Real.log 3 := by
  obtain ⟨hr, hrR, hR, -, -, hmem⟩ := geom_facts h1 hδσ hδ
  refine count_finset_le_log_meanSq ht hr hrR (by linarith) S fun ρ hρ => ?_
  obtain ⟨hz, hδρ, hwt⟩ := hS ρ hρ
  exact ⟨hz, hmem ρ (by linarith) hz.2.2 t hwt⟩

/-- The plan's `circleAverage_log_le_Lz` (J5), specialised to the discs centred `2 + t I`. -/
theorem circleAverage_log_le_Lz {t R : ℝ} (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3 / 2) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
      ≤ circleAverage Lz (2 + t * I) R :=
  circleAverage_log_norm_le_Lz hR.le (one_notMem_sphere_two_add ht (by linarith))

end Zeta23.BL

end J45part


/-! # J67 — J6 integrate the count, J7 Fubini + mean square (copies dropped) -/

section J67part

open Set Complex MeasureTheory Metric MeromorphicOn
open Real (circleAverage circleAverage_mono circleAverage_eq_intervalAverage circleAverage_def)
open scoped Real

namespace Zeta23.BL
open MNF.RH

/-! ## New: J7 preliminaries — the circle points, joint continuity, product integrability -/

/-- `circleMap (2 + t I) R θ = (2 + R cos θ) + (t + R sin θ) I`. -/
theorem circleMap_two_add (t R θ : ℝ) :
    circleMap (2 + t * I) R θ
      = ((2 + R * Real.cos θ : ℝ) : ℂ) + ((t + R * Real.sin θ : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- For `t ≥ 3`, `0 ≤ R < 3`, the circle `circleMap (2 + t I) R` avoids the pole. -/
theorem circleMap_two_add_ne_one {t R : ℝ} (ht : 3 ≤ t) (hR0 : 0 ≤ R) (hR : R < 3) (θ : ℝ) :
    circleMap (2 + t * I) R θ ≠ 1 :=
  fun h => one_notMem_sphere_two_add ht hR (h ▸ circleMap_mem_sphere _ hR0 θ)

/-- `(t, θ) ↦ Lz (circleMap (2 + t I) R θ)` is continuous on `{t ≥ 3} × ℝ`. -/
theorem continuousOn_Lz_circleMap {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    ContinuousOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2)) (Ici 3 ×ˢ univ) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap (2 + p.1 * I) R p.2) := by
    unfold circleMap
    fun_prop
  refine (continuousOn_Lz (U := {z : ℂ | z ≠ 1}) (by simp)).comp hc.continuousOn ?_
  rintro ⟨t, θ⟩ ⟨ht, -⟩
  show circleMap (2 + t * I) R θ ≠ 1
  exact circleMap_two_add_ne_one ht hR0 hR θ

/-- Product integrability of `Lz ∘ circleMap` on the rectangle `(3, T+3] × (0, 2π]`. -/
theorem integrableOn_Lz_circleMap_prod {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    IntegrableOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      (Ioc 3 (T + 3) ×ˢ Ioc 0 (2 * π)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      (Icc 3 (T + 3) ×ˢ Icc 0 (2 * π)) :=
    (continuousOn_Lz_circleMap hR0 hR).mono (prod_mono Icc_subset_Ici_self (subset_univ _))
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The same, for the product of the restricted measures (the form Fubini consumes). -/
theorem integrable_Lz_circleMap_prod_restrict {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    Integrable (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      ((volume.restrict (Ioc 3 (T + 3))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact integrableOn_Lz_circleMap_prod hR0 hR

/-- `t ↦ circleAverage Lz (2 + t I) R` is interval integrable on `[3, T + 3]`
(marginal of the product integrability). -/
theorem intervalIntegrable_circleAverage_Lz {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => circleAverage Lz (2 + t * I) R) volume 3 (T + 3) := by
  have h2 := (integrable_Lz_circleMap_prod_restrict (T := T) hR0 hR).integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have heq : (fun t : ℝ => circleAverage Lz (2 + t * I) R)
      = fun t : ℝ => (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), Lz (circleMap (2 + t * I) R θ) := by
    funext t
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
  rw [heq]
  exact h2.const_mul _

/-! ## J7 (first half): Fubini -/

/-- J7, Fubini form: the `t`-integral of the circle averages is `(2π)⁻¹` times the `θ`-integral
of the `t`-integrals along the circle points. -/
theorem integral_circleAverage_Lz_eq_swap {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (hT : 0 ≤ T) :
    ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) R
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) R θ) := by
  simp_rw [circleAverage_def, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral_intervalIntegral_swap ?_
  rw [uIoc_of_le (by linarith : (3:ℝ) ≤ T + 3), uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
  exact integrableOn_Lz_circleMap_prod hR0 hR

/-! ## J7 (second half): the inner integral along a vertical segment -/

/-- `Lz z ≤ (1/2) ‖ζ z‖²`, from `log (1 + x) ≤ x`. -/
theorem Lz_le_half_sq (z : ℂ) : Lz z ≤ (1 / 2) * ‖riemannZeta z‖ ^ 2 := by
  unfold Lz
  have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + ‖riemannZeta z‖ ^ 2)
  exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- The vertical segment `σ + u I`, `u ∈ [a, b]` with `a > 0`, avoids the pole. -/
theorem segment_mapsTo_ne_one {σ a b : ℝ} (ha : 0 < a) :
    MapsTo (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) (Icc a b) {z : ℂ | z ≠ 1} := by
  intro u hu heq
  have := congrArg Complex.im heq
  simp at this
  linarith [hu.1]

theorem intervalIntegrable_Lz_segment {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => Lz ((σ : ℂ) + (u : ℂ) * I)) volume a b :=
  ((continuousOn_Lz (U := {z : ℂ | z ≠ 1}) (by simp)).comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (segment_mapsTo_ne_one ha)).intervalIntegrable_of_Icc hab

theorem intervalIntegrable_normSq_zeta_segment {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2) volume a b :=
  (((Zeta23.RvM.analyticOnNhd_riemannZeta (S := {z : ℂ | z ≠ 1}) (by simp)).continuousOn.comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (segment_mapsTo_ne_one ha)).norm.pow 2).intervalIntegrable_of_Icc hab

/-- J7, per-`θ` bound: along the circle points `circleMap (2 + t I) (Rout σ₁) θ`, `t ∈ [3, T+3]`,
the integral of `Lz` is an integral along the vertical segment `Re s = 2 + Rout σ₁ cos θ`
(which lies in `[σ₁, 2 + Rout σ₁]`), enlarged to `u ∈ [1, T + 5]`, and bounded via
`Lz ≤ (1/2)‖ζ‖²` by the uniform mean square `hMS`. -/
theorem integral_Lz_circle_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ} (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) (θ : ℝ) :
    ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ) ≤ (1 / 2) * (C * (T + 5)) := by
  have hRdef : Rout σ₁ = 2 - σ₁ := rfl
  have hR0 : 0 < Rout σ₁ := by rw [hRdef]; linarith
  have hR : Rout σ₁ < 3 / 2 := by rw [hRdef]; linarith
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hR0.le
  have hcos' := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hR0.le
  have hsin : |Rout σ₁ * Real.sin θ| ≤ Rout σ₁ := by
    rw [abs_mul, abs_of_pos hR0]
    exact mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)
  have hsin' := abs_le.1 hsin
  have hσ1 : σ₁ ≤ 2 + Rout σ₁ * Real.cos θ := by rw [hRdef] at hcos ⊢; linarith
  have hσ2 : 2 + Rout σ₁ * Real.cos θ ≤ 2 + Rout σ₁ := by linarith
  simp_rw [circleMap_two_add]
  have hshift := intervalIntegral.integral_comp_add_right (a := 3) (b := T + 3)
    (fun u : ℝ => Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I))
    (Rout σ₁ * Real.sin θ)
  rw [hshift]
  calc ∫ u in (3 + Rout σ₁ * Real.sin θ)..(T + 3 + Rout σ₁ * Real.sin θ),
          Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)
      ≤ ∫ u in (1:ℝ)..(T + 5), Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I) :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun u => Lz_nonneg _)
          (intervalIntegrable_Lz_segment one_pos (by linarith))
    _ ≤ ∫ u in (1:ℝ)..(T + 5),
          (1 / 2) * ‖riemannZeta (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith)
          (intervalIntegrable_Lz_segment one_pos (by linarith))
          ((intervalIntegrable_normSq_zeta_segment one_pos (by linarith)).const_mul _)
          (fun u _ => Lz_le_half_sq _)
    _ = (1 / 2) * ∫ u in (1:ℝ)..(T + 5),
          ‖riemannZeta (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (1 / 2) * (C * (T + 5)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hMS _ hσ1 hσ2 (T + 5) (by linarith)

/-- J7, assembled: the `t`-integral of the circle averages of `Lz` over `[3, T + 3]` is at most
`(1/2) C (T + 5)` under the uniform mean square hypothesis `hMS` on `σ ∈ [σ₁, 2 + Rout σ₁]`. -/
theorem integral_circleAverage_Lz_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ}
    (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) :
    ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) (Rout σ₁) ≤ (1 / 2) * (C * (T + 5)) := by
  have hR0 : 0 < Rout σ₁ := by show 0 < 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  rw [integral_circleAverage_Lz_eq_swap hR0.le hR hT]
  have hG0 : ∀ θ : ℝ, 0 ≤ ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ) :=
    fun θ => intervalIntegral.integral_nonneg (by linarith) (fun t _ => Lz_nonneg _)
  have hGle : ∀ θ : ℝ, ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)
      ≤ (1 / 2) * (C * (T + 5)) := integral_Lz_circle_le h1 h2 hT hMS
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun θ : ℝ => ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ))
    (C := (1 / 2) * (C * (T + 5))) (fun θ _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 θ)]; exact hGle θ)
  rw [sub_zero, abs_of_pos (by positivity)] at hnorm
  have hpi : 0 ≤ (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)
      ≤ (2 * π)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)‖ :=
        mul_le_mul_of_nonneg_left (Real.le_norm_self _) hpi
    _ ≤ (2 * π)⁻¹ * ((1 / 2) * (C * (T + 5)) * (2 * π)) :=
        mul_le_mul_of_nonneg_left hnorm hpi
    _ = (1 / 2) * (C * (T + 5)) := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-! ## J6: integrate the per-`t` count over `t ∈ [3, T + 3]` -/

/-- J6 (`count_le_integral` of BOHR_LANDAU_PLAN §3): every zero `ρ` with `Re ρ ≥ 1/2 + δ`,
`4 < Im ρ ≤ T` lies in the inner ball `closedBall (2 + t I) (rin σ₁ δ)` for all `t` in the window
`[Im ρ − hwin, Im ρ + hwin] ⊆ [3, T + 3]`, so integrating the per-`t` bound of J4+J5 over
`t ∈ [3, T + 3]` gives the multiplicity-weighted count times `2 hwin log (Rout/rin)`. -/
theorem count_le_integral {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3) := by
  obtain ⟨hr, hrR, hR, hh, hh1, -⟩ := geom_facts h1 hδσ hδ
  -- the zeros counted by `NRight δ T - NRight δ 4`
  have hZfin : (MNF.RH.zerosIn 4 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2}).Finite :=
    (MNF.RH.zerosIn_finite 4 T).subset inter_subset_left
  have hcount : (NRight δ T : ℝ) - NRight δ 4 = ∑ ρ ∈ hZfin.toFinset, (zeta_order ρ : ℝ) := by
    rw [NRight_sub_eq hT, finsum_mem_eq_finite_toFinset_sum _ hZfin]
  -- the step functions `g ρ`: `zeta_order ρ` on the window of `ρ`, `0` elsewhere
  set g : ℂ → ℝ → ℝ := fun ρ t =>
    (Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)).indicator (fun _ => (zeta_order ρ : ℝ)) t with hg
  -- pointwise, for `t ∈ [3, T + 3]`: J4 + J5 applied to the zeros whose window contains `t`
  have hpt : ∀ t ∈ Icc (3:ℝ) (T + 3),
      (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
        ≤ circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3 := by
    intro t ht
    have ht3 : 3 ≤ t := ht.1
    classical
    set S : Finset ℂ := Finset.filter
      (fun ρ : ℂ => t ∈ Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)) hZfin.toFinset with hS
    have hsum : ∑ ρ ∈ hZfin.toFinset, g ρ t = ∑ ρ ∈ S, (zeta_order ρ : ℝ) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [hg, Set.indicator_apply]
    rw [hsum]
    have hcw := count_window_le h1 hδσ hδ ht3 S (fun ρ hρ => by
      rw [hS, Finset.mem_filter, Finite.mem_toFinset] at hρ
      obtain ⟨⟨⟨hz, -, -⟩, hδρ⟩, hρt⟩ := hρ
      have h1' : ρ.im - hwin σ₁ δ ≤ t := hρt.1
      have h2' : t ≤ ρ.im + hwin σ₁ δ := hρt.2
      exact ⟨hz, hδρ, abs_le.2 ⟨by linarith, by linarith⟩⟩)
    have hLz := circleAverage_log_le_Lz ht3 (hr.trans hrR) hR
    linarith
  -- the step functions are integrable, with integral `2 hwin · zeta_order ρ`
  have hgi : ∀ ρ ∈ hZfin.toFinset, IntervalIntegrable (g ρ) volume 3 (T + 3) := by
    intro ρ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact (integrable_const _).indicator measurableSet_Icc
  have hgint : ∀ ρ ∈ hZfin.toFinset,
      ∫ t in (3:ℝ)..(T + 3), g ρ t = 2 * hwin σ₁ δ * (zeta_order ρ : ℝ) := by
    intro ρ hρ
    rw [Finite.mem_toFinset] at hρ
    obtain ⟨⟨-, h4, hT'⟩, -⟩ := hρ
    have hsub : Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ) ⊆ Ioc 3 (T + 3) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp only [hg]
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
      inter_eq_left.2 hsub, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  -- integrate the pointwise bound
  have hLHSint : IntervalIntegrable
      (fun t => (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)) volume 3 (T + 3) := by
    have := (IntervalIntegrable.sum hZfin.toFinset hgi).mul_const (Real.log (Rout σ₁ / rin σ₁ δ))
    simpa only [Finset.sum_apply] using this
  have hRHSint : IntervalIntegrable
      (fun t => circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3) volume 3 (T + 3) :=
    (intervalIntegrable_circleAverage_Lz (hr.trans hrR).le (by linarith) (by linarith)).add
      intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (by linarith) hLHSint hRHSint hpt
  have hLHS : ∫ t in (3:ℝ)..(T + 3),
        (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
      = 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_finsetSum hgi,
      Finset.sum_congr rfl hgint, ← Finset.mul_sum, ← hcount]
    ring
  rw [← hLHS]
  exact hmono

/-! ## J6 + J7 assembled -/

/-- J6 + J7: for `T ≥ 4`, under the uniform mean square hypothesis `hMS` on
`σ ∈ [σ₁, 2 + Rout σ₁]` with constant `C`,
`2 hwin log(Rout/rin) (NRight δ T − NRight δ 4) ≤ (1/2) C (T + 5) + T log 3`. -/
theorem count_le_meanSquare {σ₁ δ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ (1 / 2) * (C * (T + 5)) + T * Real.log 3 := by
  have hR0 : 0 ≤ Rout σ₁ := by show 0 ≤ 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  have h6 := count_le_integral h1 hδσ hδ hT
  have h7 := integral_circleAverage_Lz_le (T := T) h1 h2 (by linarith) hMS
  rw [intervalIntegral.integral_add
    (intervalIntegrable_circleAverage_Lz (T := T) hR0 hR (by linarith))
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h6
  have : (T + 3 - 3) * Real.log 3 = T * Real.log 3 := by ring
  linarith

/-- The same with the mean square hypothesis in the shape of `MeanSquareUnifFrom σ₁`
(no upper bound on `σ`). -/
theorem count_le_meanSquare' {σ₁ δ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ (1 / 2) * (C * (T + 5)) + T * Real.log 3 :=
  count_le_meanSquare h1 h2 hδσ hδ (fun σ hσ _ T hT => hMS σ hσ T hT) hT

/-! ## The region `σ > 1`: the trivial bound, so `hMS` need only be supplied on `[σ₁, σ₂]`, σ₂ > 1 -/

/-- `ζ(σ) ≤ ζ(σ₂)` for `σ ≥ σ₂ > 1` (as sums `∑ 1/n^σ`). -/
theorem tsum_one_div_rpow_anti {σ₂ σ : ℝ} (h2 : 1 < σ₂) (hσ : σ₂ ≤ σ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ σ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ σ₂ := by
  refine (Real.summable_one_div_nat_rpow.2 (h2.trans_le hσ)).tsum_le_tsum (fun n => ?_)
    (Real.summable_one_div_nat_rpow.2 h2)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : σ ≠ 0), Real.zero_rpow (by linarith : σ₂ ≠ 0)]
  · have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn' hσ)

/-- For `σ ≥ σ₂ > 1` the mean square on `[1, T]` is at most `ζ(σ₂)² T` (trivial bound). -/
theorem meanSquare_of_gt_one {σ₂ σ : ℝ} (h2 : 1 < σ₂) (hσ : σ₂ ≤ σ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ σ₂) ^ 2 * T := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ σ₂ with hZ
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := T) (C := Z ^ 2)
    (f := fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_zeta_le_tsum (h2.trans_le hσ) t).trans (tsum_one_div_rpow_anti h2 hσ)) 2)
  rw [abs_of_nonneg (by linarith)] at h
  calc _ ≤ ‖∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ Z ^ 2 * (T - 1) := h
    _ ≤ Z ^ 2 * T := by nlinarith [sq_nonneg Z]

/-- A mean square hypothesis on `[σ₁, σ₂]` with `σ₂ > 1` extends to all `σ ≥ σ₁`
(constant `max C ζ(σ₂)²`). -/
theorem meanSquare_hyp_extend {σ₁ σ₂ C : ℝ} (h2 : 1 < σ₂)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) :
    ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2
        ≤ max C ((∑' n : ℕ, 1 / (n : ℝ) ^ σ₂) ^ 2) * T := by
  intro σ hσ T hT
  rcases le_or_gt σ σ₂ with h | h
  · exact (hMS σ hσ h T hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · exact (meanSquare_of_gt_one h2 h.le (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

end Zeta23.BL

end J67part


/-! # J89 — J8 generic assembly, J9 δ > 1/6 (copies dropped) -/

section J89part

open Set Complex Metric

namespace Zeta23.BL
open MNF.RH

/-! ## J8: generic assembly, parametric in `σ₁` -/

/-- **J8 (`rightHalf_of_meanSquareUnif` of BOHR_LANDAU_PLAN §3).** For `1/2 < σ₁ < 1`, the
uniform mean square `MeanSquareUnifFrom σ₁` gives `NRight δ T = O(T)` for every `δ > σ₁ − 1/2`.
Explicit constant for `δ < 1/2`: `C = NRight δ 4 / 2 + ((9/8) max C_ms 0 + log 3) / K` with
`K = 2 hwin σ₁ δ · log (Rout σ₁ / rin σ₁ δ)`. -/
theorem rightHalf_of_meanSquareUnif {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1)
    (hms : M3.MeanSquareUnifFrom σ₁) :
    ∀ δ : ℝ, σ₁ - 1 / 2 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T := by
  intro δ hδσ
  -- the trivial case `δ ≥ 1/2`
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · exact ⟨0, fun T _ => by rw [NRight_eq_zero_of_half_le hδ]; simp⟩
  obtain ⟨C₀, hC₀⟩ := hms
  -- replace the mean-square constant by a nonnegative one
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have hMS : ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ max C₀ 0 * T :=
    fun σ hσ T hT => (hC₀ σ hσ T hT).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  obtain ⟨hr, hrR, -, hh, -, -⟩ := geom_facts h1 hδσ hδ.le
  have hlog : 0 < Real.log (Rout σ₁ / rin σ₁ δ) := Real.log_pos ((one_lt_div hr).2 hrR)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((9 / 8) * max C₀ 0 + Real.log 3) / K := ⟨_, rfl⟩
  have hMK : M * K = (9 / 8) * max C₀ 0 + Real.log 3 := by rw [hM]; exact div_mul_cancel₀ _ hKpos.ne'
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg (by positivity) hKpos.le
  have hN4 : (0:ℝ) ≤ NRight δ 4 := Nat.cast_nonneg _
  refine ⟨(NRight δ 4 : ℝ) / 2 + M, fun T hT => ?_⟩
  rcases le_or_gt 4 T with hT4 | hT4
  · -- `T ≥ 4`: J6 + J7
    have h67 := count_le_meanSquare' h1 h2 hδσ hδ.le hMS hT4
    rw [← hK] at h67
    have hbound : (1 / 2) * (max C₀ 0 * (T + 5)) + T * Real.log 3 ≤ K * (M * T) := by
      have h95 : (1 / 2) * (max C₀ 0 * (T + 5)) ≤ (9 / 8) * max C₀ 0 * T := by nlinarith
      calc (1 / 2) * (max C₀ 0 * (T + 5)) + T * Real.log 3
          ≤ (9 / 8) * max C₀ 0 * T + T * Real.log 3 := by linarith
        _ = ((9 / 8) * max C₀ 0 + Real.log 3) * T := by ring
        _ = K * (M * T) := by rw [← hMK]; ring
    have hdiff : (NRight δ T : ℝ) - NRight δ 4 ≤ M * T :=
      le_of_mul_le_mul_left (h67.trans hbound) hKpos
    nlinarith [mul_nonneg hN4 (by linarith : (0:ℝ) ≤ T - 2)]
  · -- `2 ≤ T < 4`: monotonicity
    have hmono : (NRight δ T : ℝ) ≤ NRight δ 4 := by exact_mod_cast NRight_mono hT4.le
    nlinarith [mul_nonneg hN4 (by linarith : (0:ℝ) ≤ T - 2),
      mul_nonneg hM0 (by linarith : (0:ℝ) ≤ T)]

/-! ## J9: partial result (i) — every `δ > 1/6` -/

/-- **J9 (`rightHalf_gt_sixth`).** Zeros with `Re ρ ≥ 1/2 + δ`, `δ > 1/6`, are `O(T)`:
`σ₁ := (2/3 + (1/2 + δ))/2 ∈ (2/3, 1/2 + δ)` with M3's `meanSquareUnif_naive`. -/
theorem rightHalf_gt_sixth :
    ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T := by
  intro δ hδ
  rcases le_or_gt (1 / 2) δ with hδ2 | hδ2
  · exact ⟨0, fun T _ => by rw [NRight_eq_zero_of_half_le hδ2]; simp⟩
  · have h1 : 1 / 2 < (2 / 3 + (1 / 2 + δ)) / 2 := by linarith
    have h2 : (2 / 3 + (1 / 2 + δ)) / 2 < 1 := by linarith
    have h23 : 2 / 3 ≤ (2 / 3 + (1 / 2 + δ)) / 2 := by linarith
    have hδσ : (2 / 3 + (1 / 2 + δ)) / 2 - 1 / 2 < δ := by linarith
    exact rightHalf_of_meanSquareUnif h1 h2 (M3.meanSquareUnif_naive h23 h2) δ hδσ

/-- **J9 (`bohrLandau_gt_sixth`).** The off-line count `NOff δ 0 T` is `O(T)` for every
`δ > 1/6` (via `NOff_eq_right_add_left` and `NLeft_eq_NRight`, exactly as `bohrLandau_of_right`).
This is a genuine but weaker statement than `MNF.RH.BohrLandau` (which needs every `δ > 0`). -/
theorem bohrLandau_gt_sixth :
    ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T := by
  intro δ hδ
  obtain ⟨C, hC⟩ := rightHalf_gt_sixth δ hδ
  refine ⟨2 * C, fun T hT => ?_⟩
  rw [NOff_eq_right_add_left (by linarith) T, NLeft_eq_NRight]
  push_cast
  linarith [hC T hT]

end Zeta23.BL

end J89part


/-! # M45 — the [0,1] patch, σ = 1, and the strip mean square (M3 copy dropped) -/

section M45part

open Complex Set MeasureTheory intervalIntegral Filter Topology Asymptotics

namespace Zeta23.BL.M45

/-- Pointwise bound on the segment `σ + [0,1] I` for `0 < σ < 1`. -/
theorem norm_zeta_le_strip {σ t : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖riemannZeta ((σ:ℂ) + t * I)‖ ≤ 1 / 2 + 1 / (1 - σ) + 2 / σ := by
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hne : (σ:ℂ) + t * I ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hb := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (s := (σ:ℂ) + t * I)
    (by rw [hre]; exact h0) hne
  rw [hre] at hb
  have h1s : 1 - σ ≤ ‖1 - ((σ:ℂ) + t * I)‖ := by
    have := Complex.abs_re_le_norm (1 - ((σ:ℂ) + t * I))
    simp only [sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
      mul_one, sub_zero, add_zero] at this
    exact le_trans (le_abs_self _) this
  have hs : ‖(σ:ℂ) + t * I‖ ≤ 2 := by
    calc ‖(σ:ℂ) + t * I‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ) * I‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp [Complex.norm_real]
      _ ≤ 2 := by rw [abs_of_pos h0, abs_of_nonneg ht0]; linarith
  have e1 : 1 / ‖1 - ((σ:ℂ) + t * I)‖ ≤ 1 / (1 - σ) :=
    one_div_le_one_div_of_le (by linarith) h1s
  have e2 : ‖(σ:ℂ) + t * I‖ / σ ≤ 2 / σ := div_le_div_of_nonneg_right hs h0.le
  linarith

/-- **M4a.** The `[0,1]` patch for `0 < σ < 1`. -/
theorem meanSquare_zero_one {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∫ t in (0:ℝ)..1, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤ (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2)
    (f := fun t : ℝ => ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2) (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_zeta_le_strip h0 h1 ht.1.le ht.2) 2)
  rw [sub_zero, abs_one, mul_one] at h
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ h)

/-- For `σ ≠ 1` the integrand is continuous on all of `ℝ`. -/
lemma continuous_norm_zeta_sq {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (σ:ℂ) + t * I ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    exact hσ this
  have h2 : ContinuousAt (fun t : ℝ => (σ:ℂ) + t * I) t := by fun_prop
  have hc : ContinuousAt (riemannZeta ∘ fun t : ℝ => (σ:ℂ) + t * I) t :=
    ContinuousAt.comp (differentiableAt_riemannZeta hne).continuousAt h2
  exact hc.norm.pow 2

/-- Near `t = 0`, `‖ζ(1+it)‖² ≥ |t|⁻¹/4`. -/
lemma zeta_one_lower : ∃ δ > 0, ∀ t : ℝ, t ≠ 0 → |t| ≤ δ →
    |t|⁻¹ ≤ 4 * ‖riemannZeta (1 + t * I)‖ ^ 2 := by
  set M := ‖riemannZeta₀ 1‖ + 1 with hMdef
  have hM : 0 < M := by positivity
  have hcont : Continuous (fun t : ℝ => riemannZeta₀ (1 + t * I)) :=
    differentiable_riemannZeta₀.continuous.comp (by fun_prop)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ‖riemannZeta₀ (1 + (t:ℂ) * I)‖ < M := by
    have h := (hcont.norm.tendsto 0)
    simp only [ofReal_zero, zero_mul, add_zero] at h
    exact h.eventually_lt_const (by rw [hMdef]; linarith)
  obtain ⟨ε, hε, hεM⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min (ε / 2) (min 1 (1 / (2 * M))), by positivity, fun t ht0 htδ => ?_⟩
  have htε : |t| < ε := lt_of_le_of_lt (htδ.trans (min_le_left _ _)) (by linarith)
  have ht1 : |t| ≤ 1 := htδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htM : |t| ≤ 1 / (2 * M) := htδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hζ₀ : ‖riemannZeta₀ (1 + t * I)‖ < M := hεM (by rw [Real.dist_eq, sub_zero]; exact htε)
  have htpos : 0 < |t| := abs_pos.2 ht0
  set u := |t|⁻¹ with hu
  have hu_pos : 0 < u := inv_pos.2 htpos
  have hu1 : 1 ≤ u := by rw [hu, ← one_div]; exact one_le_one_div htpos ht1
  have htu : |t| * u = 1 := mul_inv_cancel₀ htpos.ne'
  have h2M : 2 * M ≤ u := by
    have := (le_div_iff₀ (by positivity)).1 htM
    nlinarith
  have hne : (1:ℂ) + t * I ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hζ : riemannZeta (1 + t * I) = ((t:ℂ) * I)⁻¹ + riemannZeta₀ (1 + t * I) := by
    rw [riemannZeta_eq_inv_sub_add hne, add_sub_cancel_left]
  have hninv : ‖((t:ℂ) * I)⁻¹‖ = u := by
    rw [hu, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hlow : u - M ≤ ‖riemannZeta (1 + t * I)‖ := by
    have h := norm_sub_le (((t:ℂ) * I)⁻¹ + riemannZeta₀ (1 + t * I)) (riemannZeta₀ (1 + t * I))
    rw [add_sub_cancel_right, hninv, ← hζ] at h
    linarith
  have hhalf : u / 2 ≤ ‖riemannZeta (1 + t * I)‖ := by linarith
  have hsq : (u / 2) ^ 2 ≤ ‖riemannZeta (1 + t * I)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hhalf 2
  nlinarith

/-- **M4b.** `‖ζ(1+it)‖²` is not interval-integrable on `[0,T]` for `T ≠ 0`: the simple pole at
`s = 1` gives `‖ζ(1+it)‖² ≍ t⁻²` near `t = 0`. -/
theorem not_intervalIntegrable_zeta_one_sq {T : ℝ} (hT : T ≠ 0) :
    ¬ IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 + t * I)‖ ^ 2) volume 0 T := by
  obtain ⟨δ, hδ, hbound⟩ := zeta_one_lower
  refine not_intervalIntegrable_of_sub_inv_isBigO_punctured (c := 0) ?_ hT.symm Set.left_mem_uIcc
  refine IsBigO.of_bound 4 ?_
  have h1 : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  have h2 : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ δ := by
    apply eventually_nhdsWithin_of_eventually_nhds
    exact Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun t ht => by
      rw [Real.dist_eq, sub_zero] at ht; exact ht.le⟩
  filter_upwards [h1, h2] with t ht0 htδ
  simp only [sub_zero, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  exact hbound t ht0 htδ

theorem integral_zeta_one_sq_eq_zero {T : ℝ} (hT : T ≠ 0) :
    ∫ t in (0:ℝ)..T, ‖riemannZeta (1 + t * I)‖ ^ 2 = 0 :=
  intervalIntegral.integral_undef (not_intervalIntegrable_zeta_one_sq hT)

theorem meanSquare_one : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (((1:ℝ):ℂ) + t * I)‖ ^ 2 ≤ C * T :=
  ⟨0, fun T hT => by
    rw [Complex.ofReal_one, integral_zeta_one_sq_eq_zero (by linarith), zero_mul]⟩

/-- **M5.** For `2/3 ≤ σ < 1`: `∫₀ᵀ = ∫₀¹ + ∫₁ᵀ`, the first by M4a, the second by M3's
`meanSquareUnif_explicit` (with `σ₁ := σ`); `C = (1/2 + 1/(1−σ) + 2/σ)² + C(σ)`. -/
theorem meanSquare_strip_lt_one {σ : ℝ} (h1 : 2 / 3 ≤ σ) (h2 : σ < 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  refine ⟨(1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2
    + (4 * (1 + 1 / (2 * σ - 1)) + 208 * (1 + 4 / (2 - 2 * σ)) + 17 + 4 * (1 + 1 / σ) ^ 2),
    fun T hT => ?_⟩
  have hcont := continuous_norm_zeta_sq (σ := σ) h2.ne
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 1)
    (hcont.intervalIntegrable 1 T)]
  have hA := meanSquare_zero_one (by linarith) h2
  have hC := M3.meanSquareUnif_explicit (σ₁ := σ) h1 h2 le_rfl (by linarith : 1 ≤ T)
  have hB0 : 0 ≤ (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 := sq_nonneg _
  have hBT : (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 ≤ (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 * T :=
    le_mul_of_one_le_right hB0 (by linarith)
  linarith

/-- The genuine (non-junk) statement at `σ = 1`: the mean square from `1` to `T` is `O(T)`.
This is M3's uniform bound at `σ₁ = 2/3`, `σ = 1`. -/
theorem meanSquare_one_from_one : ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
    ∫ t in (1:ℝ)..T, ‖riemannZeta (((1:ℝ):ℂ) + t * I)‖ ^ 2 ≤ C * T :=
  ⟨_, fun _ hT => M3.meanSquareUnif_explicit (σ₁ := 2 / 3) le_rfl (by norm_num)
    (by norm_num : (2:ℝ) / 3 ≤ 1) hT⟩

/-- **The target.** The verbatim sorried statement `Zeta23.BL.meanSquare_strip` of
`Zeta23/BohrLandau.lean`, with its hypothesis `1/2 < σ` restricted to `2/3 ≤ σ` (the range
reached by M3).  At `σ = 1` the statement is true only vacuously: the integrand is not
interval-integrable on `[0,T]` (`not_intervalIntegrable_zeta_one_sq`), so the Bochner interval
integral is `0` by convention; see `meanSquare_one` and, for the genuine content at `σ = 1`,
`meanSquare_one_from_one`. -/
theorem meanSquare_strip_of {σ : ℝ} (h1 : 2 / 3 ≤ σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact meanSquare_one
  · exact meanSquare_strip_lt_one h1 hlt

/-- The task's shape, with the lower threshold `σ₁` as a separate binder. -/
theorem meanSquare_strip_from {σ₁ σ : ℝ} (h0 : 2 / 3 ≤ σ₁) (h1 : σ₁ ≤ σ) (h2 : σ ≤ 1) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T :=
  meanSquare_strip_of (h0.trans h1) h2

end Zeta23.BL.M45

end M45part

/-! # Axiom audit: every theorem, lemma and definition of this file -/

#print axioms M1.log_nat_gap
#print axioms M1.mv_Icc
#print axioms M1.log_sub_log_ne_zero
#print axioms M1.term_eq
#print axioms M1.Z_eq
#print axioms M1.norm_cpow_neg_mul_I
#print axioms M1.dirichlet_meanSquare_le
#print axioms M1.cpow_neg_add_eq
#print axioms M1.norm_sq_rpow
#print axioms M1.sum_inv_le
#print axioms M1.sum_weight_le
#print axioms M1.meanValue_pow_raw
#print axioms M1.meanValue_pow
#print axioms M1.sum_Icc_rpow_le_integral
#print axioms M1.sum_rpow_neg_le
#print axioms M1.sum_Icc_rpow_le
#print axioms M1.sum_weight_le_logfree
#print axioms M1.meanValue_pow_logfree
#print axioms M1.meanValue_pow_explicit
#print axioms Zeta23.BL.M2.norm_add4_sq_le
#print axioms Zeta23.BL.M2.s_re
#print axioms Zeta23.BL.M2.s_im
#print axioms Zeta23.BL.M2.one_sub_s_re
#print axioms Zeta23.BL.M2.one_sub_s_im
#print axioms Zeta23.BL.M2.neg_s_re
#print axioms Zeta23.BL.M2.s_ne_one
#print axioms Zeta23.BL.M2.s_ne_zero
#print axioms Zeta23.BL.M2.norm_s_le
#print axioms Zeta23.BL.M2.norm_one_sub_s_ge
#print axioms Zeta23.BL.M2.rpow_sq_eq
#print axioms Zeta23.BL.M2.norm_P_le
#print axioms Zeta23.BL.M2.norm_P_le'
#print axioms Zeta23.BL.M2.norm_Q_le
#print axioms Zeta23.BL.M2.norm_Q_le'
#print axioms Zeta23.BL.M2.norm_R_le_core
#print axioms Zeta23.BL.M2.norm_R_le
#print axioms Zeta23.BL.M2.norm_R_le_uniform
#print axioms Zeta23.BL.M2.norm_R_le'
#print axioms Zeta23.BL.M2.zeta_eq_four_terms
#print axioms Zeta23.BL.M2.zeta_sub_sum_le
#print axioms Zeta23.BL.M2.norm_zeta_sq_le
#print axioms Zeta23.BL.M2.norm_zeta_sq_le'
#print axioms Zeta23.BL.M2.one_div_cpow_eq_rpow_mul
#print axioms Zeta23.BL.M2.range_sum_eq_Icc
#print axioms Zeta23.BL.M2.range_sum_eq_twist
#print axioms Zeta23.BL.M2.integral_range_sq_eq_Icc
#print axioms M3a.sum_Icc_one_eq
#print axioms M3a.antitoneOn_rpow_Icc
#print axioms M3a.sum_Ico_rpow_succ_le_integral
#print axioms M3a.sum_Icc_rpow_le
#print axioms M3a.sum_Icc_rpow_le_mul
#print axioms M3a.sum_Icc_rpow_le_tsum
#print axioms M3a.sum_Icc_rpow_neg_le_tsum_one_div
#print axioms M3a.sum_Icc_rpow_mul_log_le
#print axioms M3a.sum_Icc_rpow_mul_log_le_of_sigma
#print axioms M3a.sum_Icc_rpow_le_of_sigma
#print axioms Zeta23.BL.M3.Dpoly
#print axioms Zeta23.BL.M3.continuous_Dpoly
#print axioms Zeta23.BL.M3.meanValue_Dpoly
#print axioms Zeta23.BL.M3.norm_zeta_sq_le_unif
#print axioms Zeta23.BL.M3.continuousOn_norm_zeta_sq
#print axioms Zeta23.BL.M3.integral_inv_sq_one
#print axioms Zeta23.BL.M3.integral_bound_abstract
#print axioms Zeta23.BL.M3.meanSquare_param
#print axioms Zeta23.BL.M3.N_choice
#print axioms Zeta23.BL.M3.rpow_neg_le_of_choice
#print axioms Zeta23.BL.M3.rpow_pos_le_of_choice
#print axioms Zeta23.BL.M3.meanSquareUnif_explicit
#print axioms Zeta23.BL.M3.MeanSquareUnifFrom
#print axioms Zeta23.BL.M3.meanSquareUnif_naive
#print axioms Zeta23.BL.M3.meanSquareUnif_task
#print axioms Zeta23.BL.NRight_eq_zero_of_half_le
#print axioms Zeta23.BL.MNF_zerosIn_union
#print axioms Zeta23.BL.NRight_add
#print axioms Zeta23.BL.NRight_sub_eq
#print axioms Zeta23.BL.NRight_mono
#print axioms Zeta23.BL.zeta_order_eq_zero_of_ne_zero
#print axioms Zeta23.BL.divisor_riemannZeta_eq_int
#print axioms Zeta23.BL.divisor_riemannZeta_eq
#print axioms Zeta23.BL.sum_zeta_order_le_finsum_divisor
#print axioms Zeta23.BL.finsum_divisor_riemannZeta_eq
#print axioms Zeta23.BL.finsum_divisor_riemannZeta_eq_zerosIn
#print axioms Zeta23.BL.Rout
#print axioms Zeta23.BL.rin
#print axioms Zeta23.BL.hwin
#print axioms Zeta23.BL.mem_closedBall_iff_sq
#print axioms Zeta23.BL.abs_re_im_sub_le_of_mem_closedBall
#print axioms Zeta23.BL.bounds_of_mem_closedBall_two
#print axioms Zeta23.BL.one_notMem_closedBall_two
#print axioms Zeta23.BL.re_ge_of_mem_closedBall_Rout
#print axioms Zeta23.BL.outer_disc_facts
#print axioms Zeta23.BL.geom_facts
#print axioms Zeta23.BL.one_notMem_closedBall_two_add
#print axioms Zeta23.BL.one_notMem_sphere_two_add
#print axioms Zeta23.BL.neg_log_norm_riemannZeta_two_add_le
#print axioms Zeta23.BL.count_disc_le
#print axioms Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor
#print axioms Zeta23.BL.count_finset_le
#print axioms Zeta23.BL.Lz
#print axioms Zeta23.BL.Lz_nonneg
#print axioms Zeta23.BL.log_le_half_log_one_add_sq
#print axioms Zeta23.BL.log_norm_le_Lz
#print axioms Zeta23.BL.continuousOn_Lz
#print axioms Zeta23.BL.circleIntegrable_Lz
#print axioms Zeta23.BL.circleAverage_log_norm_le_Lz
#print axioms Zeta23.BL.concaveOn_half_log_one_add
#print axioms Zeta23.BL.circleAverage_Lz_le
#print axioms Zeta23.BL.count_finset_le_log_meanSq
#print axioms Zeta23.BL.closedBall_Rout_subset
#print axioms Zeta23.BL.count_window_le
#print axioms Zeta23.BL.count_window_le_log_meanSq
#print axioms Zeta23.BL.circleAverage_log_le_Lz
#print axioms Zeta23.BL.circleMap_two_add
#print axioms Zeta23.BL.circleMap_two_add_ne_one
#print axioms Zeta23.BL.continuousOn_Lz_circleMap
#print axioms Zeta23.BL.integrableOn_Lz_circleMap_prod
#print axioms Zeta23.BL.integrable_Lz_circleMap_prod_restrict
#print axioms Zeta23.BL.intervalIntegrable_circleAverage_Lz
#print axioms Zeta23.BL.integral_circleAverage_Lz_eq_swap
#print axioms Zeta23.BL.Lz_le_half_sq
#print axioms Zeta23.BL.segment_mapsTo_ne_one
#print axioms Zeta23.BL.intervalIntegrable_Lz_segment
#print axioms Zeta23.BL.intervalIntegrable_normSq_zeta_segment
#print axioms Zeta23.BL.integral_Lz_circle_le
#print axioms Zeta23.BL.integral_circleAverage_Lz_le
#print axioms Zeta23.BL.count_le_integral
#print axioms Zeta23.BL.count_le_meanSquare
#print axioms Zeta23.BL.count_le_meanSquare'
#print axioms Zeta23.BL.tsum_one_div_rpow_anti
#print axioms Zeta23.BL.meanSquare_of_gt_one
#print axioms Zeta23.BL.meanSquare_hyp_extend
#print axioms Zeta23.BL.rightHalf_of_meanSquareUnif
#print axioms Zeta23.BL.rightHalf_gt_sixth
#print axioms Zeta23.BL.bohrLandau_gt_sixth
#print axioms Zeta23.BL.M45.norm_zeta_le_strip
#print axioms Zeta23.BL.M45.meanSquare_zero_one
#print axioms Zeta23.BL.M45.continuous_norm_zeta_sq
#print axioms Zeta23.BL.M45.zeta_one_lower
#print axioms Zeta23.BL.M45.not_intervalIntegrable_zeta_one_sq
#print axioms Zeta23.BL.M45.integral_zeta_one_sq_eq_zero
#print axioms Zeta23.BL.M45.meanSquare_one
#print axioms Zeta23.BL.M45.meanSquare_strip_lt_one
#print axioms Zeta23.BL.M45.meanSquare_one_from_one
#print axioms Zeta23.BL.M45.meanSquare_strip_of
#print axioms Zeta23.BL.M45.meanSquare_strip_from
