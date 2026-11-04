import Mathlib

/-!
# M3a — partial sums of `n ^ a`

Plan node M3a of BOHR_LANDAU_PLAN.md:
* `sum_Icc_rpow_le` : for `-1 < a ≤ 0`, `∑ n ∈ Icc 1 N, n^a ≤ 1 + N^(a+1)/(a+1)`;
* `sum_Icc_rpow_le_mul` : the same with explicit constant, `≤ (1 + 1/(a+1)) * N^(a+1)` (`1 ≤ N`);
* `sum_Icc_rpow_le_tsum` / `sum_Icc_rpow_neg_le_tsum_one_div` : for `a < -1` (resp. `1 < p`) the
  partial sums are bounded by the convergent series;
* `sum_Icc_rpow_mul_log_le` / `sum_Icc_rpow_mul_log_le_of_sigma` : the mixed sum with `log n + 1`.
-/

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

#print axioms M3a.sum_Icc_rpow_le
#print axioms M3a.sum_Icc_rpow_le_mul
#print axioms M3a.sum_Icc_rpow_le_tsum
#print axioms M3a.sum_Icc_rpow_neg_le_tsum_one_div
#print axioms M3a.sum_Icc_rpow_mul_log_le
#print axioms M3a.sum_Icc_rpow_mul_log_le_of_sigma
#print axioms M3a.sum_Icc_rpow_le_of_sigma
