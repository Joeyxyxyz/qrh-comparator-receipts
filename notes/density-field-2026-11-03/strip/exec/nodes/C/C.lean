/-
Density/Centre — node C of STRIP_PLAN (items C1, C1', C2a, C2b, C2c, C2d).

Analyticity of the Möbius mollifier `Mx` and of the mollified zeta `fz = ζ · Mx`, and the
bounds at the Jensen-disc centre line `Re s ≥ 2`:
  * C1   `analyticOnNhd_Mx`           — `Mx X` is entire
  * C1'  `analyticOnNhd_fz`, `continuousOn_fz` — `fz X` analytic / continuous off `s = 1`
  * C2a  `tail_inv_sq_le`             — `Σ_{n > X} 1/n² ≤ 1/X`
  * C2b  `fz_sub_one_eq`              — `fz X s − 1 = −ζ(s)·Σ_{n > X} μ(n) n^{−s}` for `Re s > 1`
  * C2c  `norm_fz_sub_one_le`         — `‖fz X s − 1‖ ≤ (π²/6)·(1/X)` for `Re s ≥ 2`
  * C2d  `fz_lower_two`, `neg_log_norm_fz_two_le`, `log_norm_fz_le_of_two_le_re`,
         `norm_sq_fz_le_of_two_le_re`  — the centre-line bounds used by G5/G7/A0

The DEFINITIONS block below is the frozen Stage-0 block of STRIP_PLAN.md, copied verbatim
(the single `open MNF.RH` before it only resolves `zeta_order`; it is not part of any body).
-/
import Zeta23.BL.BohrLandauClosure

open MNF.RH
open scoped LSeries.notation

namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius

/-- Möbius mollifier `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`. -/
noncomputable def Mx (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)
/-- the mollified zeta `f = ζ · M_X`. -/
noncomputable def fz (X : ℕ) (s : ℂ) : ℂ := riemannZeta s * Mx X s
/-- coefficient of `m^{-s}` in `S N · M_X`. -/
def cm (N X m : ℕ) : ℤ := ∑ d ∈ m.divisors.filter (· ≤ X), if m / d ≤ N then μ d else 0
/-- number of divisors of `m` that are `≤ X`. -/
def dX (X m : ℕ) : ℕ := (m.divisors.filter (· ≤ X)).card
/-- ε-majorant of `log ‖f‖` (replaces the tree's `Lz`, whose `1 +` kills every saving). -/
noncomputable def Leps (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ := (1 / 2) * Real.log (ε ^ 2 + ‖f z‖ ^ 2)
/-- zeros with `σ ≤ Re ρ`, `T₁ < Im ρ ≤ T₂`, with multiplicity (window form of `NRight`). -/
noncomputable def NSigma (σ T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ MNF.RH.zerosIn T₁ T₂ ∩ {ρ | σ ≤ ρ.re}, zeta_order ρ

/-! ### C1 — the mollifier is entire -/

/-- C1: `Mx X` is analytic on all of `ℂ` (a finite sum of `c · n^{-s}`, `n ≥ 1`). -/
theorem analyticOnNhd_Mx (X : ℕ) : AnalyticOnNhd ℂ (Mx X) Set.univ := by
  have h : ∀ n ∈ Icc 1 X,
      AnalyticOnNhd ℂ (fun s : ℂ => ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)) Set.univ := by
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    refine analyticOnNhd_const.mul ?_
    refine AnalyticOnNhd.cpow analyticOnNhd_const analyticOnNhd_id.neg ?_
    intro z _
    exact Complex.natCast_mem_slitPlane.mpr hn0
  exact Finset.analyticOnNhd_fun_sum (Icc 1 X) h

/-! ### C1' — `fz` off the pole -/

/-- C1': `fz X = ζ · Mx X` is analytic on any set avoiding `1`. -/
theorem analyticOnNhd_fz {X : ℕ} {S : Set ℂ} (hS : (1:ℂ) ∉ S) : AnalyticOnNhd ℂ (fz X) S :=
  (Zeta23.RvM.analyticOnNhd_riemannZeta hS).mul ((analyticOnNhd_Mx X).mono (Set.subset_univ S))

/-- C1': `fz X` is continuous on any set avoiding `1`. -/
theorem continuousOn_fz {X : ℕ} {U : Set ℂ} (hU : (1:ℂ) ∉ U) : ContinuousOn (fz X) U :=
  (analyticOnNhd_fz hU).continuousOn

/-! ### C2a — the tail of `Σ 1/n²` -/

/-- C2a: `Σ_{n > X} 1/n² ≤ 1/X` (telescoping `1/n² ≤ 1/(n−1) − 1/n`). -/
theorem tail_inv_sq_le {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (if X < n then 1 / (n:ℝ) ^ 2 else 0) ≤ 1 / (X:ℝ) := by
  set b : ℕ → ℝ := fun n => if X < n then 1 / (n:ℝ) ^ 2 else 0 with hb
  show ∑' n, b n ≤ 1 / (X:ℝ)
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    simp only [hb]
    split_ifs <;> positivity
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  -- partial sums: `Σ_{i < X+1+M} b i ≤ 1/X − 1/(X+M)`
  have key : ∀ M : ℕ, ∑ i ∈ range (X + 1 + M), b i ≤ 1 / X - 1 / ((X:ℝ) + M) := by
    intro M
    induction M with
    | zero =>
      have h0 : ∑ i ∈ range (X + 1 + 0), b i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        simp only [hb]
        rw [if_neg (by omega)]
      rw [h0]
      simp
    | succ M ih =>
      rw [show X + 1 + (M + 1) = (X + 1 + M) + 1 by ring, Finset.sum_range_succ]
      have hterm : b (X + 1 + M) = 1 / ((X:ℝ) + M + 1) ^ 2 := by
        simp only [hb]
        rw [if_pos (by omega)]
        push_cast
        ring
      rw [hterm]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M:ℝ) + 1 := by push_cast; ring
      rw [hcast, ← add_assoc]
      have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
      have hk : (1:ℝ) ≤ (X:ℝ) + M := by linarith
      have hpos : 0 < (X:ℝ) + M := by linarith
      have hpos1 : 0 < (X:ℝ) + M + 1 := by linarith
      have h1 : 1 / ((X:ℝ) + M) - 1 / ((X:ℝ) + M + 1)
          = 1 / (((X:ℝ) + M) * ((X:ℝ) + M + 1)) := by
        field_simp
        ring
      have hineq : 1 / ((X:ℝ) + M + 1) ^ 2 ≤ 1 / ((X:ℝ) + M) - 1 / ((X:ℝ) + M + 1) := by
        rw [h1]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
  refine Real.tsum_le_of_sum_range_le hb0 (fun n => ?_)
  calc ∑ i ∈ range n, b i ≤ ∑ i ∈ range (X + 1 + n), b i :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
          (fun i _ _ => hb0 i)
    _ ≤ 1 / X - 1 / ((X:ℝ) + n) := key n
    _ ≤ 1 / X := by
        have : 0 ≤ 1 / ((X:ℝ) + n) := by positivity
        linarith

/-! ### C2b — the Dirichlet-series identity for `fz − 1` -/

set_option linter.unusedVariables false in
/-- C2b: for `Re s > 1`, `fz X s − 1 = −ζ(s)·Σ_{n > X} μ(n) n^{−s}`
(from `ζ(s)·L(μ, s) = 1`, splitting the absolutely convergent `L(μ, s)` at `X`).
The hypothesis `hX` is kept for the plan's statement shape; the identity does not use it. -/
theorem fz_sub_one_eq {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 1 < s.re) :
    fz X s - 1 = -(riemannZeta s * ∑' n : ℕ,
      (if X < n then ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) else 0)) := by
  -- ζ(s) · L(μ, s) = 1
  have hmul : riemannZeta s * L ↗μ s = 1 := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rwa [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  have hterm : ∀ n : ℕ, LSeries.term (↗μ) s n = ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) :=
    fun n => LSeries.term_def₀ (by simp) s n
  set g : ℕ → ℂ := fun n => if X < n then ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) else 0 with hg
  set h : ℕ → ℂ := fun n => if X < n then 0 else ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) with hh
  have hsplit : ∀ n, LSeries.term (↗μ) s n = h n + g n := by
    intro n
    simp only [hterm, hg, hh]
    split_ifs <;> simp
  have hsum : Summable (LSeries.term (↗μ) s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hhs : Summable h := by
    refine summable_of_ne_finset_zero (s := range (X + 1)) (fun n hn => ?_)
    rw [Finset.mem_range] at hn
    simp only [hh]
    rw [if_pos (by omega)]
  have hgs : Summable g := by
    have hge : g = fun n => LSeries.term (↗μ) s n - h n := by
      funext n
      rw [hsplit n]
      ring
    rw [hge]
    exact hsum.sub hhs
  have hhead : ∑' n, h n = Mx X s := by
    rw [tsum_eq_sum (s := range (X + 1)) (fun n hn => by
      rw [Finset.mem_range] at hn
      simp only [hh]
      rw [if_pos (by omega)])]
    unfold Mx
    rw [← Finset.sum_subset (s₁ := Icc 1 X) (s₂ := range (X + 1)) (f := h) ?_ ?_]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      simp only [hh]
      rw [if_neg (by omega)]
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro n hn hn'
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc] at hn'
      have hn0 : n = 0 := by omega
      subst hn0
      simp only [hh]
      split_ifs <;> simp
  have hL : L ↗μ s = Mx X s + ∑' n, g n := by
    unfold LSeries
    rw [tsum_congr hsplit, hhs.tsum_add hgs, hhead]
  calc fz X s - 1 = riemannZeta s * Mx X s - riemannZeta s * L ↗μ s := by
        rw [hmul]
        rfl
    _ = -(riemannZeta s * ∑' n, g n) := by
        rw [hL]
        ring

/-! ### C2c — the centre bound `‖fz − 1‖ ≤ (π²/6)/X` -/

/-- C2c: for `Re s ≥ 2`, `‖fz X s − 1‖ ≤ (π²/6)·(1/X)`
(`‖ζ‖ ≤ π²/6`, `|μ| ≤ 1`, `‖n^{−s}‖ ≤ n^{−2}`, and C2a). -/
theorem norm_fz_sub_one_le {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖fz X s - 1‖ ≤ Real.pi ^ 2 / 6 * (1 / X) := by
  have hs1 : 1 < s.re := by linarith
  rw [fz_sub_one_eq hX hs1, norm_neg, norm_mul]
  set g : ℕ → ℂ := fun n => if X < n then ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) else 0 with hg
  set b : ℕ → ℝ := fun n => if X < n then 1 / (n:ℝ) ^ 2 else 0 with hb
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    simp only [hb]
    split_ifs <;> positivity
  have hle : ∀ n, ‖g n‖ ≤ b n := by
    intro n
    simp only [hg, hb]
    split_ifs with hn
    · have hn0 : 0 < n := by omega
      rw [norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
      have h1 : |((μ n : ℤ) : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := n)
        exact_mod_cast this
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
      have h2 : (n:ℝ) ^ (-s.re) ≤ (n:ℝ) ^ (-(2:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have h3 : (n:ℝ) ^ (-(2:ℝ)) = 1 / (n:ℝ) ^ 2 := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div]
      rw [h3] at h2
      have h4 : 0 ≤ (n:ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc |((μ n : ℤ) : ℝ)| * (n:ℝ) ^ (-s.re) ≤ 1 * (1 / (n:ℝ) ^ 2) :=
            mul_le_mul h1 h2 h4 zero_le_one
        _ = 1 / (n:ℝ) ^ 2 := one_mul _
    · simp
  have hbs : Summable b := by
    refine Summable.of_nonneg_of_le hb0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simp only [hb]
    split_ifs
    · exact le_rfl
    · positivity
  have hgn : Summable (fun n => ‖g n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hbs
  have htail : ‖∑' n, g n‖ ≤ 1 / (X:ℝ) :=
    calc ‖∑' n, g n‖ ≤ ∑' n, ‖g n‖ := norm_tsum_le_tsum_norm hgn
      _ ≤ ∑' n, b n := hgn.tsum_le_tsum hle hbs
      _ ≤ 1 / (X:ℝ) := tail_inv_sq_le hX
  exact mul_le_mul (Zeta23.RvM.norm_riemannZeta_le_of_two_le_re hs) htail (norm_nonneg _)
    (by positivity)

/-! ### C2d — the centre-line bounds for `X ≥ 4` -/

/-- `π² < 10` (from `π < 3.15`). -/
lemma pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have h := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

/-- For `X ≥ 4`: `(π²/6)·(1/X) ≤ π²/24`. -/
lemma pi_sq_div_six_div_le {X : ℕ} (hX : 4 ≤ X) :
    Real.pi ^ 2 / 6 * (1 / X) ≤ Real.pi ^ 2 / 24 := by
  have hX' : (4:ℝ) ≤ X := by exact_mod_cast hX
  have h1 : 1 / (X:ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hX'
  calc Real.pi ^ 2 / 6 * (1 / X) ≤ Real.pi ^ 2 / 6 * (1 / 4) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.pi ^ 2 / 24 := by ring

/-- `‖fz X s‖ ≤ 1 + ‖fz X s − 1‖`. -/
lemma norm_fz_le_one_add {X : ℕ} (s : ℂ) : ‖fz X s‖ ≤ 1 + ‖fz X s - 1‖ := by
  calc ‖fz X s‖ = ‖(fz X s - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖fz X s - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    _ = 1 + ‖fz X s - 1‖ := by rw [norm_one]; ring

/-- `1 − ‖fz X s − 1‖ ≤ ‖fz X s‖`. -/
lemma one_sub_norm_le_norm_fz {X : ℕ} (s : ℂ) : 1 - ‖fz X s - 1‖ ≤ ‖fz X s‖ := by
  have h4 := norm_sub_norm_le (1:ℂ) (fz X s)
  rw [norm_sub_rev, norm_one] at h4
  linarith

/-- C2d: `‖fz X (2 + it)‖ ≥ 1/2` for `X ≥ 4` (since `π²/24 < 1/2`). -/
theorem fz_lower_two {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : (1/2 : ℝ) ≤ ‖fz X (2 + t * I)‖ := by
  have hre : (2 + t * I : ℂ).re = 2 := by simp
  have h := norm_fz_sub_one_le (X := X) (by omega) (s := 2 + t * I) hre.symm.le
  have h2 := pi_sq_div_six_div_le hX
  have h3 := pi_sq_lt_ten
  have h4 := one_sub_norm_le_norm_fz (X := X) (2 + t * I)
  linarith

/-- C2d: `−log ‖fz X (2 + it)‖ ≤ π²/(3X)` for `X ≥ 4`
(`−log(1 − x) ≤ 2x` on `[0, 1/2]`, with `x = (π²/6)/X ≤ π²/24`). -/
theorem neg_log_norm_fz_two_le {X : ℕ} (hX : 4 ≤ X) (t : ℝ) :
    -Real.log ‖fz X (2 + t * I)‖ ≤ Real.pi ^ 2 / (3 * X) := by
  have hre : (2 + t * I : ℂ).re = 2 := by simp
  have h := norm_fz_sub_one_le (X := X) (by omega) (s := 2 + t * I) hre.symm.le
  have h2 := pi_sq_div_six_div_le hX
  have h3 := pi_sq_lt_ten
  have h4 := one_sub_norm_le_norm_fz (X := X) (2 + t * I)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.pi ^ 2 / 6 * (1 / (X:ℝ)) := ⟨_, rfl⟩
  rw [← hx] at h h2
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxh : x ≤ 1 / 2 := by linarith
  have hpos : 0 < 1 - x := by linarith
  have hlog : Real.log (1 - x) ≤ Real.log ‖fz X (2 + t * I)‖ :=
    Real.log_le_log hpos (by linarith)
  have hlog2 : -Real.log (1 - x) ≤ 2 * x := by
    rw [← Real.log_inv]
    have h5 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    linarith
  have h2x : 2 * x = Real.pi ^ 2 / (3 * X) := by
    rw [hx]
    ring
  linarith

/-- C2d: `log ‖fz X s‖ ≤ π²/(6X)` for `Re s ≥ 2`, `X ≥ 4` (`log(1 + x) ≤ x`). -/
theorem log_norm_fz_le_of_two_le_re {X : ℕ} (hX : 4 ≤ X) {s : ℂ} (hs : 2 ≤ s.re) :
    Real.log ‖fz X s‖ ≤ Real.pi ^ 2 / (6 * X) := by
  have h := norm_fz_sub_one_le (X := X) (by omega) hs
  have h2 := pi_sq_div_six_div_le hX
  have h3 := pi_sq_lt_ten
  have h4 := one_sub_norm_le_norm_fz (X := X) s
  have h5 := norm_fz_le_one_add (X := X) s
  have hpos : 0 < ‖fz X s‖ := by linarith
  have h6 := Real.log_le_sub_one_of_pos hpos
  have h7 : Real.pi ^ 2 / 6 * (1 / X) = Real.pi ^ 2 / (6 * X) := by ring
  linarith

/-- C2d: `‖fz X s‖² ≤ 1 + π²/(2X)` for `Re s ≥ 2`, `X ≥ 4` (`(1 + x)² ≤ 1 + 3x` on `[0, 1]`). -/
theorem norm_sq_fz_le_of_two_le_re {X : ℕ} (hX : 4 ≤ X) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖fz X s‖ ^ 2 ≤ 1 + Real.pi ^ 2 / (2 * X) := by
  have h := norm_fz_sub_one_le (X := X) (by omega) hs
  have h2 := pi_sq_div_six_div_le hX
  have h3 := pi_sq_lt_ten
  have h5 := norm_fz_le_one_add (X := X) s
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.pi ^ 2 / 6 * (1 / (X:ℝ)) := ⟨_, rfl⟩
  rw [← hx] at h h2
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by linarith
  have hnn : 0 ≤ ‖fz X s‖ := norm_nonneg _
  have hle : ‖fz X s‖ ≤ 1 + x := by linarith
  have hsq : ‖fz X s‖ * ‖fz X s‖ ≤ (1 + x) * (1 + x) :=
    mul_le_mul hle hle hnn (by linarith)
  have h3x : 3 * x = Real.pi ^ 2 / (2 * X) := by
    rw [hx]
    ring
  nlinarith

end Zeta23.Density

#print axioms Zeta23.Density.analyticOnNhd_Mx
#print axioms Zeta23.Density.analyticOnNhd_fz
#print axioms Zeta23.Density.continuousOn_fz
#print axioms Zeta23.Density.tail_inv_sq_le
#print axioms Zeta23.Density.fz_sub_one_eq
#print axioms Zeta23.Density.norm_fz_sub_one_le
#print axioms Zeta23.Density.fz_lower_two
#print axioms Zeta23.Density.neg_log_norm_fz_two_le
#print axioms Zeta23.Density.log_norm_fz_le_of_two_le_re
#print axioms Zeta23.Density.norm_sq_fz_le_of_two_le_re
