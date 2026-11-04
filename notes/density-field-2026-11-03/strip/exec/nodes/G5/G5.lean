/-
G5.lean — node G5 of STRIP_PLAN (items G5, G5': the per-`t` count on discs for `fz`).

  * G5   `count_finset_le_fz`  — Jensen on `closedBall (2 + tI) r ⊂ closedBall (2 + tI) R`,
         `t ≥ 3`, `0 < r < R < 3`, for the mollified function `fz X = ζ · M_X`, `X ≥ 4`,
         with the centre term `−log ‖fz X (2 + tI)‖ ≤ π²/(3X)` (C2d) in place of `log 3`.
  * G5'  `count_window_le_fz`  — the window form, `r = rin σ₁ δ`, `R = Rout σ₁`.
  Also `count_disc_le_fz` (divisor form, the analogue of `Zeta23.BL.count_disc_le`).

Pattern: `Zeta23.BL.count_disc_le → count_finset_le → count_window_le`
(`Zeta23/BL/BohrLandauPartial.lean`), with `sum_divisor_mul_log_le` (`Zeta23/BL/JensenDisc.lean`).

Scratch files cannot be imported, so the upstream items this node uses are copied verbatim
(same names and statements as in the sibling nodes C and G4, so the merger can drop either copy):
  from C : `analyticOnNhd_Mx` (C1), `analyticOnNhd_fz` (C1'), `tail_inv_sq_le` (C2a),
           `fz_sub_one_eq` (C2b), `norm_fz_sub_one_le` (C2c), the helpers `pi_sq_lt_ten`,
           `pi_sq_div_six_div_le`, `norm_fz_le_one_add`, `one_sub_norm_le_norm_fz`, and
           `fz_lower_two`, `neg_log_norm_fz_two_le` (C2d);
  from G4: `sum_Icc_two_inv_mul_sub_one`, `norm_moebius_mul_cpow_le`, `Mx_eq_one_add`,
           `Mx_ne_zero_of_le_re` (G4a), `analyticOrderAt_Mx_ne_top` (G4b),
           `zeta_order_le_divisor_fz` (G4), `finset_sum_zeta_order_le_finsum_divisor_fz` (G4').

The DEFINITIONS block below is the frozen Stage-0 block of STRIP_PLAN.md, copied verbatim
(the `open`s before it only resolve `zeta_order`, `circleAverage`, `Rout/rin/hwin`;
they are not part of any definition body).  No `sorry`.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

open MNF.RH
open Real (circleAverage)
open Zeta23.BL (Rout rin hwin)

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

/-! ## END of the frozen DEFINITIONS block -/

/-! ## Copies from node C (C1, C1', C2a, C2b, C2c, C2d) -/

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

/-- C1': `fz X = ζ · Mx X` is analytic on any set avoiding `1`. -/
theorem analyticOnNhd_fz {X : ℕ} {S : Set ℂ} (hS : (1:ℂ) ∉ S) : AnalyticOnNhd ℂ (fz X) S :=
  (Zeta23.RvM.analyticOnNhd_riemannZeta hS).mul ((analyticOnNhd_Mx X).mono (Set.subset_univ S))

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

/- `open scoped LSeries.notation` is restricted to C2b: that scope also makes `δ` a token
(`LSeries.delta`), which would break the binder `{σ₁ δ : ℝ}` of G5'. -/
set_option linter.unusedVariables false in
open scoped LSeries.notation in
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

/-! ## Copies from node G4 (G4a, G4b, G4, G4' and their helpers) -/

/-- Telescoping: `∑_{n=2}^{X} 1/(n(n−1)) = 1 − 1/X` for `X ≥ 1`. -/
theorem sum_Icc_two_inv_mul_sub_one {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 2 X, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (X : ℝ) := by
  induction X, hX using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty_of_lt (by norm_num)]; simp
  | succ X hX ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
    have hX1 : (X : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (1 : ℝ) / (((X + 1 : ℕ) : ℝ) * (((X + 1 : ℕ) : ℝ) - 1))
        = 1 / (X : ℝ) - 1 / ((X : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ hX0 hX1]
      congr 1 <;> ring
    rw [h3]
    push_cast
    ring

/-- One term of `M_X − 1`: for `n ≥ 2` and `Re s ≥ 3`, `‖μ(n) n^{-s}‖ ≤ 1/(n(n−1))`. -/
theorem norm_moebius_mul_cpow_le {n : ℕ} (hn : 2 ≤ n) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [norm_natCast_cpow_of_pos hn0, Complex.neg_re]
    calc (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = 1 / (n : ℝ) ^ 2 := by rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
      _ ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          apply one_div_le_one_div_of_le
          · nlinarith
          · nlinarith
  calc ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ = ‖((μ n : ℤ) : ℂ)‖ * ‖(n : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ 1 * (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        mul_le_mul hμ hpow (norm_nonneg _) zero_le_one
    _ = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := one_mul _

/-- `M_X(s) = 1 + ∑_{n=2}^{X} μ(n) n^{-s}` for `X ≥ 1` (the `n = 1` term is `1`). -/
theorem Mx_eq_one_add {X : ℕ} (hX : 1 ≤ X) (s : ℂ) :
    Mx X s = 1 + ∑ n ∈ Icc 2 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s) := by
  unfold Mx
  have h1 : (1 : ℕ) ∈ Icc 1 X := Finset.mem_Icc.2 ⟨le_rfl, hX⟩
  rw [← Finset.add_sum_erase _ _ h1]
  have he : (Icc 1 X).erase 1 = Icc 2 X := by
    ext n; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [he]
  simp

/-- G4a. `M_X(s) ≠ 0` for `Re s ≥ 3` (and `X ≥ 1`): `‖M_X(s) − 1‖ ≤ 1 − 1/X < 1`. -/
theorem Mx_ne_zero_of_le_re {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 3 ≤ s.re) : Mx X s ≠ 0 := by
  rw [Mx_eq_one_add hX s]
  intro h0
  have hle : ‖∑ n ∈ Icc 2 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ 1 - 1 / (X : ℝ) := by
    calc ‖∑ n ∈ Icc 2 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Icc 2 X, ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 2 X, 1 / ((n : ℝ) * ((n : ℝ) - 1)) :=
          Finset.sum_le_sum fun n hn => norm_moebius_mul_cpow_le (Finset.mem_Icc.1 hn).1 hs
      _ = 1 - 1 / (X : ℝ) := sum_Icc_two_inv_mul_sub_one hX
  have heq : ∑ n ∈ Icc 2 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s) = -1 := by
    linear_combination h0
  rw [heq, norm_neg, norm_one] at hle
  have hXpos : (0 : ℝ) < 1 / (X : ℝ) := one_div_pos.2 (Nat.cast_pos.2 hX)
  linarith

/-- G4b. `M_X` is not locally identically zero anywhere: it is entire, `ℂ` is connected, and
`M_X(3) ≠ 0` (G4a). -/
theorem analyticOrderAt_Mx_ne_top {X : ℕ} (hX : 1 ≤ X) (z : ℂ) :
    analyticOrderAt (Mx X) z ≠ ⊤ := by
  refine (analyticOnNhd_Mx X).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (3 : ℂ)) (Set.mem_univ z) ?_
  rw [((analyticOnNhd_Mx X) 3 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
    (Mx_ne_zero_of_le_re hX (by simp))]
  exact ENat.zero_ne_top

/-- G4. On a closed ball not containing `1`, the multiplicity of `ρ` as a zero of `ζ` is at most
the divisor of `fz X = ζ · M_X` at `ρ`: `ord_ρ(ζ · M_X) = ord_ρ ζ + ord_ρ M_X` with both orders
finite (`Zeta23.analyticOrderAt_riemannZeta_ne_top`, G4b), and `ord_ρ M_X ≥ 0`. -/
theorem zeta_order_le_divisor_fz {X : ℕ} (hX : 1 ≤ X) {c : ℂ} {r : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    (zeta_order ρ : ℤ) ≤ MeromorphicOn.divisor (fz X) (closedBall c r) ρ := by
  have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hρ)
  have hζ : AnalyticAt ℂ riemannZeta ρ := Zeta23.RvM.analyticOnNhd_riemannZeta h1 ρ hρ
  have hM : AnalyticAt ℂ (Mx X) ρ := analyticOnNhd_Mx X ρ (Set.mem_univ ρ)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (analyticOnNhd_fz h1) hρ]
  have hmul : analyticOrderAt (fz X) ρ
      = analyticOrderAt riemannZeta ρ + analyticOrderAt (Mx X) ρ :=
    analyticOrderAt_mul hζ hM
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_Mx_ne_top hX ρ)
  unfold zeta_order
  rw [hmul, ← ha, ← hb, ENat.toNat_natCast, ← Nat.cast_add, ENat.map_natCast,
    WithTop.untop₀_coe]
  exact_mod_cast Nat.le_add_right a b

/-- G4'. A finite set of nontrivial zeros inside the ball contributes at most the full divisor
sum of `fz X` (pattern: `Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor`, with `≤` from G4
in place of `=`). -/
theorem finset_sum_zeta_order_le_finsum_divisor_fz {X : ℕ} (hX : 1 ≤ X) {c : ℂ} {r : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall c r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ))
      ≤ ∑ᶠ u, (MeromorphicOn.divisor (fz X) (closedBall c r) u : ℝ) := by
  set D : ℂ → ℝ := fun u => (MeromorphicOn.divisor (fz X) (closedBall c r) u : ℝ) with hD
  have hf : AnalyticOnNhd ℂ (fz X) (closedBall c r) := analyticOnNhd_fz h1
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor (fz X) (closedBall c r)).finiteSupport (isCompact_closedBall ..)
      |>.subset fun _ _ ↦ (by simp_all)
  have hnn : ∀ u, 0 ≤ D u := fun u => by
    simp only [hD]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
  have h1' : ∑ ρ ∈ S, (zeta_order ρ : ℝ) ≤ ∑ ρ ∈ S, D ρ := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    simp only [hD]
    exact_mod_cast zeta_order_le_divisor_fz hX h1 (hS ρ hρ).2
  have h2 : ∑ᶠ u, D u = ∑ u ∈ S ∪ hfin.toFinset, D u :=
    finsum_eq_sum_of_support_subset D (by
      intro u hu
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inr hu)
  rw [h2]
  exact h1'.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun u _ _ => hnn u))

/-! ## G5 — the per-`t` count on discs for `fz` -/

/-- The centre of the Jensen disc is not a zero of `fz X` (`‖fz X (2 + it)‖ ≥ 1/2`, C2d). -/
theorem fz_two_add_ne_zero {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : fz X (2 + t * I) ≠ 0 := by
  intro h0
  have h := fz_lower_two hX t
  rw [h0, norm_zero] at h
  norm_num at h

/-- G5, divisor form (the analogue of `Zeta23.BL.count_disc_le`): Jensen's disc inequality for
`fz X` on `closedBall (2 + tI) R`, `t ≥ 3`, `0 < r < R < 3`. -/
theorem count_disc_le_fz {X : ℕ} (hX : 4 ≤ X) {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r)
    (hrR : r < R) (hR : R < 3) :
    (∑ᶠ u, (MeromorphicOn.divisor (fz X) (closedBall (2 + t * I) r) u : ℝ))
        * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R
          - Real.log ‖fz X (2 + t * I)‖ :=
  sum_divisor_mul_log_le (2 + t * I) r R (fz X) hr hrR
    (analyticOnNhd_fz (Zeta23.BL.one_notMem_closedBall_two_add ht hR))
    (fz_two_add_ne_zero hX t)

/-- G5. For `t ≥ 3`, `0 < r < R < 3`, `X ≥ 4` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + tI) r`:
`(∑ ρ ∈ S, zeta_order ρ) · log (R/r) ≤ circleAverage (log ‖fz X‖) (2 + tI) R + π²/(3X)`
(pattern `Zeta23.BL.count_finset_le`, with G4' in place of the ζ-divisor identity and the
centre bound C2d `−log ‖fz X (2 + tI)‖ ≤ π²/(3X)` in place of `log 3`). -/
theorem count_finset_le_fz {X : ℕ} (hX : 4 ≤ X) {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r)
    (hrR : r < R) (hR : R < 3) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R + Real.pi ^ 2 / (3 * X) := by
  have hlog : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).mpr hrR.le)
  have h1 := finset_sum_zeta_order_le_finsum_divisor_fz (X := X) (by omega)
    (Zeta23.BL.one_notMem_closedBall_two_add ht (hrR.trans hR)) S hS
  have h2 := count_disc_le_fz hX ht hr hrR hR
  have h3 := neg_log_norm_fz_two_le hX t
  calc (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ (∑ᶠ u, (MeromorphicOn.divisor (fz X) (closedBall (2 + t * I) r) u : ℝ))
          * Real.log (R / r) := mul_le_mul_of_nonneg_right h1 hlog
    _ ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R
          - Real.log ‖fz X (2 + t * I)‖ := h2
    _ ≤ _ := by linarith

/-- G5'. The window form (pattern `Zeta23.BL.count_window_le`; `geom_facts` supplies the
inclusion of the window into `closedBall (2 + tI) (rin σ₁ δ)`). -/
theorem count_window_le_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {X : ℕ} (hX : 4 ≤ X) {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) (Rout σ₁)
          + Real.pi ^ 2 / (3 * X) := by
  obtain ⟨hr, hrR, hR, -, -, hmem⟩ := Zeta23.BL.geom_facts h1 hδσ hδ
  refine count_finset_le_fz hX ht hr hrR (by linarith) S fun ρ hρ => ?_
  obtain ⟨hz, hδρ, hwt⟩ := hS ρ hρ
  exact ⟨hz, hmem ρ (by linarith) hz.2.2 t hwt⟩

end Zeta23.Density

#print axioms Zeta23.Density.fz_two_add_ne_zero
#print axioms Zeta23.Density.count_disc_le_fz
#print axioms Zeta23.Density.count_finset_le_fz
#print axioms Zeta23.Density.count_window_le_fz
