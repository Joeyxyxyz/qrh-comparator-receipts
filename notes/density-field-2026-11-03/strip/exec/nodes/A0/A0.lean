/-
A0.lean — node A0 of STRIP_PLAN (item A0: the count-to-mean-square bridge; the analogue of
`Zeta23.BL.count_le_meanSquare'`, `Zeta23/BL/BohrLandauPartial.lean:1862`).

  * A0   `count_le_meanSquare_fz`         — the plan's statement: for `T ≥ 4`, `X ≥ 4`, `ε > 0`,
         and a window mean-square hypothesis `hMS` on `σ ∈ [σ₁, 2]`, `a ∈ [3/2, 9/2]`,
         `2 hwin log(Rout/rin) · (NRight δ T − NRight δ 4) ≤ T · (½(ε² + E) + π²/X)`.
  * A0w  `count_le_meanSquare_fz_window`  — the window-abstracted core (zeros
         `NSigma (1/2 + δ) T₁ T₂`, integration window `[a, a + ℓ]`, `hMS` on `[a', a' + ℓ]`,
         `a' ∈ [a − 3/2, a + 3/2]`), the Carlson-stage shape.
  * `integral_circleAverage_Leps_le`       — J7 analogue: `∫_a^{a+ℓ} circleAverage (Leps ε (fz X))
         ≤ ℓ (½(ε² + E) + π²/(4X))` (G6 swap, per-θ bound, average of a constant).
  * `integral_Leps_circle_le`              — the per-θ bound: along `Re s = 2 + Rout cos θ`, either
         `Re ≤ 2` (hMS + G1c + G1d) or `Re > 2` (pointwise C2d + G1d).
  * `integral_Leps_segment_le_of_meanSquare`, `integral_Leps_segment_le_of_two_le`,
    `Leps_fz_le_of_two_le_re`              — the two segment bounds.

Scratch files cannot be imported, so the upstream items this node uses are copied verbatim
(same names and statements as in the sibling nodes, so the merger can drop either copy):
  the whole of exec/G7/G7.lean (which itself carries the copies from C, G4, G5, G1, G6 that G7
  needs), plus `norm_sq_fz_le_of_two_le_re` (C2d, exec/C/C.lean), `concaveOn_half_log_add` (G1b),
  `half_log_le_half` (G1d), `segment_average_Leps_le` (G1c) from exec/G1/G1.lean, and
  `integral_circleAverage_Leps_eq_swap` (G6), `intervalIntegrable_Leps_segment`,
  `intervalIntegrable_normSq_fz_segment` from exec/G6/G6.lean.

The DEFINITIONS block below is the frozen Stage-0 block of STRIP_PLAN.md, copied verbatim
(the `open`s before it only resolve `zeta_order`, `circleAverage`, `Rout/rin/hwin`;
they are not part of any definition body).  No `sorry`.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

open MNF.RH
open Real (circleAverage circleAverage_def)
open scoped Real
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

/-- C1': `fz X` is continuous on any set avoiding `1`. -/
theorem continuousOn_fz {X : ℕ} {U : Set ℂ} (hU : (1:ℂ) ∉ U) : ContinuousOn (fz X) U :=
  (analyticOnNhd_fz hU).continuousOn

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
(`LSeries.delta`), which would break the binder `{σ₁ δ : ℝ}` of G5' and G7. -/
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

/-! ## Copies from node G5 (G5, G5') -/

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

/-! ## Copies from node G1 (G1a, `continuousOn_Leps`, G3) -/

set_option linter.unusedVariables false in
/-- G1a: `log ‖f z‖ ≤ Leps ε f z` wherever `f z ≠ 0` (the hypothesis `hz` is needed because
`Real.log 0 = 0`, while `Leps ε f z = log ε < 0` there when `ε < 1`; `hε` is kept for the
plan's signature). -/
theorem log_norm_le_Leps {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℂ) {z : ℂ} (hz : f z ≠ 0) :
    Real.log ‖f z‖ ≤ Leps ε f z := by
  unfold Leps
  have h0 : 0 < ‖f z‖ := norm_pos_iff.mpr hz
  have h1 : Real.log (‖f z‖ ^ 2) ≤ Real.log (ε ^ 2 + ‖f z‖ ^ 2) :=
    Real.log_le_log (pow_pos h0 2) (le_add_of_nonneg_left (sq_nonneg ε))
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

/-- `Leps ε f` is continuous wherever `f` is (since `ε² + ‖f‖² > 0`). -/
theorem continuousOn_Leps {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ContinuousOn f U) : ContinuousOn (Leps ε f) U := by
  unfold Leps
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · exact continuousOn_const.add (hf.norm.pow 2)
  · intro z _
    have := pow_pos hε 2
    positivity

/-- G3: for `f` analytic on a neighbourhood of the closed ball with `f c ≠ 0`, the circle
average of `log ‖f‖` is at most the circle average of `Leps ε f` (a.e. comparison on the circle
through `AnalyticOnNhd.ae_circleMap_ne_zero`, `JensenDisc.lean:121`; pattern
`JensenDisc.lean:63-116`). -/
theorem circleAverage_log_norm_le_Leps {ε : ℝ} (hε : 0 < ε) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (h₁f : AnalyticOnNhd ℂ f (closedBall c R)) (h₂f : f c ≠ 0) :
    circleAverage (fun z => Real.log ‖f z‖) c R ≤ circleAverage (Leps ε f) c R := by
  have hfc : ContinuousOn f (sphere c R) := (h₁f.mono sphere_subset_closedBall).continuousOn
  have hint : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    (h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR.le
  have hLint : CircleIntegrable (Leps ε f) c R := (continuousOn_Leps hε hfc).circleIntegrable hR.le
  have hae := h₁f.ae_circleMap_ne_zero c R hR f h₂f
  rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
  refine setIntegral_mono_ae_restrict hint.1 hLint.1 ?_
  filter_upwards [hae] with θ hθ
  exact log_norm_le_Leps hε f hθ

/-! ## Copies from node G6 (the integrability of `t ↦ circleAverage (Leps ε (fz X)) (2 + tI) R`) -/

/-- `Leps ε (fz X)` is continuous off the pole `s = 1`. -/
theorem continuousOn_Leps_fz_ne_one {X : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (Leps ε (fz X)) {z : ℂ | z ≠ 1} :=
  continuousOn_Leps hε (continuousOn_fz (X := X) (U := {z : ℂ | z ≠ 1}) (by simp))

/-- `(t, θ) ↦ Leps ε (fz X) (circleMap (2 + t I) R θ)` is continuous on `{t ≥ 3} × ℝ`
(pattern `continuousOn_Lz_circleMap`, `BohrLandauPartial.lean:1605`). -/
theorem continuousOn_Leps_circleMap {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < 3) :
    ContinuousOn (fun p : ℝ × ℝ => Leps ε (fz X) (circleMap (2 + p.1 * I) R p.2))
      (Set.Ici 3 ×ˢ Set.univ) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap (2 + p.1 * I) R p.2) := by
    unfold circleMap
    fun_prop
  refine (continuousOn_Leps_fz_ne_one (X := X) hε).comp hc.continuousOn ?_
  rintro ⟨t, θ⟩ ⟨ht, -⟩
  show circleMap (2 + t * I) R θ ≠ 1
  exact Zeta23.BL.circleMap_two_add_ne_one ht hR0 hR θ

/-- Product integrability of `Leps ε (fz X) ∘ circleMap` on the rectangle
`(a, a + ℓ] × (0, 2π]`, `a ≥ 3` (pattern `integrableOn_Lz_circleMap_prod`, `:1616`). -/
theorem integrableOn_Leps_circleMap_prod {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R a ℓ : ℝ}
    (hR0 : 0 ≤ R) (hR : R < 3) (ha : 3 ≤ a) :
    IntegrableOn (fun p : ℝ × ℝ => Leps ε (fz X) (circleMap (2 + p.1 * I) R p.2))
      (Set.Ioc a (a + ℓ) ×ˢ Set.Ioc 0 (2 * π)) := by
  have hsub : Set.Icc a (a + ℓ) ⊆ Set.Ici 3 := fun x hx => le_trans ha hx.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => Leps ε (fz X) (circleMap (2 + p.1 * I) R p.2))
      (Set.Icc a (a + ℓ) ×ˢ Set.Icc 0 (2 * π)) :=
    (continuousOn_Leps_circleMap hε hR0 hR).mono (Set.prod_mono hsub (Set.subset_univ _))
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- The same, for the product of the restricted measures (the form Fubini consumes; pattern
`integrable_Lz_circleMap_prod_restrict`, `:1626`). -/
theorem integrable_Leps_circleMap_prod_restrict {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R a ℓ : ℝ}
    (hR0 : 0 ≤ R) (hR : R < 3) (ha : 3 ≤ a) :
    Integrable (fun p : ℝ × ℝ => Leps ε (fz X) (circleMap (2 + p.1 * I) R p.2))
      ((volume.restrict (Set.Ioc a (a + ℓ))).prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact integrableOn_Leps_circleMap_prod hε hR0 hR ha

/-- `t ↦ circleAverage (Leps ε (fz X)) (2 + t I) R` is interval integrable on `[a, a + ℓ]`,
`a ≥ 3` (marginal of the product integrability; pattern
`intervalIntegrable_circleAverage_Lz`, `:1634`). -/
theorem intervalIntegrable_circleAverage_Leps {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R a ℓ : ℝ}
    (hR0 : 0 ≤ R) (hR : R < 3) (ha : 3 ≤ a) (hℓ : 0 ≤ ℓ) :
    IntervalIntegrable (fun t => circleAverage (Leps ε (fz X)) (2 + t * I) R)
      volume a (a + ℓ) := by
  have h1 := integrable_Leps_circleMap_prod_restrict (X := X) (ℓ := ℓ) hε hR0 hR ha
  have h2 := h1.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have heq : (fun t : ℝ => circleAverage (Leps ε (fz X)) (2 + t * I) R)
      = fun t : ℝ => (2 * π)⁻¹ *
          ∫ θ in Set.Ioc 0 (2 * π), Leps ε (fz X) (circleMap (2 + t * I) R θ) := by
    funext t
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
  rw [heq]
  exact h2.const_mul _

/-! ## G7 — integrate the per-`t` count over the window -/

/-- The per-disc majorant step: on the discs centred `2 + tI`, `t ≥ 3`, `0 < R < 3`, G3 applies
to `fz X` (analytic on the disc by C1', non-zero at the centre by C2d).  This is the analogue of
`Zeta23.BL.circleAverage_log_le_Lz` (`BohrLandauPartial.lean:1568`). -/
theorem circleAverage_log_fz_le_Leps {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {t R : ℝ}
    (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3) :
    circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R
      ≤ circleAverage (Leps ε (fz X)) (2 + t * I) R :=
  circleAverage_log_norm_le_Leps hε (2 + t * I) hR (fz X)
    (analyticOnNhd_fz (Zeta23.BL.one_notMem_closedBall_two_add ht hR'))
    (fz_two_add_ne_zero hX t)

/-- G7, window-abstracted form (the plan's "window parameters abstracted from the start"):
every zero `ρ` with `Re ρ ≥ 1/2 + δ`, `T₁ < Im ρ ≤ T₂` lies in the inner ball
`closedBall (2 + tI) (rin σ₁ δ)` for all `t ∈ [Im ρ − hwin, Im ρ + hwin] ⊆ (a, b]` (as
`hwin ≤ 1`, `a ≤ T₁ − 1`, `T₂ + 1 ≤ b`), so integrating the per-`t` bound G5' + G3 over
`t ∈ [a, b]` (`a ≥ 3`) gives the multiplicity-weighted count `NSigma (1/2 + δ) T₁ T₂` times
`2 hwin log (Rout/rin)`.  Pattern copy of `Zeta23.BL.count_le_integral`
(`BohrLandauPartial.lean:1767-1840`), step-function machinery unchanged. -/
theorem count_le_integral_fz_window {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T₁ T₂ a b : ℝ}
    (ha : 3 ≤ a) (haT : a ≤ T₁ - 1) (hT : T₁ ≤ T₂) (hTb : T₂ + 1 ≤ b) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * (NSigma (1 / 2 + δ) T₁ T₂ : ℝ)
      ≤ ∫ t in a..b, (circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁)
          + Real.pi ^ 2 / (3 * X)) := by
  obtain ⟨hr, hrR, hR, hh, hh1, -⟩ := Zeta23.BL.geom_facts h1 hδσ hδ
  have hab : a ≤ b := by linarith
  -- the zeros counted by `NSigma (1/2 + δ) T₁ T₂`
  have hZfin : (MNF.RH.zerosIn T₁ T₂ ∩ {ρ : ℂ | 1 / 2 + δ ≤ ρ.re}).Finite :=
    (MNF.RH.zerosIn_finite T₁ T₂).subset Set.inter_subset_left
  have hcount : (NSigma (1 / 2 + δ) T₁ T₂ : ℝ) = ∑ ρ ∈ hZfin.toFinset, (zeta_order ρ : ℝ) := by
    unfold NSigma
    rw [Nat.cast_finsum_mem hZfin, finsum_mem_eq_finite_toFinset_sum _ hZfin]
  -- the step functions `g ρ`: `zeta_order ρ` on the window of `ρ`, `0` elsewhere
  set g : ℂ → ℝ → ℝ := fun ρ t =>
    (Set.Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)).indicator (fun _ => (zeta_order ρ : ℝ)) t
    with hg
  -- pointwise, for `t ∈ [a, b]`: G5' + G3 applied to the zeros whose window contains `t`
  have hpt : ∀ t ∈ Set.Icc a b,
      (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
        ≤ circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁) + Real.pi ^ 2 / (3 * X) := by
    intro t ht
    have ht3 : 3 ≤ t := ha.trans ht.1
    classical
    set S : Finset ℂ := Finset.filter
      (fun ρ : ℂ => t ∈ Set.Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)) hZfin.toFinset with hS
    have hsum : ∑ ρ ∈ hZfin.toFinset, g ρ t = ∑ ρ ∈ S, (zeta_order ρ : ℝ) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [hg, Set.indicator_apply]
    rw [hsum]
    have hcw := count_window_le_fz h1 hδσ hδ hX ht3 S (fun ρ hρ => by
      rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      obtain ⟨⟨⟨hz, -, -⟩, hδρ⟩, hρt⟩ := hρ
      have hδρ' : 1 / 2 + δ ≤ ρ.re := hδρ
      have h1' : ρ.im - hwin σ₁ δ ≤ t := hρt.1
      have h2' : t ≤ ρ.im + hwin σ₁ δ := hρt.2
      exact ⟨hz, by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩)
    have hL := circleAverage_log_fz_le_Leps hX hε ht3 (hr.trans hrR) (by linarith)
    linarith
  -- the step functions are integrable, with integral `2 hwin · zeta_order ρ`
  have hgi : ∀ ρ ∈ hZfin.toFinset, IntervalIntegrable (g ρ) volume a b := by
    intro ρ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (integrable_const _).indicator measurableSet_Icc
  have hgint : ∀ ρ ∈ hZfin.toFinset,
      ∫ t in a..b, g ρ t = 2 * hwin σ₁ δ * (zeta_order ρ : ℝ) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨-, h4, hT'⟩, -⟩ := hρ
    have hsub : Set.Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ) ⊆ Set.Ioc a b :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_of_le hab]
    simp only [hg]
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
      Set.inter_eq_left.2 hsub, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  -- integrate the pointwise bound
  have hLHSint : IntervalIntegrable
      (fun t => (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)) volume a b := by
    have := (IntervalIntegrable.sum hZfin.toFinset hgi).mul_const (Real.log (Rout σ₁ / rin σ₁ δ))
    simpa only [Finset.sum_apply] using this
  have hRHSint : IntervalIntegrable
      (fun t => circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁) + Real.pi ^ 2 / (3 * X))
      volume a b := by
    have hI := intervalIntegrable_circleAverage_Leps (X := X) (ℓ := b - a) hε (hr.trans hrR).le
      (by linarith) ha (by linarith)
    rw [add_sub_cancel] at hI
    exact hI.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hLHSint hRHSint hpt
  have hLHS : ∫ t in a..b, (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
      = 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * (NSigma (1 / 2 + δ) T₁ T₂ : ℝ) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_finsetSum hgi,
      Finset.sum_congr rfl hgint, ← Finset.mul_sum, ← hcount]
    ring
  rw [← hLHS]
  exact hmono

/-- G7 in the Carlson-stage shape: zeros `NSigma (1/2 + δ) T₁ T₂`, window `[T₁ − 1, T₂ + 1]`,
`4 ≤ T₁ ≤ T₂`. -/
theorem count_le_integral_fz_NSigma {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T₁ T₂ : ℝ}
    (hT₁ : 4 ≤ T₁) (hT : T₁ ≤ T₂) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * (NSigma (1 / 2 + δ) T₁ T₂ : ℝ)
      ≤ ∫ t in (T₁ - 1)..(T₂ + 1), (circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁)
          + Real.pi ^ 2 / (3 * X)) :=
  count_le_integral_fz_window h1 hδσ hδ hX hε (by linarith) le_rfl hT le_rfl

/-- `NRight δ T − NRight δ 4 = NSigma (1/2 + δ) 4 T` (as reals), for `T ≥ 4`: the two sets of
zeros agree since `δ ≤ Re ρ − 1/2 ↔ 1/2 + δ ≤ Re ρ` (`Zeta23.BL.NRight_sub_eq`,
`BohrLandauPartial.lean:1129`). -/
theorem NRight_sub_eq_NSigma {δ T : ℝ} (hT : 4 ≤ T) :
    (Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4 = NSigma (1 / 2 + δ) 4 T := by
  rw [Zeta23.BL.NRight_sub_eq hT]
  unfold NSigma
  have hfin : (MNF.RH.zerosIn 4 T ∩ {ρ : ℂ | 1 / 2 + δ ≤ ρ.re}).Finite :=
    (MNF.RH.zerosIn_finite 4 T).subset Set.inter_subset_left
  have hset : {ρ : ℂ | δ ≤ ρ.re - 1 / 2} = {ρ : ℂ | 1 / 2 + δ ≤ ρ.re} := by
    ext ρ
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [Nat.cast_finsum_mem hfin, hset]

/-- G7 (the plan's statement, `STRIP_PLAN.md` §(C) Stage 2): for `T ≥ 4`,
`2 hwin log(Rout/rin) · (NRight δ T − NRight δ 4)
  ≤ ∫_{3}^{T+3} (circleAverage (Leps ε (fz X)) (2 + tI) (Rout σ₁) + π²/(3X)) dt`.
Here `NRight` is `Zeta23.BL.NRight` (the plan's convention), written fully qualified because
`MNF.RH.NRight` is also in scope through `open MNF.RH`. -/
theorem count_le_integral_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
        * ((Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁)
          + Real.pi ^ 2 / (3 * X)) := by
  rw [NRight_sub_eq_NSigma hT]
  exact count_le_integral_fz_window h1 hδσ hδ hX hε le_rfl (by norm_num) hT (by linarith)


/-! ## Copies from node C (C2d, the squared centre-line bound) -/

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

/-! ## Copies from node G1 (G1b, G1d, G1c) -/

/-- G1b: `x ↦ (1/2) log (ε² + x)` is concave on `Ici 0` (pattern:
`concaveOn_half_log_one_add`, `BohrLandauPartial.lean:1472`). -/
theorem concaveOn_half_log_add {ε : ℝ} (hε : 0 < ε) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (1/2) * Real.log (ε ^ 2 + x)) := by
  have h1 : ConcaveOn ℝ ((fun z : ℝ => ε ^ 2 + z) ⁻¹' Set.Ioi 0)
      (Real.log ∘ fun z : ℝ => ε ^ 2 + z) :=
    strictConcaveOn_log_Ioi.concaveOn.translate_right (ε ^ 2)
  have h2 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (Real.log ∘ fun z : ℝ => ε ^ 2 + z) :=
    h1.subset (fun x hx => by
      simp only [Set.mem_preimage, Set.mem_Ioi]
      linarith [pow_pos hε 2, Set.mem_Ici.mp hx]) (convex_Ici 0)
  have h3 := h2.smul (c := (1 / 2 : ℝ)) (by norm_num)
  simpa [smul_eq_mul, Function.comp] using h3

set_option linter.unusedVariables false in
/-- G1d: `(1/2) log (ε² + (1 + x)) ≤ (1/2) (ε² + x)`, from `log y ≤ y - 1` (the hypothesis
`hε` is not needed, since `ε² ≥ 0` anyway; it is kept for the plan's signature). -/
theorem half_log_le_half {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    (1/2) * Real.log (ε ^ 2 + (1 + x)) ≤ (1/2) * (ε ^ 2 + x) := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ε ^ 2 + (1 + x))
  exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- G1c: Jensen's inequality for the concave `x ↦ (1/2) log (ε² + x)` on the interval average
over `[a, a + ℓ]`: the integral of `Leps ε f` along the vertical segment `Re = σ` is at most
`ℓ · (1/2) log (ε² + (mean square of ‖f‖ on the segment))`.  This is the step at which the
receipted proof (`Lz_le_half_sq`, `BohrLandauPartial.lean:1663`) threw the logarithm away. -/
theorem segment_average_Leps_le {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℂ) (σ a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hf : IntervalIntegrable (fun t => ‖f ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ))
    (hL : IntervalIntegrable (fun t => Leps ε f ((σ:ℂ) + t * I)) volume a (a + ℓ)) :
    ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I)
      ≤ ℓ * ((1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2)) := by
  have hab : a ≤ a + ℓ := by linarith
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc a (a + ℓ))) := inferInstance
  have hne : NeZero (volume (Set.Ioc a (a + ℓ))) := ⟨by
    rw [Real.volume_Ioc]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith⟩
  -- (the measure is fixed through `hfi`: the name `μ` is the Möbius notation here)
  have hfi : Integrable (fun t : ℝ => ‖f ((σ:ℂ) + t * I)‖ ^ 2)
      (volume.restrict (Set.Ioc a (a + ℓ))) := hf.1
  have hgi : Integrable (fun t : ℝ => Leps ε f ((σ:ℂ) + t * I))
      (volume.restrict (Set.Ioc a (a + ℓ))) := hL.1
  have hgc : ContinuousOn (fun x : ℝ => (1/2) * Real.log (ε ^ 2 + x)) (Set.Ici 0) := by
    refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
    · exact continuousOn_const.add continuousOn_id
    · intro x hx
      show ε ^ 2 + x ≠ 0
      linarith [pow_pos hε 2, Set.mem_Ici.mp hx]
  have hfs : ∀ᵐ t ∂(volume.restrict (Set.Ioc a (a + ℓ))),
      (fun t : ℝ => ‖f ((σ:ℂ) + t * I)‖ ^ 2) t ∈ Set.Ici (0:ℝ) := by
    filter_upwards; simp
  have key := (concaveOn_half_log_add hε).le_map_average hgc isClosed_Ici hfs hfi hgi
  have e1 : (⨍ t in Set.Ioc a (a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2)
      = (1/ℓ) * ∫ t in a..(a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2 := by
    rw [setAverage_eq, Real.volume_real_Ioc_of_le hab, add_sub_cancel_left, smul_eq_mul,
      intervalIntegral.integral_of_le hab, one_div]
  have e2 : (⨍ t in Set.Ioc a (a + ℓ), Leps ε f ((σ:ℂ) + t * I))
      = (1/ℓ) * ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I) := by
    rw [setAverage_eq, Real.volume_real_Ioc_of_le hab, add_sub_cancel_left, smul_eq_mul,
      intervalIntegral.integral_of_le hab, one_div]
  have key2 : (1/ℓ) * ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I)
      ≤ (1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2) := by
    rw [← e1, ← e2]
    exact key
  calc ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I)
      = ℓ * ((1/ℓ) * ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I)) := by
        have hcancel : ℓ * (1 / ℓ) = 1 := by
          rw [mul_one_div, div_self hℓ.ne']
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ℓ * ((1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left key2 hℓ.le

/-! ## Copies from node G6 (the Fubini swap and the segment integrability lemmas) -/

/-- G6, Fubini form: the `t`-integral over `[a, a + ℓ]` (`a ≥ 3`, `ℓ ≥ 0`) of the circle
averages of `Leps ε (fz X)` is `(2π)⁻¹` times the `θ`-integral of the `t`-integrals along the
circle points (pattern `integral_circleAverage_Lz_eq_swap`, `:1649`). -/
theorem integral_circleAverage_Leps_eq_swap {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R a ℓ : ℝ}
    (hR0 : 0 ≤ R) (hR : R < 3) (ha : 3 ≤ a) (hℓ : 0 ≤ ℓ) :
    ∫ t in a..(a + ℓ), circleAverage (Leps ε (fz X)) (2 + t * I) R
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) R θ) := by
  simp_rw [circleAverage_def, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral_intervalIntegral_swap ?_
  rw [Set.uIoc_of_le (by linarith : a ≤ a + ℓ), Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
  exact integrableOn_Leps_circleMap_prod hε hR0 hR ha

/-! ## The inner integrals along a vertical segment -/

/-- `u ↦ Leps ε (fz X) (σ + u I)` is interval integrable on `[a, b]` for `a > 0` (the segment
avoids the pole; pattern `intervalIntegrable_Lz_segment`, `:1676`). -/
theorem intervalIntegrable_Leps_segment {X : ℕ} {ε : ℝ} (hε : 0 < ε) {σ a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => Leps ε (fz X) ((σ : ℂ) + (u : ℂ) * I)) volume a b :=
  ((continuousOn_Leps_fz_ne_one (X := X) hε).comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (Zeta23.BL.segment_mapsTo_ne_one ha)).intervalIntegrable_of_Icc hab

/-- `u ↦ ‖fz X (σ + u I)‖²` is interval integrable on `[a, b]` for `a > 0` (pattern
`intervalIntegrable_normSq_zeta_segment`, `:1682`). -/
theorem intervalIntegrable_normSq_fz_segment {X : ℕ} {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖fz X ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2) volume a b :=
  (((continuousOn_fz (X := X) (U := {z : ℂ | z ≠ 1}) (by simp)).comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (Zeta23.BL.segment_mapsTo_ne_one ha)).norm.pow 2).intervalIntegrable_of_Icc hab


/-! ## A0 — the count-to-mean-square bridge (analogue of `Zeta23.BL.count_le_meanSquare'`) -/

/-- Along a vertical segment `Re s = σ`, the window integral of `Leps ε (fz X)` over
`[a, a + ℓ]` (`a > 0`, `ℓ > 0`) is bounded through the window mean square of `‖fz X‖`:
Jensen (G1c) gives `ℓ · ½ log(ε² + mean square)`, and `log(ε² + 1 + E) ≤ ε² + E` (G1d). -/
theorem integral_Leps_segment_le_of_meanSquare {X : ℕ} {ε : ℝ} (hε : 0 < ε) {σ a ℓ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) {E : ℝ} (hE0 : 0 ≤ E)
    (hms : ∫ t in a..(a + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ ℓ * (1 + E)) :
    ∫ t in a..(a + ℓ), Leps ε (fz X) ((σ:ℂ) + t * I) ≤ ℓ * ((1/2) * (ε ^ 2 + E)) := by
  have hab : a ≤ a + ℓ := by linarith
  have hJ := segment_average_Leps_le hε (fz X) σ a hℓ
    (intervalIntegrable_normSq_fz_segment ha hab) (intervalIntegrable_Leps_segment hε ha hab)
  have hint0 : 0 ≤ ∫ t in a..(a + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
  have hmean : (1/ℓ) * ∫ t in a..(a + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ 1 + E := by
    rw [one_div, inv_mul_le_iff₀ hℓ]
    exact hms
  have hlog : (1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2)
      ≤ (1/2) * Real.log (ε ^ 2 + (1 + E)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log
    · have h1 := pow_pos hε 2
      have h2 := mul_nonneg (one_div_pos.mpr hℓ).le hint0
      linarith
    · linarith
  calc ∫ t in a..(a + ℓ), Leps ε (fz X) ((σ:ℂ) + t * I)
      ≤ ℓ * ((1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2)) :=
        hJ
    _ ≤ ℓ * ((1/2) * Real.log (ε ^ 2 + (1 + E))) := mul_le_mul_of_nonneg_left hlog hℓ.le
    _ ≤ ℓ * ((1/2) * (ε ^ 2 + E)) :=
        mul_le_mul_of_nonneg_left (half_log_le_half hε.le hE0) hℓ.le

/-- Pointwise, for `Re s ≥ 2` and `X ≥ 4`: `Leps ε (fz X) s ≤ ½ (ε² + π²/(2X))`
(C2d `‖fz X s‖² ≤ 1 + π²/(2X)` and G1d). -/
theorem Leps_fz_le_of_two_le_re {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {s : ℂ}
    (hs : 2 ≤ s.re) :
    Leps ε (fz X) s ≤ (1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X)) := by
  unfold Leps
  have h := norm_sq_fz_le_of_two_le_re hX hs
  have hp : 0 ≤ Real.pi ^ 2 / (2 * X) := by positivity
  calc (1 / 2) * Real.log (ε ^ 2 + ‖fz X s‖ ^ 2)
      ≤ (1/2) * Real.log (ε ^ 2 + (1 + Real.pi ^ 2 / (2 * X))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.log_le_log
        · have := pow_pos hε 2
          positivity
        · linarith
    _ ≤ (1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X)) := half_log_le_half hε.le hp

/-- Along a vertical segment `Re s = σ ≥ 2` the window integral of `Leps ε (fz X)` over
`[a, a + ℓ]` (`a > 0`, `ℓ ≥ 0`) is at most `ℓ · ½ (ε² + π²/(2X))` (no mean square needed). -/
theorem integral_Leps_segment_le_of_two_le {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε)
    {σ a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) (hσ : 2 ≤ σ) :
    ∫ t in a..(a + ℓ), Leps ε (fz X) ((σ:ℂ) + t * I)
      ≤ ℓ * ((1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X))) := by
  have hab : a ≤ a + ℓ := by linarith
  have hpt : ∀ t : ℝ, Leps ε (fz X) ((σ:ℂ) + t * I)
      ≤ (1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X)) := by
    intro t
    apply Leps_fz_le_of_two_le_re hX hε
    have hre : ((σ:ℂ) + t * I).re = σ := by simp
    rw [hre]
    exact hσ
  calc ∫ t in a..(a + ℓ), Leps ε (fz X) ((σ:ℂ) + t * I)
      ≤ ∫ t in a..(a + ℓ), (1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X)) :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_Leps_segment hε ha hab)
          intervalIntegrable_const (fun t _ => hpt t)
    _ = ℓ * ((1/2) * (ε ^ 2 + Real.pi ^ 2 / (2 * X))) := by
        rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]

/-- The per-`θ` bound (analogue of `Zeta23.BL.integral_Lz_circle_le`,
`BohrLandauPartial.lean:1688`): along the circle points `circleMap (2 + tI) (Rout σ₁) θ`,
`t ∈ [a, a + ℓ]`, the integral of `Leps ε (fz X)` is an integral along the vertical segment
`Re s = 2 + Rout σ₁ cos θ ∈ [σ₁, 2 + Rout σ₁]` over the shifted window
`[a', a' + ℓ]`, `a' = a + Rout σ₁ sin θ ∈ (a − 3/2, a + 3/2)`.  If `Re ≤ 2` the window mean
square `hMS` applies (G1c + G1d); if `Re > 2` the pointwise centre bound (C2d + G1d) applies. -/
theorem integral_Leps_circle_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {X : ℕ} (hX : 4 ≤ X)
    {ε : ℝ} (hε : 0 < ε) {a ℓ : ℝ} (ha : 3 ≤ a) (hℓ : 0 < ℓ) {E : ℝ} (hE0 : 0 ≤ E)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a' : ℝ, a - 3 / 2 ≤ a' → a' ≤ a + 3 / 2 →
      ∫ t in a'..(a' + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ ℓ * (1 + E)) (θ : ℝ) :
    ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ)
      ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) := by
  have hRdef : Rout σ₁ = 2 - σ₁ := rfl
  have hR0 : 0 < Rout σ₁ := by rw [hRdef]; linarith
  have hR : Rout σ₁ < 3 / 2 := by rw [hRdef]; linarith
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hR0.le
  have hsin : |Rout σ₁ * Real.sin θ| ≤ Rout σ₁ := by
    rw [abs_mul, abs_of_pos hR0]
    exact mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)
  obtain ⟨hsin1, hsin2⟩ := abs_le.1 hsin
  have hσ1 : σ₁ ≤ 2 + Rout σ₁ * Real.cos θ := by rw [hRdef] at hcos ⊢; linarith
  simp_rw [Zeta23.BL.circleMap_two_add]
  have hshift := intervalIntegral.integral_comp_add_right (a := a) (b := a + ℓ)
    (fun u : ℝ => Leps ε (fz X) (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I))
    (Rout σ₁ * Real.sin θ)
  rw [hshift]
  have hwindow : a + ℓ + Rout σ₁ * Real.sin θ = a + Rout σ₁ * Real.sin θ + ℓ := by ring
  rw [hwindow]
  have ha'0 : 0 < a + Rout σ₁ * Real.sin θ := by linarith
  have hp : 0 ≤ Real.pi ^ 2 / (4 * X) := by positivity
  have hpi : Real.pi ^ 2 / (2 * X) = 2 * (Real.pi ^ 2 / (4 * X)) := by ring
  rcases le_or_gt (2 + Rout σ₁ * Real.cos θ) 2 with hσ2 | hσ2
  · -- `Re ≤ 2`: the window mean square
    have h := integral_Leps_segment_le_of_meanSquare hε ha'0 hℓ hE0
      (hMS _ hσ1 hσ2 (a + Rout σ₁ * Real.sin θ) (by linarith) (by linarith))
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hℓ.le)
  · -- `Re > 2`: the pointwise centre bound
    have h := integral_Leps_segment_le_of_two_le hX hε ha'0 hℓ.le hσ2.le
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hℓ.le)

/-- J7 analogue, assembled: the `t`-integral over `[a, a + ℓ]` (`a ≥ 3`, `ℓ > 0`) of the circle
averages of `Leps ε (fz X)` on the discs of radius `Rout σ₁` is at most
`ℓ (½(ε² + E) + π²/(4X))` under the window mean-square hypothesis `hMS` (G6 swap, the per-`θ`
bound `integral_Leps_circle_le`, and the average of a constant over `θ ∈ [0, 2π]`). -/
theorem integral_circleAverage_Leps_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {X : ℕ}
    (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {a ℓ : ℝ} (ha : 3 ≤ a) (hℓ : 0 < ℓ) {E : ℝ} (hE0 : 0 ≤ E)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a' : ℝ, a - 3 / 2 ≤ a' → a' ≤ a + 3 / 2 →
      ∫ t in a'..(a' + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ ℓ * (1 + E)) :
    ∫ t in a..(a + ℓ), circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁)
      ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) := by
  have hR0 : 0 < Rout σ₁ := by show 0 < 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  rw [integral_circleAverage_Leps_eq_swap hε hR0.le hR ha hℓ.le]
  have hGle : ∀ θ : ℝ,
      ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ)
        ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) :=
    fun θ => integral_Leps_circle_le h1 h2 hX hε ha hℓ hE0 hMS θ
  -- the `θ`-marginal is integrable (Fubini on the product integrability of G6)
  have hGint : IntervalIntegrable
      (fun θ : ℝ => ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ))
      volume 0 (2 * π) := by
    have h1' := integrable_Leps_circleMap_prod_restrict (X := X) (a := a) (ℓ := ℓ) hε hR0.le hR ha
    have h2' := h1'.integral_prod_right
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    have heq : (fun θ : ℝ => ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ))
        = fun θ : ℝ =>
            ∫ t in Set.Ioc a (a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ) := by
      funext θ
      rw [intervalIntegral.integral_of_le (by linarith)]
    rw [heq]
    exact h2'
  have hmono : ∫ θ in (0:ℝ)..(2 * π),
        (∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ))
      ≤ ∫ θ in (0:ℝ)..(2 * π), ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) :=
    intervalIntegral.integral_mono_on (by positivity) hGint intervalIntegrable_const
      (fun θ _ => hGle θ)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have hpi : 0 < 2 * π := by positivity
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          (∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) (Rout σ₁) θ))
      ≤ (2 * π)⁻¹ * (2 * π * (ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)))) :=
        mul_le_mul_of_nonneg_left hmono (inv_pos.mpr hpi).le
    _ = ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

/-- A0, window-abstracted form (the Carlson-stage shape): zeros `NSigma (1/2 + δ) T₁ T₂`,
integration window `[a, a + ℓ]` with `3 ≤ a ≤ T₁ − 1`, `T₁ ≤ T₂`, `T₂ + 1 ≤ a + ℓ`, and the
window mean square `hMS` on `[a', a' + ℓ]` for `a' ∈ [a − 3/2, a + 3/2]`, `σ ∈ [σ₁, 2]`:
`2 hwin log(Rout/rin) · NSigma (1/2 + δ) T₁ T₂ ≤ ℓ (½(ε² + E) + π²/X)`.
(G7w, the split of the constant `π²/(3X)`, `integral_circleAverage_Leps_le`, and
`π²/(4X) + π²/(3X) = (7/12) π²/X ≤ π²/X`.) -/
theorem count_le_meanSquare_fz_window {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T₁ T₂ a ℓ : ℝ}
    (ha : 3 ≤ a) (haT : a ≤ T₁ - 1) (hT : T₁ ≤ T₂) (hTb : T₂ + 1 ≤ a + ℓ) {E : ℝ} (hE0 : 0 ≤ E)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a' : ℝ, a - 3 / 2 ≤ a' → a' ≤ a + 3 / 2 →
      ∫ t in a'..(a' + ℓ), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ ℓ * (1 + E)) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * (NSigma (1 / 2 + δ) T₁ T₂ : ℝ)
      ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / X) := by
  have h2 : σ₁ < 1 := by linarith
  have hR0 : 0 < Rout σ₁ := by show 0 < 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  have hℓ : 0 < ℓ := by linarith
  -- G7 (window form)
  have h6 := count_le_integral_fz_window h1 hδσ hδ hX hε ha haT hT hTb
  have hI := intervalIntegrable_circleAverage_Leps (X := X) (a := a) (ℓ := ℓ) hε hR0.le hR ha hℓ.le
  rw [intervalIntegral.integral_add hI intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at h6
  -- the per-`θ` bound averaged over `θ`
  have h7 := integral_circleAverage_Leps_le h1 h2 hX hε ha hℓ hE0 hMS
  have hp : 0 ≤ Real.pi ^ 2 / (X:ℝ) := by positivity
  calc 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * (NSigma (1 / 2 + δ) T₁ T₂ : ℝ)
      ≤ (∫ t in a..(a + ℓ), circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁))
          + (a + ℓ - a) * (Real.pi ^ 2 / (3 * X)) := h6
    _ = (∫ t in a..(a + ℓ), circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁))
          + ℓ * (Real.pi ^ 2 / (3 * X)) := by ring
    _ ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / (4 * X)) + ℓ * (Real.pi ^ 2 / (3 * X)) := by
        linarith [h7]
    _ = ℓ * ((1/2) * (ε ^ 2 + E) + (7 / 12) * (Real.pi ^ 2 / X)) := by ring
    _ ≤ ℓ * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / X) := by
        apply mul_le_mul_of_nonneg_left _ hℓ.le
        linarith

/-- A0 (the plan's statement, `STRIP_PLAN.md` §(C) Stage 3): for `T ≥ 4`, `X ≥ 4`, `ε > 0`,
`E ≥ 0`, and the window mean-square hypothesis `hMS` (`σ ∈ [σ₁, 2]`, windows `[a, a + T]` with
`a ∈ [3/2, 9/2]`),
`2 hwin log(Rout/rin) · (NRight δ T − NRight δ 4) ≤ T · (½(ε² + E) + π²/X)`.
Here `NRight` is `Zeta23.BL.NRight` (the plan's convention), written fully qualified because
`MNF.RH.NRight` is also in scope through `open MNF.RH`.  This is the quantitative replacement
of `Zeta23.BL.count_le_meanSquare'` (`BohrLandauPartial.lean:1862`). -/
theorem count_le_meanSquare_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 4 ≤ T) {E : ℝ}
    (hE0 : 0 ≤ E)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a : ℝ, 3 / 2 ≤ a → a ≤ 9 / 2 →
      ∫ t in a..(a + T), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ T * (1 + E)) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
        * ((Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4)
      ≤ T * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / X) := by
  rw [NRight_sub_eq_NSigma hT]
  exact count_le_meanSquare_fz_window h1 hδσ hδ hX hε (a := 3) (ℓ := T) le_rfl (by norm_num) hT
    (by linarith) hE0
    (fun σ hσ1 hσ2 a' ha1 ha2 => hMS σ hσ1 hσ2 a' (by linarith) (by linarith))

end Zeta23.Density

#print axioms Zeta23.Density.integral_Leps_segment_le_of_meanSquare
#print axioms Zeta23.Density.Leps_fz_le_of_two_le_re
#print axioms Zeta23.Density.integral_Leps_segment_le_of_two_le
#print axioms Zeta23.Density.integral_Leps_circle_le
#print axioms Zeta23.Density.integral_circleAverage_Leps_le
#print axioms Zeta23.Density.count_le_meanSquare_fz_window
#print axioms Zeta23.Density.count_le_meanSquare_fz
