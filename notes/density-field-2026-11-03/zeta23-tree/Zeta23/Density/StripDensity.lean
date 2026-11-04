/-
═══════════════════════════════════════════════════════════════════════
ZETA23 — A ZERO-DENSITY ESTIMATE WITH A POWER SAVING (SINGLE-WINDOW FORM)
(StripDensity.lean)
[PROVED | this tree]  No `sorry`; axioms `[propext, Classical.choice, Quot.sound]`
(every theorem is audited by name from `MNF_AuditDensity.lean` at the tree root).
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e), on top of
Zeta23/BL/BohrLandauPartial.lean, Zeta23/BL/BohrLandauClosure.lean (the sharp approximate
formula `BLClosure.zeta_approx_sharp`), Zeta23/BL/JensenDisc.lean, and the MNF/RH library (MNF is the name of the framework that
library is written for, not standard terminology; only `zeta_order`, `zerosIn` and
`is_nontrivial_zero` are used from it).

WHAT IS PROVED.  For every `1/2 < σ₁` and `σ₁ − 1/2 < δ ≤ 1/2` there is a constant `C` with

  `NRight δ T ≤ C · T ^ (1 − (2σ₁ − 1)² / (2σ₁)) · (1 + log T) ^ 3`   for all `T ≥ 2`

(`density_single_window`), where `NRight δ T = Zeta23.BL.NRight δ T` (same definition body as
`MNF.RH.NRight`) counts, with multiplicity, the nontrivial zeros `ρ` of ζ with `0 < Im ρ ≤ T`
and `Re ρ − 1/2 ≥ δ`.  The exponent is `1 − (2σ₁ − 1)²/(2σ₁)`: at `σ₁ = 3/4` the count is
`O(T^{5/6} (log T)^3)`; for a given `δ` the saving is `(2σ₁ − 1)²/(2σ₁)`, which approaches
`4δ²/(1 + 2δ) ≈ 4δ²` as `σ₁ → 1/2 + δ` from below (the hypothesis `σ₁ − 1/2 < δ` is strict and
`C` depends on `σ₁`, so every saving below `4δ²/(1 + 2δ)` is attained and that value itself is
not).  This sharpens the Bohr–Landau bound `NRight δ T = O(T)` proved on this tree
(`Zeta23.BL.rightHalfBound`; two-sided form `Zeta23.BL.bohrLandau_full`) to a power saving:
the number of zeros with `0 < Im ρ ≤ T` at distance `≥ δ` to the right of the line is
`O(T^{1−c})` rather than `O(T)`.

THE METHOD is Carlson's (1920), with a weaker exponent than Carlson's `4σ₁(1 − σ₁)`: the
mollified function `f_X = ζ · M_X`, `M_X(s) = Σ_{n ≤ X} μ(n) n^{−s}`, is averaged on Jensen
discs centred `2 + it` (the disc machinery of BohrLandauPartial.lean), the circle averages of
`log ‖f_X‖` are majorised by `Leps ε f_X = ½ log(ε² + ‖f_X‖²)` and then, through Jensen's
inequality for the concave `log`, by window mean squares of `‖f_X‖` on vertical segments;
those mean squares come from the product Dirichlet polynomial `S_N · M_X` (Montgomery–Vaughan,
`M1.dirichlet_meanSquare_le`) plus the sharp approximate-formula remainder, with the divisor
bound `Σ_{m ≤ Y} d_X(m)² ≤ Y (1 + log X)³` controlling the coefficients.  One approximate
formula of length `N ≈ T` is used on the single window `[3, T + 3]`; this is what costs the
exponent (Carlson's `4σ₁(1 − σ₁)` needs `N ≈ t` dyadically — not proved here).  Multiplicativity
of ζ enters only through `μ * ζ = 1` in the mollifier; it buys a power saving in the count,
not a zero-free strip.

WHAT THIS IS NOT.  Nothing here touches `MNF.RH.SpectralGapHyp` (the spectral-gap hypothesis
of the MNF library), nothing here excludes a single zero, and nothing here says anything about
zeros closer than δ to the line: the result is a *count* of zeros off the line, strictly weaker
than any zero-free strip, and not known to imply anything about one.  It uses no zero-free
region and proves none, and it is not evidence for the Riemann hypothesis.  Nothing here uses
the 7/8 theorem.  A linear saving `1 − c(σ₁ − 1/2)`
(Ingham) is out of reach of this route (it needs a fourth moment not on the tree).

FILE LAYOUT.  The DEFINITIONS block (`Mx`, `fz`, `cm`, `dX`, `Leps`, `NSigma`) at the top is
the fixed list of definitions the statements depend on; the `open`s before it only resolve
`zeta_order`, `circleAverage` and `Rout/rin/hwin` and are not part of any definition body.
Besides that block, the section "Exponent arithmetic" introduces seven auxiliary real constants (`E0gen`,
`Egen`, `Esingle`, `K1c`, `Ebarc`, `CMc`, `Ksingle`) that name the error terms; they occur in the
statements of that section and of `count_le_Egen` only, not in `density_single_window`; any
file restating those statements must reproduce these definitions verbatim (or inline them).
`NRight` is always written `Zeta23.BL.NRight`, since `open MNF.RH` (needed for the `NSigma`
body) would make the
bare name ambiguous with `MNF.RH.NRight`.  Sections, by content: centre bound; product
polynomial; divisor sum; partial summation; window mean squares; mollifier zero orders; Jensen
discs; the `Leps` majorant; integrability and Fubini; count-to-integral; count-to-mean-square;
exponent arithmetic; geometric factor; assembly.
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

/-! ## END of the DEFINITIONS block -/


/-! ## Analyticity of `M_X`, `f_X`, and the centre bound on `Re s ≥ 2` -/

section Centre

/-- `Mx X` is analytic on all of `ℂ` (a finite sum of `c · n^{-s}`, `n ≥ 1`). -/
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

/-- `fz X = ζ · Mx X` is analytic on any set avoiding `1`. -/
theorem analyticOnNhd_fz {X : ℕ} {S : Set ℂ} (hS : (1:ℂ) ∉ S) : AnalyticOnNhd ℂ (fz X) S :=
  (Zeta23.RvM.analyticOnNhd_riemannZeta hS).mul ((analyticOnNhd_Mx X).mono (Set.subset_univ S))

/-- `fz X` is continuous on any set avoiding `1`. -/
theorem continuousOn_fz {X : ℕ} {U : Set ℂ} (hU : (1:ℂ) ∉ U) : ContinuousOn (fz X) U :=
  (analyticOnNhd_fz hU).continuousOn

/-- `Σ_{n > X} 1/n² ≤ 1/X` (telescoping `1/n² ≤ 1/(n−1) − 1/n`). -/
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

/- `open scoped LSeries.notation` is restricted to `fz_sub_one_eq`: that scope also makes `δ` a token
(`LSeries.delta`), which would break every binder `{σ₁ δ : ℝ}` below. -/
set_option linter.unusedVariables false in
open scoped LSeries.notation in
/-- For `Re s > 1`, `fz X s − 1 = −ζ(s)·Σ_{n > X} μ(n) n^{−s}`
(from `ζ(s)·L(μ, s) = 1`, splitting the absolutely convergent `L(μ, s)` at `X`).
The hypothesis `hX` is kept for the statement shape; the identity does not use it. -/
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

/-- For `Re s ≥ 2`, `‖fz X s − 1‖ ≤ (π²/6)·(1/X)`
(`‖ζ‖ ≤ π²/6`, `|μ| ≤ 1`, `‖n^{−s}‖ ≤ n^{−2}`, and `tail_inv_sq_le`). -/
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

/-- `‖fz X (2 + it)‖ ≥ 1/2` for `X ≥ 4` (since `π²/24 < 1/2`). -/
theorem fz_lower_two {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : (1/2 : ℝ) ≤ ‖fz X (2 + t * I)‖ := by
  have hre : (2 + t * I : ℂ).re = 2 := by simp
  have h := norm_fz_sub_one_le (X := X) (by omega) (s := 2 + t * I) hre.symm.le
  have h2 := pi_sq_div_six_div_le hX
  have h3 := pi_sq_lt_ten
  have h4 := one_sub_norm_le_norm_fz (X := X) (2 + t * I)
  linarith

/-- `−log ‖fz X (2 + it)‖ ≤ π²/(3X)` for `X ≥ 4`
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

/-- `log ‖fz X s‖ ≤ π²/(6X)` for `Re s ≥ 2`, `X ≥ 4` (`log(1 + x) ≤ x`). -/
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

/-- `‖fz X s‖² ≤ 1 + π²/(2X)` for `Re s ≥ 2`, `X ≥ 4` (`(1 + x)² ≤ 1 + 3x` on `[0, 1]`). -/
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

end Centre


/-! ## The product polynomial `S_N · M_X` and its coefficients -/

section ProductPolynomial

/-! ### `|cm N X m| ≤ dX X m` -/

/-- The coefficient is bounded by the number of divisors `≤ X`
(each term of the defining sum is `μ d` or `0`, and `|μ d| ≤ 1`). -/
theorem abs_cm_le (N X m : ℕ) : (|cm N X m| : ℝ) ≤ dX X m := by
  rw [cm, dX, Int.cast_sum]
  calc |∑ d ∈ m.divisors.filter (· ≤ X), ((if m / d ≤ N then μ d else 0 : ℤ) : ℝ)|
      ≤ ∑ d ∈ m.divisors.filter (· ≤ X), |((if m / d ≤ N then μ d else 0 : ℤ) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ m.divisors.filter (· ≤ X), (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        split_ifs
        · have h := ArithmeticFunction.abs_moebius_le_one (n := d)
          exact_mod_cast h
        · simp
    _ = ((m.divisors.filter (· ≤ X)).card : ℝ) := by simp

/-! ### `cm N X m = [m = 1]` for `m ≤ X ≤ N` -/

/-- For `m ≤ X ≤ N` every divisor `d` of `m` has `d ≤ X` and `m / d ≤ N`, so
`cm N X m = Σ_{d ∣ m} μ d = (ζ * μ)(m) = [m = 1]`. -/
theorem cm_eq_of_le {N X m : ℕ} (hXN : X ≤ N) (hm : m ≤ X) :
    cm N X m = if m = 1 then 1 else 0 := by
  have h1 : m.divisors.filter (· ≤ X) = m.divisors := by
    apply filter_true_of_mem
    intro d hd
    exact (Nat.divisor_le hd).trans hm
  have h2 : ∀ d ∈ m.divisors, (if m / d ≤ N then μ d else 0) = μ d := by
    intro d _
    rw [if_pos ((Nat.div_le_self m d).trans (hm.trans hXN))]
  rw [cm, h1, sum_congr rfl h2, ← ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply]

/-! ### `S N s * Mx X s = Σ_{m ≤ NX} cm N X m · m^{-s}` -/

/-- The product of the two Dirichlet polynomials, reindexed by `m = n * d`. -/
theorem S_mul_Mx_eq (N X : ℕ) (s : ℂ) :
    BLClosure.S N s * Mx X s = ∑ m ∈ Icc 1 (N * X), ((cm N X m : ℤ) : ℂ) * (m : ℂ) ^ (-s) := by
  -- the right-hand summand as a sum over the fibre {d ∣ m, d ≤ X, m/d ≤ N}
  have hR : ∀ m ∈ Icc 1 (N * X), ((cm N X m : ℤ) : ℂ) * (m : ℂ) ^ (-s)
      = ∑ d ∈ (m.divisors.filter (· ≤ X)).filter (fun d => m / d ≤ N),
          ((μ d : ℤ) : ℂ) * (m : ℂ) ^ (-s) := by
    intro m _
    rw [sum_filter, cm, Int.cast_sum, sum_mul]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl hR, sum_sigma']
  unfold BLClosure.S Mx
  rw [sum_mul_sum, sum_sigma']
  refine sum_nbij' (fun x => ⟨x.1 * x.2, x.2⟩) (fun y => ⟨y.1 / y.2, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hn1, hnN⟩, hd1, hdX⟩ := hx
    have hd0 : 0 < d := hd1
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hn1 hd0).ne', Nat.mul_le_mul hnN hdX⟩,
      ⟨⟨Dvd.intro_left n rfl, (Nat.mul_pos hn1 hd0).ne'⟩, hdX⟩, ?_⟩
    rw [Nat.mul_div_cancel n hd0]
    exact hnN
  · rintro ⟨m, d⟩ hy
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨hm1, _⟩, ⟨⟨hdm, hm0⟩, hdX⟩, hmdN⟩ := hy
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm1
    exact ⟨⟨Nat.div_pos (Nat.le_of_dvd hm1 hdm) hd0, hmdN⟩, hd0, hdX⟩
  · rintro ⟨n, d⟩ hx
    simp only [mem_sigma, mem_Icc] at hx
    have hd0 : 0 < d := hx.2.1
    simp [Nat.mul_div_cancel n hd0]
  · rintro ⟨m, d⟩ hy
    simp only [mem_sigma, mem_Icc, mem_filter, Nat.mem_divisors] at hy
    have hdm : d ∣ m := hy.2.1.1.1
    simp [Nat.div_mul_cancel hdm]
  · rintro ⟨n, d⟩ _
    simp only
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring

end ProductPolynomial


/-! ## The divisor-sum bound `Σ_{m ≤ Y} d_X(m)² ≤ Y (1 + log X)³` -/

section DivisorSum

/-! ### Common multiples in `[1, Y]` -/

/-- The number of `m ∈ [1, Y]` divisible by both `d₁` and `d₂` is at most
`Y · gcd(d₁,d₂) / (d₁ d₂)` (it equals `⌊Y / lcm(d₁,d₂)⌋`). -/
theorem card_filter_dvd_dvd_le (Y d₁ d₂ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (((Icc 1 Y).filter (fun m => d₁ ∣ m ∧ d₂ ∣ m)).card : ℝ)
      ≤ Y * Nat.gcd d₁ d₂ / (d₁ * d₂) := by
  have hL : 0 < Nat.lcm d₁ d₂ := Nat.lcm_pos h₁ h₂
  have hset : (Icc 1 Y).filter (fun m => d₁ ∣ m ∧ d₂ ∣ m)
      = (Ioc 0 Y).filter (fun m => Nat.lcm d₁ d₂ ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Nat.lcm_dvd_iff]
    constructor
    · rintro ⟨⟨hm1, hm2⟩, h3⟩
      exact ⟨⟨by omega, hm2⟩, h3⟩
    · rintro ⟨⟨hm1, hm2⟩, h3⟩
      exact ⟨⟨by omega, hm2⟩, h3⟩
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  have hcast : ((Y / Nat.lcm d₁ d₂ : ℕ) : ℝ) ≤ (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ) := Nat.cast_div_le
  refine le_trans hcast (le_of_eq ?_)
  have hgl : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * d₂ := by
    exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
  have hg : (0:ℝ) < Nat.gcd d₁ d₂ := by exact_mod_cast Nat.gcd_pos_of_pos_left d₂ h₁
  have hL' : (0:ℝ) < Nat.lcm d₁ d₂ := by exact_mod_cast hL
  rw [← hgl, div_eq_div_iff hL'.ne' (by positivity)]
  ring

/-! ### `gcd` is one of the common divisors -/

/-- `gcd d₁ d₂` is one term of the sum of the common divisors of `d₁` and `d₂`. -/
theorem gcd_le_sum_dvd (d₁ d₂ : ℕ) (h₁ : 0 < d₁) :
    (Nat.gcd d₁ d₂ : ℝ) ≤ ∑ g ∈ d₁.divisors.filter (· ∣ d₂), (g : ℝ) := by
  have hmem : Nat.gcd d₁ d₂ ∈ d₁.divisors.filter (· ∣ d₂) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_left d₁ d₂, h₁.ne'⟩, Nat.gcd_dvd_right d₁ d₂⟩
  exact Finset.single_le_sum (fun g _ => Nat.cast_nonneg g) hmem

/-- Indexed over `Icc 1 X` (the form used in `sum_gcd_div_le`): for `1 ≤ d₁ ≤ X`,
`gcd d₁ d₂ ≤ ∑_{g ≤ X} [g ∣ d₁ ∧ g ∣ d₂] g`. -/
theorem gcd_le_sum_Icc {X d₁ d₂ : ℕ} (h₁ : 0 < d₁) (hX : d₁ ≤ X) :
    (Nat.gcd d₁ d₂ : ℝ) ≤ ∑ g ∈ Icc 1 X, if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0 := by
  have hg : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ h₁
  have hmem : Nat.gcd d₁ d₂ ∈ Icc 1 X := by
    rw [Finset.mem_Icc]
    exact ⟨hg, le_trans (Nat.le_of_dvd h₁ (Nat.gcd_dvd_left d₁ d₂)) hX⟩
  have h : (if Nat.gcd d₁ d₂ ∣ d₁ ∧ Nat.gcd d₁ d₂ ∣ d₂ then ((Nat.gcd d₁ d₂ : ℕ) : ℝ) else 0)
      ≤ ∑ g ∈ Icc 1 X, if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0 :=
    Finset.single_le_sum (f := fun g => if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0)
      (fun g _ => by split_ifs <;> positivity) hmem
  rwa [if_pos ⟨Nat.gcd_dvd_left d₁ d₂, Nat.gcd_dvd_right d₁ d₂⟩] at h

/-! ### Harmonic sum over the multiples of `g` -/

/-- `∑_{d ≤ X, g ∣ d} 1/d ≤ (1/g)(1 + log X)`. -/
theorem sum_div_of_dvd_le (X g : ℕ) (hg : 0 < g) :
    ∑ d ∈ (Icc 1 X).filter (g ∣ ·), (1 / (d : ℝ)) ≤ (1 / g) * (1 + Real.log X) := by
  have hsub : (Icc 1 X).filter (g ∣ ·) ⊆ (Icc 1 X).image (fun e => g * e) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdX⟩, ⟨e, rfl⟩⟩ := hd
    rw [Finset.mem_image]
    refine ⟨e, ?_, rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hd1
      · exact h
    · calc e ≤ g * e := Nat.le_mul_of_pos_left e hg
        _ ≤ X := hdX
  have hinj : Set.InjOn (fun e => g * e) (Icc 1 X) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hg hab
  calc ∑ d ∈ (Icc 1 X).filter (g ∣ ·), (1 / (d : ℝ))
      ≤ ∑ d ∈ (Icc 1 X).image (fun e => g * e), (1 / (d : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    _ = ∑ e ∈ Icc 1 X, (1 / ((g * e : ℕ) : ℝ)) := Finset.sum_image hinj
    _ = (1 / g) * ∑ e ∈ Icc 1 X, (e : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        push_cast
        rw [one_div, one_div, mul_inv]
    _ ≤ (1 / g) * (1 + Real.log X) := by
        gcongr
        exact M1.sum_inv_le X

/-! ### The gcd double sum -/

/-- Pointwise identity used in `sum_gcd_div_le`. -/
theorem ite_and_div_eq (g d₁ d₂ : ℕ) :
    (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) / (d₁ * d₂)
      = (g : ℝ) * ((if g ∣ d₁ then 1 / (d₁ : ℝ) else 0) * (if g ∣ d₂ then 1 / (d₂ : ℝ) else 0)) := by
  by_cases h1 : g ∣ d₁
  · by_cases h2 : g ∣ d₂
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]; ring
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring

/-- `∑_{d₁,d₂ ≤ X} gcd(d₁,d₂)/(d₁ d₂) ≤ (1 + log X)³`. -/
theorem sum_gcd_div_le (X : ℕ) :
    ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, (Nat.gcd d₁ d₂ : ℝ) / (d₁ * d₂) ≤ (1 + Real.log X) ^ 3 := by
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0
    simp
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hXpos)
  -- `S g = ∑_{d ≤ X, g ∣ d} 1/d`
  set S : ℕ → ℝ := fun g => ∑ d ∈ Icc 1 X, if g ∣ d then 1 / (d : ℝ) else 0 with hS
  have hS_nonneg : ∀ g, 0 ≤ S g := fun g =>
    Finset.sum_nonneg fun d _ => by split_ifs <;> positivity
  have hS_le : ∀ g ∈ Icc 1 X, S g ≤ (1 / g) * (1 + Real.log X) := by
    intro g hg
    have hg0 : 0 < g := (Finset.mem_Icc.mp hg).1
    simp only [hS]
    rw [← Finset.sum_filter]
    exact sum_div_of_dvd_le X g hg0
  calc ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, (Nat.gcd d₁ d₂ : ℝ) / (d₁ * d₂)
      ≤ ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, ∑ g ∈ Icc 1 X,
          (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) / (d₁ * d₂) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        rw [← Finset.sum_div]
        have hd₁ := Finset.mem_Icc.mp hd₁
        exact div_le_div_of_nonneg_right (gcd_le_sum_Icc hd₁.1 hd₁.2) (by positivity)
    _ = ∑ g ∈ Icc 1 X, ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X,
          (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) / (d₁ * d₂) := Finset.sum_comm_cycle
    _ = ∑ g ∈ Icc 1 X, (g : ℝ) * (S g * S g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [hS]
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        exact ite_and_div_eq g d₁ d₂
    _ ≤ ∑ g ∈ Icc 1 X, (g : ℝ) *
          (((1 / g) * (1 + Real.log X)) * ((1 / g) * (1 + Real.log X))) := by
        refine Finset.sum_le_sum fun g hg => ?_
        have h := hS_le g hg
        have h0 := hS_nonneg g
        exact mul_le_mul_of_nonneg_left (mul_le_mul h h h0 (le_trans h0 h)) (Nat.cast_nonneg g)
    _ = (1 + Real.log X) ^ 2 * ∑ g ∈ Icc 1 X, (g : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g hg => ?_
        have hg0 : (g : ℝ) ≠ 0 := by
          have := (Finset.mem_Icc.mp hg).1
          exact_mod_cast (by omega : g ≠ 0)
        have hinv : (g : ℝ) * (g : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hg0
        linear_combination ((1 + Real.log X) ^ 2 * (g : ℝ)⁻¹) * hinv
    _ ≤ (1 + Real.log X) ^ 2 * (1 + Real.log X) := by
        gcongr
        exact M1.sum_inv_le X
    _ = (1 + Real.log X) ^ 3 := by ring

/-! ### The divisor-sum bound -/

/-- `dX X m` counts the `d ∈ [1, X]` dividing `m` (for `m ≠ 0`). -/
theorem dX_eq_card_filter {X m : ℕ} (hm : 0 < m) :
    dX X m = ((Icc 1 X).filter (· ∣ m)).card := by
  unfold dX
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hdX⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm, hdX⟩, hd⟩
  · rintro ⟨⟨_, hdX⟩, hd⟩
    exact ⟨⟨hd, hm.ne'⟩, hdX⟩

/-- `dX X m = ∑_{d ≤ X} [d ∣ m]` as a real number (for `m ≠ 0`). -/
theorem dX_eq_sum {X m : ℕ} (hm : 0 < m) :
    (dX X m : ℝ) = ∑ d ∈ Icc 1 X, if d ∣ m then (1 : ℝ) else 0 := by
  rw [dX_eq_card_filter hm, Finset.sum_boole]

/-- `∑_{m ≤ Y} dX(X,m)² ≤ Y (1 + log X)³`.  The logarithm is in `X`, not `Y`. -/
theorem sum_dX_sq_le (X Y : ℕ) :
    ∑ m ∈ Icc 1 Y, (dX X m : ℝ) ^ 2 ≤ Y * (1 + Real.log X) ^ 3 := by
  calc ∑ m ∈ Icc 1 Y, (dX X m : ℝ) ^ 2
      = ∑ m ∈ Icc 1 Y, ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X,
          (if d₁ ∣ m ∧ d₂ ∣ m then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
        rw [dX_eq_sum hm0, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h1 : d₁ ∣ m <;> by_cases h2 : d₂ ∣ m <;> simp [h1, h2]
    _ = ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, ∑ m ∈ Icc 1 Y,
          (if d₁ ∣ m ∧ d₂ ∣ m then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X,
          ((((Icc 1 Y).filter (fun m => d₁ ∣ m ∧ d₂ ∣ m)).card : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
        rw [Finset.sum_boole]
    _ ≤ ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, (Y : ℝ) * Nat.gcd d₁ d₂ / (d₁ * d₂) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        exact card_filter_dvd_dvd_le Y d₁ d₂ (Finset.mem_Icc.mp hd₁).1 (Finset.mem_Icc.mp hd₂).1
    _ = Y * ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, (Nat.gcd d₁ d₂ : ℝ) / (d₁ * d₂) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        ring
    _ ≤ Y * (1 + Real.log X) ^ 3 := by
        gcongr
        exact sum_gcd_div_le X

end DivisorSum


/-! ## Partial summation with generic weights -/

section PartialSummation

/-! #### Abel summation with generic weights -/

set_option linter.unusedVariables false in
/-- Partial summation: if `0 ≤ w`, `∑_{m ≤ Y} w m ≤ Y L` for every `Y`, and `g ≥ 0` is
antitone, then `∑_{m ≤ M} w m g m ≤ L ∑_{m ≤ M} g m`. -/
theorem sum_mul_le_of_partial_sums {w g : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) (hg : ∀ m, 0 ≤ g m) (hanti : Antitone g)
    (M : ℕ) : ∑ m ∈ Icc 1 M, w m * g m ≤ L * ∑ m ∈ Icc 1 M, g m := by
  -- strengthened invariant: the slack `(M L − W(M)) g M` is carried along
  have key : ∀ M : ℕ, ∑ m ∈ Icc 1 M, w m * g m + ((M:ℝ) * L - ∑ m ∈ Icc 1 M, w m) * g M
      ≤ L * ∑ m ∈ Icc 1 M, g m := by
    intro M
    induction M with
    | zero =>
      simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, Nat.cast_zero,
        zero_mul, sub_zero, add_zero, mul_zero, le_refl]
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 : g (M + 1) ≤ g M := hanti (Nat.le_succ M)
      have h2 : 0 ≤ (M:ℝ) * L - ∑ m ∈ Icc 1 M, w m := sub_nonneg.mpr (hW M)
      have h3 := hg (M + 1)
      have h4 := mul_le_mul_of_nonneg_left h1 h2
      push_cast
      nlinarith [h4, ih, h3, hL]
  have h := key M
  have h2 : 0 ≤ (M:ℝ) * L - ∑ m ∈ Icc 1 M, w m := sub_nonneg.mpr (hW M)
  have h3 := mul_nonneg h2 (hg M)
  linarith

/-- Tail version of `sum_mul_le_of_partial_sums` (start at `X`): the price of starting late is the single term
`(X+1) g (X+1)`. -/
theorem sum_mul_le_of_partial_sums_tail {w g : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) (hg : ∀ m, 0 ≤ g m) (hanti : Antitone g)
    (X M : ℕ) :
    ∑ m ∈ Ioc X M, w m * g m ≤ L * ((X + 1) * g (X + 1) + ∑ m ∈ Ioc X M, g m) := by
  have hLg : 0 ≤ L * (((X:ℝ) + 1) * g (X + 1)) :=
    mul_nonneg hL (mul_nonneg (by positivity) (hg _))
  rcases lt_or_ge M X with hMX | hXM
  · rw [Finset.Ioc_eq_empty_of_le hMX.le, Finset.sum_empty, Finset.sum_empty, add_zero]
    exact hLg
  · -- antitone majorant: constant `g (X+1)` up to `X`, then `g`
    set g' : ℕ → ℝ := fun m => if m ≤ X then g (X + 1) else g m with hg'_def
    have hg' : ∀ m, 0 ≤ g' m := by
      intro m
      simp only [hg'_def]
      split_ifs <;> exact hg _
    have hanti' : Antitone g' := by
      intro a b hab
      simp only [hg'_def]
      by_cases ha : a ≤ X
      · by_cases hb : b ≤ X
        · rw [if_pos ha, if_pos hb]
        · rw [if_pos ha, if_neg hb]
          exact hanti (by omega)
      · have hb : ¬ b ≤ X := by omega
        rw [if_neg ha, if_neg hb]
        exact hanti hab
    have h0 := sum_mul_le_of_partial_sums hw hL hW hg' hanti' M
    have eIcc : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => Finset.Icc_add_one_left_eq_Ioc 0 n
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ m ∈ Icc 1 M, f m = ∑ m ∈ Icc 1 X, f m + ∑ m ∈ Ioc X M, f m := by
      intro f
      rw [eIcc M, eIcc X, Finset.sum_Ioc_consecutive f (Nat.zero_le X) hXM]
    have e1 : ∑ m ∈ Icc 1 M, w m * g' m
        = ∑ m ∈ Icc 1 X, w m * g (X + 1) + ∑ m ∈ Ioc X M, w m * g m := by
      rw [hsplit]
      congr 1
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_pos (Finset.mem_Icc.mp hm).2]
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_neg (not_le.mpr (Finset.mem_Ioc.mp hm).1)]
    have e2 : ∑ m ∈ Icc 1 M, g' m = (X:ℝ) * g (X + 1) + ∑ m ∈ Ioc X M, g m := by
      rw [hsplit]
      congr 1
      · calc ∑ m ∈ Icc 1 X, g' m = ∑ m ∈ Icc 1 X, g (X + 1) :=
              Finset.sum_congr rfl (fun m hm => by
                simp only [hg'_def, if_pos (Finset.mem_Icc.mp hm).2])
          _ = (X:ℝ) * g (X + 1) := by simp [Finset.sum_const, Nat.card_Icc]
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_neg (not_le.mpr (Finset.mem_Ioc.mp hm).1)]
    have h3 : 0 ≤ ∑ m ∈ Icc 1 X, w m * g (X + 1) :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hw m) (hg _))
    rw [e1, e2] at h0
    have h4 : 0 ≤ L * g (X + 1) := mul_nonneg hL (hg _)
    nlinarith [h0, h3, h4]

/-! #### The tail `∑_{m > X} w m m^{-2σ}` -/

/-- Integral comparison for the tail: `∑_{X < m ≤ M} m^{-2σ} ≤ X^{1-2σ}/(2σ-1)` for `σ > 1/2`,
`1 ≤ X ≤ M`. -/
theorem sum_Ioc_rpow_le {X M : ℕ} (hX : 1 ≤ X) (hXM : X ≤ M) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) ≤ (X:ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-2 * σ)) (Set.Icc (X:ℝ) (M:ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono ?_
    intro x hx
    exact Set.mem_Ioi.mpr (by linarith [hx.1])
  have hint := AntitoneOn.sum_le_integral_Ico hXM hanti
  have hsum : ∑ i ∈ Ico X M, (((i + 1 : ℕ) : ℝ)) ^ (-2 * σ)
      = ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) := by
    rw [Finset.sum_Ico_add' (fun x : ℕ => (x:ℝ) ^ (-2 * σ)) X M 1,
      Finset.Ico_add_one_add_one_eq_Ioc]
  rw [hsum] at hint
  refine le_trans hint ?_
  have hne : -2 * σ ≠ -1 := by intro h; linarith
  have hnot : (0:ℝ) ∉ Set.uIcc (X:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hXM)]
    intro h
    have := (Set.mem_Icc.mp h).1
    linarith
  rw [integral_rpow (Or.inr ⟨hne, hnot⟩)]
  rw [show (-2 * σ + 1) = -(2 * σ - 1) by ring, show (1 - 2 * σ) = -(2 * σ - 1) by ring,
    div_neg, ← neg_div, neg_sub]
  have hM0 : 0 ≤ (M:ℝ) ^ (-(2 * σ - 1)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- Tail of the weighted sum against `m^{-2σ}`:
`∑_{X < m ≤ M} w m m^{-2σ} ≤ (2 + 1/(2σ-1)) L X^{1-2σ}`. -/
theorem tail_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) {X M : ℕ}
    (hX : 1 ≤ X) :
    ∑ m ∈ Ioc X M, w m * (m : ℝ) ^ (-2 * σ)
      ≤ (2 + 1 / (2 * σ - 1)) * L * (X : ℝ) ^ (1 - 2 * σ) := by
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hXpow : 0 ≤ (X:ℝ) ^ (1 - 2 * σ) := Real.rpow_nonneg hX0.le _
  have hC : 0 ≤ 2 + 1 / (2 * σ - 1) := by positivity
  rcases le_or_gt M X with hMX | hXM
  · rw [Finset.Ioc_eq_empty_of_le hMX, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC hL) hXpow
  · -- `g m = m^{-2σ}`, patched to `1` at `m = 0` (Mathlib's `0 ^ (-2σ) = 0` would break
    -- antitonicity on `ℕ`); on `Ioc X M` and at `X + 1` it agrees with `m^{-2σ}` since `1 ≤ X`
    set g : ℕ → ℝ := fun m => if m = 0 then 1 else (m:ℝ) ^ (-2 * σ) with hg_def
    have hg : ∀ m, 0 ≤ g m := by
      intro m
      simp only [hg_def]
      split_ifs
      · norm_num
      · exact Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hanti : Antitone g := by
      intro a b hab
      simp only [hg_def]
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb
          exact le_rfl
        · rw [if_pos rfl, if_neg (by omega)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb) (by linarith)
      · have hb : 0 < b := lt_of_lt_of_le ha hab
        rw [if_neg (by omega), if_neg (by omega)]
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha) (by exact_mod_cast hab)
          (by linarith)
    have h0 := sum_mul_le_of_partial_sums_tail hw hL hW hg hanti X M
    have eg : ∀ m ∈ Ioc X M, g m = (m:ℝ) ^ (-2 * σ) := by
      intro m hm
      have : 0 < m := lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hm).1
      simp only [hg_def, if_neg (show m ≠ 0 by omega)]
    have eg1 : g (X + 1) = ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) := by
      simp only [hg_def, if_neg (show X + 1 ≠ 0 by omega)]
    have e1 : ∑ m ∈ Ioc X M, w m * g m = ∑ m ∈ Ioc X M, w m * (m:ℝ) ^ (-2 * σ) :=
      Finset.sum_congr rfl (fun m hm => by rw [eg m hm])
    have e2 : ∑ m ∈ Ioc X M, g m = ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) :=
      Finset.sum_congr rfl (fun m hm => eg m hm)
    rw [e1, e2, eg1] at h0
    have h1 := sum_Ioc_rpow_le hX hXM.le hσ
    have h2 : ((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) ≤ (X:ℝ) ^ (1 - 2 * σ) := by
      have hX1 : (0:ℝ) < (X:ℝ) + 1 := by linarith
      have e : ((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) = ((X:ℝ) + 1) ^ (1 - 2 * σ) := by
        push_cast
        rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add_one hX1.ne', mul_comm]
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos hX0 (by linarith) (by linarith)
    have hLP : 0 ≤ L * (X:ℝ) ^ (1 - 2 * σ) := mul_nonneg hL hXpow
    calc ∑ m ∈ Ioc X M, w m * (m:ℝ) ^ (-2 * σ)
        ≤ L * (((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ)
            + ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ)) := h0
      _ ≤ L * ((X:ℝ) ^ (1 - 2 * σ) + (X:ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h1) hL
      _ = (1 + 1 / (2 * σ - 1)) * L * (X:ℝ) ^ (1 - 2 * σ) := by ring
      _ ≤ (2 + 1 / (2 * σ - 1)) * L * (X:ℝ) ^ (1 - 2 * σ) := by nlinarith [hLP]

/-! #### The off-diagonal weight `(m+1) m^{-2σ}` -/

/-- Weighted off-diagonal sum:
`∑_{m ≤ M} (m+1) w m m^{-2σ} ≤ (2 + 2/(2-2σ)) L M^{2-2σ}` for `1/2 < σ < 1`, `1 ≤ M`. -/
theorem weight_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (w m * (m : ℝ) ^ (-2 * σ))
      ≤ (2 + 2 / (2 - 2 * σ)) * L * (M : ℝ) ^ (2 - 2 * σ) := by
  -- `g m = (m+1) m^{-2σ}`, patched at `m = 0` so that it is antitone on all of `ℕ`
  set g : ℕ → ℝ := fun m => if m = 0 then 2 else ((m:ℝ) + 1) * (m:ℝ) ^ (-2 * σ) with hg_def
  have hterm : ∀ m : ℕ, 0 < m →
      ((m:ℝ) + 1) * (m:ℝ) ^ (-2 * σ) = (m:ℝ) ^ (1 - 2 * σ) + (m:ℝ) ^ (-2 * σ) := by
    intro m hm
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add_one hm'.ne']
    ring
  have hg : ∀ m, 0 ≤ g m := by
    intro m
    simp only [hg_def]
    split_ifs
    · norm_num
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hanti : Antitone g := by
    intro a b hab
    simp only [hg_def]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        exact le_rfl
      · rw [if_pos rfl, if_neg (by omega), hterm b hb]
        have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
        have h1 := Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith : 1 - 2 * σ ≤ 0)
        have h2 := Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith : -2 * σ ≤ 0)
        linarith
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      rw [if_neg (by omega), if_neg (by omega), hterm a ha, hterm b hb]
      have ha' : (0:ℝ) < a := by exact_mod_cast ha
      have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
      have h1 := Real.rpow_le_rpow_of_nonpos ha' hab' (by linarith : 1 - 2 * σ ≤ 0)
      have h2 := Real.rpow_le_rpow_of_nonpos ha' hab' (by linarith : -2 * σ ≤ 0)
      linarith
  have h0 := sum_mul_le_of_partial_sums hw hL hW hg hanti M
  have e1 : ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (w m * (m : ℝ) ^ (-2 * σ))
      = ∑ m ∈ Icc 1 M, w m * g m := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [hg_def, if_neg (show m ≠ 0 by omega)]
    ring
  have e2 : ∑ m ∈ Icc 1 M, g m = ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (m : ℝ) ^ (-2 * σ) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [hg_def, if_neg (show m ≠ 0 by omega)]
  have h1 := M1.sum_weight_le_logfree σ hσ hσ1 M
  have hMpow : 1 ≤ (M:ℝ) ^ (2 - 2 * σ) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by linarith)
  have hd : 0 < 2 - 2 * σ := by linarith
  have hdiv : 0 ≤ 2 / (2 - 2 * σ) := by positivity
  have hkey : 2 * (1 + (M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))
      ≤ (2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ) := by
    have e : (2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ)
        = 2 * (M:ℝ) ^ (2 - 2 * σ) + 2 * ((M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)) := by ring
    rw [e]
    linarith
  rw [e1]
  calc ∑ m ∈ Icc 1 M, w m * g m ≤ L * ∑ m ∈ Icc 1 M, g m := h0
    _ = L * ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (m : ℝ) ^ (-2 * σ) := by rw [e2]
    _ ≤ L * (2 * (1 + (M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))) := mul_le_mul_of_nonneg_left h1 hL
    _ ≤ L * ((2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ)) := mul_le_mul_of_nonneg_left hkey hL
    _ = (2 + 2 / (2 - 2 * σ)) * L * (M : ℝ) ^ (2 - 2 * σ) := by ring

end PartialSummation


/-! ## Window mean squares of `S_N · M_X`, `(ζ − S_N) · M_X` and `f_X` -/

section Windows

/-! ### The window translation `t ↦ u = t − a` -/

/-- Translating the window `[a, a+ℓ]` to `[0, ℓ]` inside the Dirichlet polynomial:
`m^{-(σ + (u+a)i)} = (m^{-σ} · m^{-ai}) · m^{-ui}`. -/
theorem integral_window_eq (c : ℕ → ℂ) (M : ℕ) (σ a ℓ : ℝ) :
    ∫ t in a..(a + ℓ), ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 =
    ∫ u in (0:ℝ)..ℓ, ‖∑ m ∈ Icc 1 M,
      (c m * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)) * (m : ℂ) ^ (-(u : ℂ) * I)‖ ^ 2
    := by
  have hpt : ∀ u : ℝ,
      ‖∑ m ∈ Icc 1 M, (c m * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I))
        * (m : ℂ) ^ (-(u : ℂ) * I)‖ ^ 2
        = ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + ((u + a : ℝ) : ℂ) * I))‖ ^ 2 := by
    intro u
    congr 2
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm0 : 0 < m := (Finset.mem_Icc.1 hm).1
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    rw [M1.cpow_neg_add_eq m hm0 σ (u + a)]
    have e : -(((u + a : ℝ) : ℂ)) * I = -(a : ℂ) * I + -(u : ℂ) * I := by push_cast; ring
    rw [e, Complex.cpow_add _ _ hm']
    ring
  symm
  calc ∫ u in (0:ℝ)..ℓ, ‖∑ m ∈ Icc 1 M,
          (c m * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I))
            * (m : ℂ) ^ (-(u : ℂ) * I)‖ ^ 2
      = ∫ u in (0:ℝ)..ℓ,
          (fun t : ℝ => ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2) (u + a) :=
        intervalIntegral.integral_congr (fun u _ => hpt u)
    _ = ∫ t in (0:ℝ) + a..ℓ + a,
          (fun t : ℝ => ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2) t :=
        intervalIntegral.integral_comp_add_right
          (f := fun t : ℝ => ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2) a
    _ = ∫ t in a..(a + ℓ), ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 := by
        rw [zero_add, add_comm ℓ a]

/-! ### The mean square of the product polynomial `S_N · M_X` over a window -/

/-- Squared norm of the translated coefficient `cm · m^{-σ} · m^{-ia}`: `|cm|² m^{-2σ}`. -/
theorem norm_coeff_sq (N X : ℕ) (σ a : ℝ) {m : ℕ} (hm : 0 < m) :
    ‖((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)‖ ^ 2
      = |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ) := by
  rw [norm_mul, norm_mul, M1.norm_cpow_neg_mul_I m hm a, mul_one, mul_pow, M1.norm_sq_rpow,
    Complex.norm_intCast]

/-- `|cm|² ≤ dX²` (`abs_cm_le` squared). -/
theorem abs_cm_sq_le (N X m : ℕ) : |((cm N X m : ℤ) : ℝ)| ^ 2 ≤ (dX X m : ℝ) ^ 2 :=
  pow_le_pow_left₀ (abs_nonneg _) (abs_cm_le N X m) 2

/-- Mean square of the product polynomial `S_N · M_X` on the window `[a, a+ℓ]`,
`Re s = σ ≥ σ₁`, `1/2 < σ₁ < 1`, `1 ≤ X ≤ N`: the diagonal is `ℓ · (1 + o(1))` as `X → ∞`
(the `1` is the coefficient of `m = 1`; all other coefficients `m ≤ X` vanish), the
off-diagonal is the Montgomery–Vaughan term. -/
theorem meanSquare_prodPoly {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ)
    {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ t in a..(a + ℓ), ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2
      ≤ ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁))
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
          * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) := by
  -- bookkeeping
  have hN : 1 ≤ N := le_trans hX hXN
  have hXM : X ≤ N * X := Nat.le_mul_of_pos_left X (by omega)
  have hM : 1 ≤ N * X := le_trans hX hXM
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hL : 0 ≤ (1 + Real.log X) ^ 3 := pow_nonneg (by linarith) 3
  -- the weight `w m = dX X m ^ 2` and its partial-sum bound `sum_dX_sq_le`
  have hw : ∀ m : ℕ, 0 ≤ (dX X m : ℝ) ^ 2 := fun m => sq_nonneg _
  have hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, (dX X m : ℝ) ^ 2 ≤ Y * (1 + Real.log X) ^ 3 :=
    fun Y => sum_dX_sq_le X Y
  -- pointwise: `|cm|² m^{-2σ} ≤ dX² m^{-2σ₁}` for `m ≥ 1` (`abs_cm_le` and `σ₁ ≤ σ`)
  have hpt : ∀ m ∈ Icc 1 (N * X),
      |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ (dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    exact mul_le_mul (abs_cm_sq_le N X m)
      (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
      (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
  -- the diagonal: exactly `1` below `X` (`cm_eq_of_le`), the tail by `tail_sum_le`
  have hdiag : ∑ m ∈ Icc 1 (N * X), |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)
      ≤ 1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁) := by
    have eIcc : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => Finset.Icc_add_one_left_eq_Ioc 0 n
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ m ∈ Icc 1 (N * X), f m = ∑ m ∈ Icc 1 X, f m + ∑ m ∈ Ioc X (N * X), f m := by
      intro f
      rw [eIcc (N * X), eIcc X, Finset.sum_Ioc_consecutive f (Nat.zero_le X) hXM]
    have hfirst : ∑ m ∈ Icc 1 X, |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ) = 1 := by
      rw [Finset.sum_eq_single 1]
      · simp [cm_eq_of_le hXN hX]
      · intro m hm hm1
        simp [cm_eq_of_le hXN (Finset.mem_Icc.mp hm).2, hm1]
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hX⟩) h
    have htail : ∑ m ∈ Ioc X (N * X), |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ ∑ m ∈ Ioc X (N * X), (dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁) := by
      refine Finset.sum_le_sum fun m hm => hpt m ?_
      have h := Finset.mem_Ioc.mp hm
      exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
    have hD1 : ∑ m ∈ Ioc X (N * X), (dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁)
        ≤ (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁) :=
      tail_sum_le (w := fun m => (dX X m : ℝ) ^ 2) hw hL hW h1 (X := X) (M := N * X) hX
    rw [hsplit, hfirst]
    linarith
  -- the off-diagonal: `weight_sum_le`
  have hoff : ∑ m ∈ Icc 1 (N * X),
      ((m : ℝ) + 1) * (|((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ))
        ≤ (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) := by
    have hD2 : ∑ m ∈ Icc 1 (N * X), ((m : ℝ) + 1) * ((dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁))
        ≤ (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) :=
      weight_sum_le (w := fun m => (dX X m : ℝ) ^ 2) hw hL hW h1 h1' hM
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) hD2
    exact mul_le_mul_of_nonneg_left (hpt m hm) (by positivity)
  -- assemble: `S_mul_Mx_eq`, `integral_window_eq`, Montgomery–Vaughan, then the two sums
  calc ∫ t in a..(a + ℓ), ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2
      = ∫ t in a..(a + ℓ), ‖∑ m ∈ Icc 1 (N * X),
          ((cm N X m : ℤ) : ℂ) * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => by rw [S_mul_Mx_eq])
    _ = ∫ u in (0:ℝ)..ℓ, ‖∑ m ∈ Icc 1 (N * X),
          (((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I))
            * (m : ℂ) ^ (-(u : ℂ) * I)‖ ^ 2 :=
        integral_window_eq (fun m => ((cm N X m : ℤ) : ℂ)) (N * X) σ a ℓ
    _ ≤ ℓ * ∑ m ∈ Icc 1 (N * X),
          ‖((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)‖ ^ 2
        + 26 * ∑ m ∈ Icc 1 (N * X), ((m:ℝ) + 1) *
          ‖((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)‖ ^ 2 :=
        M1.dirichlet_meanSquare_le
          (fun m => ((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I))
          (N * X) ℓ
    _ = ℓ * ∑ m ∈ Icc 1 (N * X), |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)
        + 26 * ∑ m ∈ Icc 1 (N * X),
          ((m : ℝ) + 1) * (|((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)) := by
        congr 1
        · congr 1
          exact Finset.sum_congr rfl fun m hm => norm_coeff_sq N X σ a (Finset.mem_Icc.mp hm).1
        · congr 1
          exact Finset.sum_congr rfl fun m hm => by
            rw [norm_coeff_sq N X σ a (Finset.mem_Icc.mp hm).1]
    _ ≤ ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁))
        + 26 * ((2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
          * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁)) :=
        add_le_add (mul_le_mul_of_nonneg_left hdiag hℓ)
          (mul_le_mul_of_nonneg_left hoff (by norm_num))
    _ = ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁))
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
          * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) := by ring

open Zeta23.BL

/-! ### The η-weighted square inequality -/

/-- `‖a + b‖² ≤ (1 + η)‖a‖² + (1 + 1/η)‖b‖²` for every `η > 0`
(pattern `M2.norm_add4_sq_le`). -/
theorem norm_add_sq_le_eta (a b : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖a + b‖ ^ 2 ≤ (1 + η) * ‖a‖ ^ 2 + (1 + 1 / η) * ‖b‖ ^ 2 := by
  have h : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  have key : 2 * ‖a‖ * ‖b‖ - η * ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 / η := by
    rw [le_div_iff₀ hη]
    nlinarith [sq_nonneg (η * ‖a‖ - ‖b‖)]
  have e : (1 + 1 / η) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / η := by ring
  calc ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ ≤ (1 + η) * ‖a‖ ^ 2 + (1 + 1 / η) * ‖b‖ ^ 2 := by rw [e]; nlinarith [key]

/-- `‖M_X(s)‖ ≤ 1 + X^{1-σ₁}/(1-σ₁)` for `Re s ≥ σ₁`, `1/2 < σ₁ < 1`. -/
theorem norm_Mx_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) {s : ℂ} (hs : σ₁ ≤ s.re)
    (X : ℕ) : ‖Mx X s‖ ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) := by
  unfold Mx
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Icc 1 X, ‖((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-σ₁) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.1 hn).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, neg_re]
    have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-σ₁) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hpos : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc ‖((μ n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hμ hpos
      _ = (n : ℝ) ^ (-s.re) := one_mul _
      _ ≤ (n : ℝ) ^ (-σ₁) := hpow
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have h := M1.sum_Icc_rpow_le (N := X) (a := -σ₁) (by linarith) (by linarith)
  have e : -σ₁ + 1 = 1 - σ₁ := by ring
  rw [e] at h
  exact h

/-! ### The window mean square of `(ζ − S_N)·M_X` -/

/-- `t ↦ ‖(ζ − S_N)(σ+it)·M_X(σ+it)‖²` is continuous on `[a, b]`, `a > 0`
(the pole `s = 1` has `t = 0`). -/
lemma continuousOn_B_window (σ : ℝ) (N X : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ =>
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) (Set.Icc a b) := by
  have hline : Continuous (fun t : ℝ => (σ:ℂ) + t * I) := by fun_prop
  have hζ : ContinuousOn (fun t : ℝ => riemannZeta ((σ:ℂ) + t * I)) (Set.Icc a b) :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta (S := {z : ℂ | z ≠ 1}) (by simp)).continuousOn.comp
      hline.continuousOn (segment_mapsTo_ne_one ha)
  have hS : Continuous (fun t : ℝ => BLClosure.S N ((σ:ℂ) + t * I)) := by
    unfold BLClosure.S
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
  have hM : Continuous (fun t : ℝ => Mx X ((σ:ℂ) + t * I)) := by
    unfold Mx
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  exact ((hζ.sub hS.continuousOn).mul hM.continuousOn).norm.pow 2

/-- `∫_a^{a+ℓ} t⁻² dt ≤ 1/a` for `a > 0`, `ℓ ≥ 0` (pattern `integral_inv_sq_one`). -/
lemma integral_inv_sq_window {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) :
    ∫ t in a..(a + ℓ), (t ^ 2)⁻¹ ≤ 1 / a := by
  have hab : a ≤ a + ℓ := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a (a + ℓ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hderiv : ∀ x ∈ Set.uIcc a (a + ℓ), HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0:ℝ) < x).ne'
    have := (hasDerivAt_inv hx0).neg
    rw [neg_neg] at this
    exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have : 0 < (a + ℓ)⁻¹ := by positivity
  rw [one_div]
  linarith

/-- Window mean square of `(ζ − S_N)·M_X` on `Re s = σ ≥ σ₁`, `t ∈ [a, a+ℓ]`, `a ≥ 1`,
from the pointwise bound `‖M_X‖ ≤ 1 + X^{1−σ₁}/(1−σ₁)`, the main term `‖N^{1−s}/(s−1)‖ ≤
N^{1−σ₁}/t` (`M2.norm_P_le`) and the approximate-formula error `hE`. -/
theorem meanSquare_B_window {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ)
    {N X : ℕ} (hN : 1 ≤ N) {a ℓ : ℝ} (ha : 1 ≤ a) (hℓ : 0 ≤ ℓ) {C_G : ℝ} (hCG : 0 ≤ C_G)
    (hE : ∀ t ∈ Set.Icc a (a + ℓ),
      ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
        - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ)) :
    ∫ t in a..(a + ℓ), ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
  have hab : a ≤ a + ℓ := by linarith
  have ha0 : 0 < a := by linarith
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hB0 : 0 ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) := by
    have : 0 ≤ (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) (by linarith)
    linarith
  -- the pointwise bound on the window
  have hpt : ∀ t ∈ Set.Icc a (a + ℓ),
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
          * Mx X ((σ:ℂ) + t * I)‖ ^ 2
        ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hsre : σ₁ ≤ ((σ:ℂ) + t * I).re := by simpa using hσ
    have hM : ‖Mx X ((σ:ℂ) + t * I)‖ ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁) :=
      norm_Mx_le h1 h1' hsre X
    have hP : ‖(N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
        ≤ (N:ℝ) ^ (1 - σ₁) / t := by
      have e : (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)
          = (-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I)) := by
        rw [neg_div, ← div_neg, neg_sub]
      rw [e]
      exact M2.norm_P_le hσ ht0 hN
    have hR : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
        - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
        ≤ C_G * (N:ℝ) ^ (-σ₁) := by
      refine le_trans (hE t ht) (mul_le_mul_of_nonneg_left ?_ hCG)
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsplit : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
        ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := by
      calc ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
          = ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
              - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1))
              + (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
              - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖
              + ‖(N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ := norm_add_le _ _
        _ ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := add_le_add hR hP
    have hζS0 : 0 ≤ ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖ :=
      norm_nonneg _
    have hM0 : 0 ≤ ‖Mx X ((σ:ℂ) + t * I)‖ := norm_nonneg _
    have hxy0 : 0 ≤ C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t := by
      have := Real.rpow_nonneg hN0 (-σ₁)
      have := Real.rpow_nonneg hN0 (1 - σ₁)
      positivity
    have hprod : ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)‖
          * ‖Mx X ((σ:ℂ) + t * I)‖
        ≤ (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t)
          * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) :=
      mul_le_mul hsplit hM hM0 hxy0
    have hsq := pow_le_pow_left₀ (mul_nonneg hζS0 hM0) hprod 2
    rw [norm_mul]
    refine le_trans hsq ?_
    have e1 : ((N:ℝ) ^ (1 - σ₁) / t) ^ 2 = (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ := by
      rw [div_pow, M2.rpow_sq_eq hN0 (a := 1 - σ₁) (b := 2 - 2 * σ₁) (by ring), div_eq_mul_inv]
    have e2 : (C_G * (N:ℝ) ^ (-σ₁)) ^ 2 = C_G ^ 2 * (N:ℝ) ^ (-2 * σ₁) := by
      rw [mul_pow, M2.rpow_sq_eq hN0 (a := -σ₁) (b := -2 * σ₁) (by ring)]
    have key : (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t) ^ 2
        ≤ 2 * (((N:ℝ) ^ (1 - σ₁) / t) ^ 2 + (C_G * (N:ℝ) ^ (-σ₁)) ^ 2) := by
      nlinarith [sq_nonneg (C_G * (N:ℝ) ^ (-σ₁) - (N:ℝ) ^ (1 - σ₁) / t)]
    calc ((C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t)
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁))) ^ 2
        = (C_G * (N:ℝ) ^ (-σ₁) + (N:ℝ) ^ (1 - σ₁) / t) ^ 2
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 := by ring
      _ ≤ 2 * (((N:ℝ) ^ (1 - σ₁) / t) ^ 2 + (C_G * (N:ℝ) ^ (-σ₁)) ^ 2)
            * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 :=
          mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) := by
          rw [e1, e2]; ring
  -- integrability of both sides
  have hfi : IntervalIntegrable (fun t : ℝ =>
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) :=
    (continuousOn_B_window σ N X ha0).intervalIntegrable_of_Icc hab
  have hinv : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a (a + ℓ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine (continuousOn_pow 2).inv₀ (fun t ht => ?_)
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have h1i : IntervalIntegrable (fun t : ℝ => (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹)
      volume a (a + ℓ) := hinv.const_mul _
  have h2i : IntervalIntegrable (fun _ : ℝ => C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁))
      volume a (a + ℓ) := intervalIntegrable_const
  have hgi : IntervalIntegrable (fun t : ℝ =>
      2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)))
      volume a (a + ℓ) := (h1i.add h2i).const_mul _
  -- integrate
  calc ∫ t in a..(a + ℓ), ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
          * Mx X ((σ:ℂ) + t * I)‖ ^ 2
      ≤ ∫ t in a..(a + ℓ), 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁)) :=
        intervalIntegral.integral_mono_on hab hfi hgi hpt
    _ = 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) * (∫ t in a..(a + ℓ), (t ^ 2)⁻¹)
              + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1i h2i,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
          add_sub_cancel_left]
        ring
    _ ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ) := by
        have hI := integral_inv_sq_window ha0 hℓ
        have hNp : 0 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := Real.rpow_nonneg hN0 _
        have hmain : (N : ℝ) ^ (2 - 2 * σ₁) * (∫ t in a..(a + ℓ), (t ^ 2)⁻¹)
            ≤ (N : ℝ) ^ (2 - 2 * σ₁) / a := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left hI hNp
        have h2B : 0 ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h2B

/-! ### The window mean square of `f_X = ζ · M_X` with a free `η` -/

/-- `t ↦ ‖S_N(σ+it)·M_X(σ+it)‖²` is continuous (finite Dirichlet polynomials). -/
lemma continuous_A_window (σ : ℝ) (N X : ℕ) :
    Continuous (fun t : ℝ =>
      ‖BLClosure.S N ((σ:ℂ) + t * I) * Mx X ((σ:ℂ) + t * I)‖ ^ 2) := by
  have hS : Continuous (fun t : ℝ => BLClosure.S N ((σ:ℂ) + t * I)) := by
    unfold BLClosure.S
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)
  have hM : Continuous (fun t : ℝ => Mx X ((σ:ℂ) + t * I)) := by
    unfold Mx
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  exact (hS.mul hM).norm.pow 2

/-- `t ↦ ‖f_X(σ+it)‖²` is continuous on `[a, b]`, `a > 0` (the pole `s = 1` has `t = 0`). -/
lemma continuousOn_fz_window (σ : ℝ) (X : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => ‖fz X ((σ:ℂ) + t * I)‖ ^ 2) (Set.Icc a b) := by
  have hline : Continuous (fun t : ℝ => (σ:ℂ) + t * I) := by fun_prop
  have hζ : ContinuousOn (fun t : ℝ => riemannZeta ((σ:ℂ) + t * I)) (Set.Icc a b) :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta (S := {z : ℂ | z ≠ 1}) (by simp)).continuousOn.comp
      hline.continuousOn (segment_mapsTo_ne_one ha)
  have hM : Continuous (fun t : ℝ => Mx X ((σ:ℂ) + t * I)) := by
    unfold Mx
    refine continuous_finsetSum _ (fun n hn => ?_)
    have hn0 : (n:ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  unfold fz
  exact (hζ.mul hM.continuousOn).norm.pow 2

/-- Window mean square of the mollified zeta `f_X = ζ · M_X` on `Re s = σ ≥ σ₁`,
`t ∈ [a, a+ℓ]`, `a ≥ 1`, with a free weight `η > 0`: `f_X = S_N·M_X + (ζ − S_N)·M_X`, the
pointwise inequality `‖u + v‖² ≤ (1+η)‖u‖² + (1+1/η)‖v‖²` (`norm_add_sq_le_eta`), and the two window mean
squares `meanSquare_prodPoly` (product polynomial) and `meanSquare_B_window` (approximate-formula remainder). -/
theorem meanSquare_fz_window {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ)
    {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) {a ℓ : ℝ} (ha : 1 ≤ a) (hℓ : 0 ≤ ℓ) {C_G : ℝ}
    (hCG : 0 ≤ C_G)
    (hE : ∀ t ∈ Set.Icc a (a + ℓ),
      ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
        - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ))
    {η : ℝ} (hη : 0 < η) :
    ∫ t in a..(a + ℓ), ‖fz X ((σ : ℂ) + t * I)‖ ^ 2
      ≤ (1 + η) * (ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3
            * (X : ℝ) ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
            * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁))
        + (1 + 1 / η) * (2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ)) := by
  have hab : a ≤ a + ℓ := by linarith
  have ha0 : 0 < a := by linarith
  have hN : 1 ≤ N := le_trans hX hXN
  have hη1 : 0 ≤ 1 + η := by linarith
  have hη2 : 0 ≤ 1 + 1 / η := by
    have := one_div_pos.mpr hη
    linarith
  -- the splitting `f_X = S_N·M_X + (ζ − S_N)·M_X`
  have hfz : ∀ t : ℝ, fz X ((σ : ℂ) + t * I)
      = BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)
        + (riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
            * Mx X ((σ:ℂ) + t * I) := by
    intro t
    unfold fz
    ring
  -- the pointwise bound (`norm_add_sq_le_eta`)
  have hpt : ∀ t ∈ Set.Icc a (a + ℓ), ‖fz X ((σ : ℂ) + t * I)‖ ^ 2
      ≤ (1 + η) * ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2
        + (1 + 1 / η) * ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
            * Mx X ((σ:ℂ) + t * I)‖ ^ 2 := by
    intro t _
    rw [hfz t]
    exact norm_add_sq_le_eta _ _ hη
  -- integrability
  have hfi : IntervalIntegrable (fun t : ℝ => ‖fz X ((σ : ℂ) + t * I)‖ ^ 2)
      volume a (a + ℓ) :=
    (continuousOn_fz_window σ X ha0).intervalIntegrable_of_Icc hab
  have hAi : IntervalIntegrable (fun t : ℝ =>
      ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) :=
    (continuous_A_window σ N X).intervalIntegrable a (a + ℓ)
  have hBi : IntervalIntegrable (fun t : ℝ =>
      ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) :=
    (continuousOn_B_window σ N X ha0).intervalIntegrable_of_Icc hab
  have hAi' : IntervalIntegrable (fun t : ℝ =>
      (1 + η) * ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2)
      volume a (a + ℓ) := hAi.const_mul _
  have hBi' : IntervalIntegrable (fun t : ℝ =>
      (1 + 1 / η) * ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
        * Mx X ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) := hBi.const_mul _
  have hgi : IntervalIntegrable (fun t : ℝ =>
      (1 + η) * ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2
        + (1 + 1 / η) * ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
            * Mx X ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ) := hAi'.add hBi'
  -- the two window mean squares
  have hW2 := meanSquare_prodPoly h1 h1' hσ hX hXN a hℓ
  have hW5 := meanSquare_B_window (X := X) h1 h1' hσ hN ha hℓ hCG hE
  -- integrate
  calc ∫ t in a..(a + ℓ), ‖fz X ((σ : ℂ) + t * I)‖ ^ 2
      ≤ ∫ t in a..(a + ℓ),
          ((1 + η) * ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2
            + (1 + 1 / η) * ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
                * Mx X ((σ:ℂ) + t * I)‖ ^ 2) :=
        intervalIntegral.integral_mono_on hab hfi hgi hpt
    _ = (1 + η) * (∫ t in a..(a + ℓ),
            ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2)
          + (1 + 1 / η) * (∫ t in a..(a + ℓ),
            ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I))
                * Mx X ((σ:ℂ) + t * I)‖ ^ 2) := by
        rw [intervalIntegral.integral_add hAi' hBi', intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ ≤ (1 + η) * (ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3
            * (X : ℝ) ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
            * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁))
        + (1 + 1 / η) * (2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hW2 hη1) (mul_le_mul_of_nonneg_left hW5 hη2)


end Windows


/-! ## Zero orders: `zeta_order ρ ≤ divisor (f_X) ρ` -/

section MollifierOrder

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

/-- `M_X(s) ≠ 0` for `Re s ≥ 3` (and `X ≥ 1`): `‖M_X(s) − 1‖ ≤ 1 − 1/X < 1`. -/
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

/-- `M_X` is not locally identically zero anywhere: it is entire, `ℂ` is connected, and
`M_X(3) ≠ 0` (`Mx_ne_zero_of_le_re`). -/
theorem analyticOrderAt_Mx_ne_top {X : ℕ} (hX : 1 ≤ X) (z : ℂ) :
    analyticOrderAt (Mx X) z ≠ ⊤ := by
  refine (analyticOnNhd_Mx X).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (3 : ℂ)) (Set.mem_univ z) ?_
  rw [((analyticOnNhd_Mx X) 3 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
    (Mx_ne_zero_of_le_re hX (by simp))]
  exact ENat.zero_ne_top

/-- On a closed ball not containing `1`, the multiplicity of `ρ` as a zero of `ζ` is at most
the divisor of `fz X = ζ · M_X` at `ρ`: `ord_ρ(ζ · M_X) = ord_ρ ζ + ord_ρ M_X` with both orders
finite (`Zeta23.analyticOrderAt_riemannZeta_ne_top`, `analyticOrderAt_Mx_ne_top`), and `ord_ρ M_X ≥ 0`. -/
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

/-- A finite set of nontrivial zeros inside the ball contributes at most the full divisor
sum of `fz X` (pattern: `Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor`, with `≤` from `zeta_order_le_divisor_fz`
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

end MollifierOrder


/-! ## Jensen's disc inequality for `f_X` -/

section JensenDisc

/-- The centre of the Jensen disc is not a zero of `fz X` (`fz_lower_two`). -/
theorem fz_two_add_ne_zero {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : fz X (2 + t * I) ≠ 0 := by
  intro h0
  have h := fz_lower_two hX t
  rw [h0, norm_zero] at h
  norm_num at h

/-- Divisor form (the analogue of `Zeta23.BL.count_disc_le`): Jensen's disc inequality for
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

/-- For `t ≥ 3`, `0 < r < R < 3`, `X ≥ 4` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + tI) r`:
`(∑ ρ ∈ S, zeta_order ρ) · log (R/r) ≤ circleAverage (log ‖fz X‖) (2 + tI) R + π²/(3X)`
(pattern `Zeta23.BL.count_finset_le`, with `finset_sum_zeta_order_le_finsum_divisor_fz` in place of the ζ-divisor identity and the
centre bound `−log ‖fz X (2 + tI)‖ ≤ π²/(3X)` in place of `log 3`). -/
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

/-- The window form (pattern `Zeta23.BL.count_window_le`; `geom_facts` supplies the
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

end JensenDisc


/-! ## The majorant `Leps ε f = ½ log(ε² + ‖f‖²)` -/

section LepsMajorant

set_option linter.unusedVariables false in
/-- `log ‖f z‖ ≤ Leps ε f z` wherever `f z ≠ 0` (the hypothesis `hz` is needed because
`Real.log 0 = 0`, while `Leps ε f z = log ε < 0` there when `ε < 1`; `hε` is kept for the
signature). -/
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

/-- For `f` analytic on a neighbourhood of the closed ball with `f c ≠ 0`, the circle
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

/-- `x ↦ (1/2) log (ε² + x)` is concave on `Ici 0` (pattern:
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
/-- `(1/2) log (ε² + (1 + x)) ≤ (1/2) (ε² + x)`, from `log y ≤ y - 1` (the hypothesis
`hε` is not needed, since `ε² ≥ 0` anyway; it is kept for the signature). -/
theorem half_log_le_half {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    (1/2) * Real.log (ε ^ 2 + (1 + x)) ≤ (1/2) * (ε ^ 2 + x) := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ε ^ 2 + (1 + x))
  exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- Jensen's inequality for the concave `x ↦ (1/2) log (ε² + x)` on the interval average
over `[a, a + ℓ]`: the integral of `Leps ε f` along the vertical segment `Re = σ` is at most
`ℓ · (1/2) log (ε² + (mean square of ‖f‖ on the segment))`.  This is the step at which the
tree's Bohr–Landau proof (`Lz_le_half_sq`, `BohrLandauPartial.lean:1663`) threw the logarithm away. -/
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

end LepsMajorant


/-! ## Integrability of `Leps ε (f_X)` on circles and segments; Fubini -/

section Integrability

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

/-- Fubini form: the `t`-integral over `[a, a + ℓ]` (`a ≥ 3`, `ℓ ≥ 0`) of the circle
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

/-! ### The inner integrals along a vertical segment -/

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

end Integrability


/-! ## From the zero count to the integral of the circle averages -/

section CountToIntegral

/-- The per-disc majorant step: on the discs centred `2 + tI`, `t ≥ 3`, `0 < R < 3`, `circleAverage_log_norm_le_Leps` applies
to `fz X` (analytic on the disc by `analyticOnNhd_fz`, non-zero at the centre by `fz_two_add_ne_zero`).  This is the analogue of
`Zeta23.BL.circleAverage_log_le_Lz` (`BohrLandauPartial.lean:1568`). -/
theorem circleAverage_log_fz_le_Leps {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {t R : ℝ}
    (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3) :
    circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R
      ≤ circleAverage (Leps ε (fz X)) (2 + t * I) R :=
  circleAverage_log_norm_le_Leps hε (2 + t * I) hR (fz X)
    (analyticOnNhd_fz (Zeta23.BL.one_notMem_closedBall_two_add ht hR'))
    (fz_two_add_ne_zero hX t)

/-- Window-abstracted form:
every zero `ρ` with `Re ρ ≥ 1/2 + δ`, `T₁ < Im ρ ≤ T₂` lies in the inner ball
`closedBall (2 + tI) (rin σ₁ δ)` for all `t ∈ [Im ρ − hwin, Im ρ + hwin] ⊆ (a, b]` (as
`hwin ≤ 1`, `a ≤ T₁ − 1`, `T₂ + 1 ≤ b`), so integrating the per-`t` bound `count_window_le_fz` + `circleAverage_log_norm_le_Leps` over
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
  -- pointwise, for `t ∈ [a, b]`: `count_window_le_fz` + `circleAverage_log_norm_le_Leps` applied to the zeros whose window contains `t`
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

/-- The window form used in the assembly: zeros `NSigma (1/2 + δ) T₁ T₂`, window `[T₁ − 1, T₂ + 1]`,
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

/-- `count_le_integral_fz` (`NRight` form): for `T ≥ 4`,
`2 hwin log(Rout/rin) · (NRight δ T − NRight δ 4)
  ≤ ∫_{3}^{T+3} (circleAverage (Leps ε (fz X)) (2 + tI) (Rout σ₁) + π²/(3X)) dt`.
Here `NRight` is `Zeta23.BL.NRight` (the convention of this file), written fully qualified because
`MNF.RH.NRight` is also in scope through `open MNF.RH`. -/
theorem count_le_integral_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
        * ((Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁)
          + Real.pi ^ 2 / (3 * X)) := by
  rw [NRight_sub_eq_NSigma hT]
  exact count_le_integral_fz_window h1 hδσ hδ hX hε le_rfl (by norm_num) hT (by linarith)

end CountToIntegral


/-! ## From the zero count to the window mean squares -/

section CountToMeanSquare

/-- Along a vertical segment `Re s = σ`, the window integral of `Leps ε (fz X)` over
`[a, a + ℓ]` (`a > 0`, `ℓ > 0`) is bounded through the window mean square of `‖fz X‖`:
Jensen (`segment_average_Leps_le`) gives `ℓ · ½ log(ε² + mean square)`, and `log(ε² + 1 + E) ≤ ε² + E` (`half_log_le_half`). -/
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
(`norm_sq_fz_le_of_two_le_re` and `half_log_le_half`). -/
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
`BohrLandauPartial.lean:1692`): along the circle points `circleMap (2 + tI) (Rout σ₁) θ`,
`t ∈ [a, a + ℓ]`, the integral of `Leps ε (fz X)` is an integral along the vertical segment
`Re s = 2 + Rout σ₁ cos θ ∈ [σ₁, 2 + Rout σ₁]` over the shifted window
`[a', a' + ℓ]`, `a' = a + Rout σ₁ sin θ ∈ (a − 3/2, a + 3/2)`.  If `Re ≤ 2` the window mean
square `hMS` applies (`segment_average_Leps_le` + `half_log_le_half`); if `Re > 2` the pointwise centre bound (`norm_sq_fz_le_of_two_le_re` + `half_log_le_half`) applies. -/
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

/-- The circle averages integrated in `t`: the `t`-integral over `[a, a + ℓ]` (`a ≥ 3`, `ℓ > 0`) of the circle
averages of `Leps ε (fz X)` on the discs of radius `Rout σ₁` is at most
`ℓ (½(ε² + E) + π²/(4X))` under the window mean-square hypothesis `hMS` (Fubini swap `integral_circleAverage_Leps_eq_swap`, the per-`θ`
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
  -- the `θ`-marginal is integrable (Fubini on the product integrability `integrable_Leps_circleMap_prod_restrict`)
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

/-- Window-abstracted form: zeros `NSigma (1/2 + δ) T₁ T₂`,
integration window `[a, a + ℓ]` with `3 ≤ a ≤ T₁ − 1`, `T₁ ≤ T₂`, `T₂ + 1 ≤ a + ℓ`, and the
window mean square `hMS` on `[a', a' + ℓ]` for `a' ∈ [a − 3/2, a + 3/2]`, `σ ∈ [σ₁, 2]`:
`2 hwin log(Rout/rin) · NSigma (1/2 + δ) T₁ T₂ ≤ ℓ (½(ε² + E) + π²/X)`.
(`count_le_integral_fz_window`, the split of the constant `π²/(3X)`, `integral_circleAverage_Leps_le`, and
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
  -- the count-to-integral bound, window form
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

/-- `count_le_meanSquare_fz` (`NRight` form): for `T ≥ 4`, `X ≥ 4`, `ε > 0`,
`E ≥ 0`, and the window mean-square hypothesis `hMS` (`σ ∈ [σ₁, 2]`, windows `[a, a + T]` with
`a ∈ [3/2, 9/2]`),
`2 hwin log(Rout/rin) · (NRight δ T − NRight δ 4) ≤ T · (½(ε² + E) + π²/X)`.
Here `NRight` is `Zeta23.BL.NRight` (the convention of this file), written fully qualified because
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

end CountToMeanSquare


/-! ## Exponent arithmetic -/

section ExponentArithmetic

/-! #### Auxiliary constants -/

/-- Auxiliary constant. The window mean-square excess `E₀` at mollifier length `X`, polynomial length `N`, window
length `T` (real parameters; the assembly instantiates `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`, with `N * X` the
cast of the natural product). -/
noncomputable def E0gen (σ₁ X N T : ℝ) : ℝ :=
  (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁)
    + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁) / T

/-- Auxiliary constant. The full error term of the count-to-mean-square bound at `η = E₀`, `ε² = 1/X`, `a ≥ 3/2` already used:
`½ (1/X + E) + π²/X` with `E = E₀(1+E₀) + E₀ + (1+1/E₀)·2M̄²((2/3)N^{2−2σ₁} + C_G²N^{−2σ₁}T)/T`. -/
noncomputable def Egen (σ₁ C_G X N T : ℝ) : ℝ :=
  (1 / 2) * (1 / X + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
    + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T))
  + Real.pi ^ 2 / X

/-- Auxiliary constant. `Egen` at the single-window parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`. -/
noncomputable def Esingle (σ₁ C_G T : ℝ) : ℝ :=
  Egen σ₁ C_G (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ((⌈T⌉₊ + 5 : ℕ) : ℝ) T

/-- Auxiliary constant. The constant in `E₀ ≤ K1c (1+log T)³ T^{−κ}`. -/
noncomputable def K1c (σ₁ : ℝ) : ℝ := 2 * (2 + 1 / (2 * σ₁ - 1)) + 52 * (2 + 2 / (2 - 2 * σ₁))

/-- Auxiliary constant. A uniform bound for `E₀` (logs beaten by `T^κ`). -/
noncomputable def Ebarc (σ₁ : ℝ) : ℝ := K1c σ₁ * (1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3

/-- Auxiliary constant. `M̄² ≤ CMc · X^{2−2σ₁}`. -/
noncomputable def CMc (σ₁ : ℝ) : ℝ := (1 + 1 / (1 - σ₁)) ^ 2

/-- Auxiliary constant. The final constant `K` of `exponent_single`. -/
noncomputable def Ksingle (σ₁ C_G : ℝ) : ℝ :=
  (1 / 2) * (2 + (2 + Ebarc σ₁) * K1c σ₁ + (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2))
    + 2 * Real.pi ^ 2

/-! #### The exponents θ = (2σ₁−1)/(2σ₁), κ = (2σ₁−1)²/(2σ₁) -/

lemma theta_pos {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : 0 < (2 * σ₁ - 1) / (2 * σ₁) :=
  div_pos (by linarith) (by linarith)

lemma theta_le_one {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : (2 * σ₁ - 1) / (2 * σ₁) ≤ 1 :=
  (div_le_one (by linarith)).2 (by linarith)

lemma kappa_pos {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : 0 < (2 * σ₁ - 1) ^ 2 / (2 * σ₁) :=
  div_pos (pow_pos (by linarith) 2) (by linarith)

lemma kappa_le_theta {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) ≤ (2 * σ₁ - 1) / (2 * σ₁) := by
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

/-- `θ (1 − 2σ₁) = −κ`. -/
lemma theta_mul_eq {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) / (2 * σ₁) * (1 - 2 * σ₁) = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `(2 − 2σ₁) + θ (2 − 2σ₁) − 1 = −2κ` (the off-diagonal exponent). -/
lemma offdiag_exponent {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 - 2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) - 1
      = -(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `κ + θ (2 − 2σ₁) + (1 − 2σ₁) = −κ` (the cross-term exponent: the balance). -/
lemma cross_exponent {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) + (1 - 2 * σ₁)
      = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `κ + θ (2 − 2σ₁) + (−2σ₁) = −κ − 1`. -/
lemma cross_exponent' {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) + (-2 * σ₁)
      = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1 := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

-- Sanity: at `σ₁ = 3/4` the exponent `−κ` is `−1/6` (count `T^{5/6}`), and `θ = 1/3`.
example : -((2 * (3 / 4 : ℝ) - 1) ^ 2 / (2 * (3 / 4))) = -(1 / 6) := by norm_num
example : (2 * (3 / 4 : ℝ) - 1) / (2 * (3 / 4)) = 1 / 3 := by norm_num
example : 1 - (2 * (3 / 4 : ℝ) - 1) ^ 2 / (2 * (3 / 4)) = 5 / 6 := by norm_num

/-! #### Generic real helpers -/

/-- `⌊x⌋₊ ≥ x/2` for `x ≥ 2`. -/
lemma half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- `(x^a)^2 = x^(2a)` for `x ≥ 0`. -/
lemma rpow_sq_eq {x a : ℝ} (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- `2^e ≤ 2` for `e ≤ 1`. -/
lemma two_rpow_le_two {e : ℝ} (he : e ≤ 1) : (2 : ℝ) ^ e ≤ 2 := by
  calc (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one 2

/-- `(1 + log T)^3 ≤ (1 + 3/κ)^3 T^κ` for `T ≥ 1`, `κ > 0` (logs are beaten by any power). -/
lemma one_add_log_cube_le_rpow {T κ : ℝ} (hT : 1 ≤ T) (hκ : 0 < κ) :
    (1 + Real.log T) ^ 3 ≤ (1 + 3 / κ) ^ 3 * T ^ κ := by
  have hT0 : 0 < T := by linarith
  have hε : 0 < κ / 3 := by positivity
  have hlog : Real.log T ≤ T ^ (κ / 3) / (κ / 3) := Real.log_le_rpow_div hT0.le hε
  have hdiv : T ^ (κ / 3) / (κ / 3) = (3 / κ) * T ^ (κ / 3) := by
    rw [div_eq_mul_inv, inv_div]
    ring
  rw [hdiv] at hlog
  have h1 : 1 ≤ T ^ (κ / 3) := Real.one_le_rpow hT hε.le
  have hpos : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have h2 : 1 + Real.log T ≤ (1 + 3 / κ) * T ^ (κ / 3) := by linarith
  have h3 : (T ^ (κ / 3)) ^ 3 = T ^ κ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    congr 1
    push_cast
    ring
  calc (1 + Real.log T) ^ 3 ≤ ((1 + 3 / κ) * T ^ (κ / 3)) ^ 3 := pow_le_pow_left₀ hpos h2 3
    _ = (1 + 3 / κ) ^ 3 * (T ^ (κ / 3)) ^ 3 := by ring
    _ = (1 + 3 / κ) ^ 3 * T ^ κ := by rw [h3]

/-! #### The single-window parameters -/

/-- The parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5` for `T ≥ T₀ := max 8 (4^{1/θ})`:
`4 ≤ X ≤ N`, `T^θ/2 ≤ X ≤ T^θ`, `T ≤ N ≤ 2T`. -/
lemma single_params {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      8 ≤ T ∧
      4 ≤ ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ∧
      ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ≤ ⌈T⌉₊ + 5 ∧
      (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ∧
      T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ∧
      T ≤ ((⌈T⌉₊ + 5 : ℕ) : ℝ) ∧ ((⌈T⌉₊ + 5 : ℕ) : ℝ) ≤ 2 * T := by
  have hθ0 := theta_pos hσ
  refine ⟨max 8 ((4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹), le_max_left _ _, fun T hT => ?_⟩
  have hT8 : 8 ≤ T := (le_max_left _ _).trans hT
  have hT4 : (4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹ ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hp4 : (4:ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := by
    calc (4:ℝ) = ((4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹) ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          (Real.rpow_inv_rpow (by norm_num) hθ0.ne').symm
      _ ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hT4 hθ0.le
  have hpT : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T := by
    calc T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (theta_le_one hσ)
      _ = T := Real.rpow_one T
  have hp0 : 0 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_nonneg hT0.le _
  have hfl := Nat.floor_le hp0
  have hfl2 := half_le_nat_floor (by linarith : 2 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
  have hce := Nat.le_ceil T
  have hce2 := Nat.ceil_lt_add_one hT0.le
  refine ⟨hT8, ?_, ?_, hfl, by linarith, ?_, ?_⟩
  · exact Nat.le_floor (by exact_mod_cast hp4)
  · apply Nat.floor_le_of_le
    push_cast
    linarith
  · push_cast
    linarith
  · push_cast
    linarith

/-! #### Term bounds (real parameters `X N T` with the inequalities of `single_params`) -/

/-- `X^{1−2σ₁} ≤ 2 T^{−κ}` when `T^θ ≤ 2X`. -/
lemma X_rpow_le {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T) (_hX0 : 0 < X)
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) :
    X ^ (1 - 2 * σ₁) ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have hpk : (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (1 - 2 * σ₁)
      = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    rw [← Real.rpow_mul hT0.le, theta_mul_eq hσ]
  have h1 : X ^ (1 - 2 * σ₁) ≤ (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁)
      = (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (1 - 2 * σ₁) * (2:ℝ) ^ (2 * σ₁ - 1) := by
    rw [Real.div_rpow hp0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
      show -(1 - 2 * σ₁) = 2 * σ₁ - 1 by ring]
  have h3 : (2:ℝ) ^ (2 * σ₁ - 1) ≤ 2 := two_rpow_le_two (by linarith)
  calc X ^ (1 - 2 * σ₁) ≤ (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁) := h1
    _ = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) * (2:ℝ) ^ (2 * σ₁ - 1) := by rw [h2, hpk]
    _ ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) * 2 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
    _ = 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring

/-- `T^{−κ} ≤ X^{1−2σ₁}` when `X ≤ T^θ`. -/
lemma rpow_le_X_rpow {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hT0 : 0 < T) (hX0 : 0 < X)
    (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) :
    T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ≤ X ^ (1 - 2 * σ₁) := by
  rw [← theta_mul_eq hσ, Real.rpow_mul hT0.le]
  exact Real.rpow_le_rpow_of_nonpos hX0 hXp (by linarith)

/-- `(N X)^{2−2σ₁} / T ≤ 2 T^{−κ}` (in fact `≤ 2 T^{−2κ}`) when `X ≤ T^θ`, `N ≤ 2T`. -/
lemma NX_rpow_div_le {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T)
    (hX0 : 0 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    (N * X) ^ (2 - 2 * σ₁) / T ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_nonneg hT0.le _
  have he : 0 ≤ 2 - 2 * σ₁ := by linarith
  have h1 : (N * X) ^ (2 - 2 * σ₁)
      ≤ (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) := by
    apply Real.rpow_le_rpow (mul_nonneg hN0 hX0) _ he
    calc N * X ≤ (2 * T) * T ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          mul_le_mul hN2 hXp hX0 (by linarith)
      _ = 2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := by ring
  have h2 : (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁)
      = (2:ℝ) ^ (2 - 2 * σ₁) * T ^ (2 - 2 * σ₁)
          * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) := by
    rw [Real.mul_rpow (by linarith) hp0, Real.mul_rpow (by norm_num) hT0.le]
  have h3 : (2:ℝ) ^ (2 - 2 * σ₁) ≤ 2 := two_rpow_le_two (by linarith)
  have h4 : T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T
      = T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0, ← Real.rpow_sub_one hT0.ne',
      offdiag_exponent hσ]
  have h5 : T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
      ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    apply Real.rpow_le_rpow_of_exponent_le hT1
    have := kappa_pos hσ
    linarith
  have h6 : 0 ≤ T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hp0 _)) hT0.le
  calc (N * X) ^ (2 - 2 * σ₁) / T
      ≤ (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T :=
        div_le_div_of_nonneg_right h1 hT0.le
    _ = (2:ℝ) ^ (2 - 2 * σ₁)
        * (T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T) := by
        rw [h2]; ring
    _ ≤ 2 * (T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T) :=
        mul_le_mul_of_nonneg_right h3 h6
    _ = 2 * T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by rw [h4]
    _ ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by linarith

/-- `1/X ≤ 2 T^{−κ}` (in fact `≤ 2 T^{−θ}`) when `T^θ ≤ 2X`. -/
lemma inv_X_le {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T) (_hX0 : 0 < X)
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) :
    1 / X ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have h1 : 1 / X ≤ 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) = 2 * T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) := by
    rw [Real.rpow_neg hT0.le, one_div_div, div_eq_mul_inv]
  have h3 : T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith [kappa_le_theta hσ hσ'])
  calc 1 / X ≤ 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) := h1
    _ = 2 * T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) := h2
    _ ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by linarith

/-- The diagonal/off-diagonal excess: `E₀ ≤ K1c (1 + log T)³ T^{−κ}`. -/
lemma E0gen_le {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    E0gen σ₁ X N T
      ≤ K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hXT : X ≤ T := hXp.trans (by
    calc T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (theta_le_one hσ)
      _ = T := Real.rpow_one T)
  have hL0 : 0 ≤ 1 + Real.log X := by linarith [Real.log_nonneg hX1]
  have hLT0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hLT3 : 0 ≤ (1 + Real.log T) ^ 3 := pow_nonneg hLT0 3
  have hL : (1 + Real.log X) ^ 3 ≤ (1 + Real.log T) ^ 3 :=
    pow_le_pow_left₀ hL0 (by linarith [Real.log_le_log hX0 hXT]) 3
  have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
    have : 0 < 2 * σ₁ - 1 := by linarith
    positivity
  have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
    have : 0 < 2 - 2 * σ₁ := by linarith
    positivity
  have h1 := X_rpow_le hσ hσ' hT1 hX0 hpX
  have h2 := NX_rpow_div_le hσ hσ' hT1 hX0.le hXp hN0 hN2
  calc E0gen σ₁ X N T
      = (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁)
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
          * ((N * X) ^ (2 - 2 * σ₁) / T) := by
        unfold E0gen; ring
    _ ≤ (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log T) ^ 3
          * (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log T) ^ 3
          * (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hL hA) h1 (Real.rpow_nonneg hX0.le _)
            (mul_nonneg hA hLT3)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hB)) h2
            (div_nonneg (Real.rpow_nonneg (mul_nonneg hN0 hX0.le) _) hT0.le)
            (mul_nonneg (mul_nonneg (by norm_num) hB) hLT3)
    _ = K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
        unfold K1c; ring

/-- Lower bound `2 T^{−κ} ≤ E₀` (so `E₀ > 0`, and `1/η = 1/E₀ ≤ T^κ/2`). -/
lemma le_E0gen {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT0 : 0 < T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) :
    2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ≤ E0gen σ₁ X N T := by
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ (1 + Real.log X) ^ 3 := one_le_pow₀ (by linarith [Real.log_nonneg hX1])
  have hA : 2 ≤ 2 + 1 / (2 * σ₁ - 1) := by
    have : 0 < 2 * σ₁ - 1 := by linarith
    have : 0 < 1 / (2 * σ₁ - 1) := by positivity
    linarith
  have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
    have : 0 < 2 - 2 * σ₁ := by linarith
    positivity
  have h1 := rpow_le_X_rpow hσ hT0 hX0 hXp
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hsecond : 0 ≤ 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
      * (N * X) ^ (2 - 2 * σ₁) / T := by
    apply div_nonneg _ hT0.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith))
      (Real.rpow_nonneg (mul_nonneg hN0 hX0.le) _)
  have hfirst : 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
      ≤ (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁) := by
    calc 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
        = (2 * 1) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring
      _ ≤ ((2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3) * X ^ (1 - 2 * σ₁) :=
          mul_le_mul (mul_le_mul hA hL1 (by norm_num) (by linarith)) h1 hk0
            (mul_nonneg (by linarith) (by linarith))
  unfold E0gen
  linarith

/-- A uniform bound: `E₀ ≤ Ebarc` for all `T ≥ 8` (the logs are beaten by `T^κ`). -/
lemma E0gen_le_const {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    E0gen σ₁ X N T ≤ Ebarc σ₁ := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hκ := kappa_pos hσ
  have h := E0gen_le hσ hσ' hT hX1 hXp hpX hN0 hN2
  have hlog := one_add_log_cube_le_rpow hT1 hκ
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hTk : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) = 1 := by
    rw [← Real.rpow_add hT0]
    simp
  calc E0gen σ₁ X N T
      ≤ K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := h
    _ ≤ K1c σ₁ * ((1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3 * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hK1) hk0
    _ = K1c σ₁ * (1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3
          * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        ring
    _ = Ebarc σ₁ := by rw [hTk, mul_one]; rfl

/-- The cross term `(1 + 1/E₀)·2M̄²((2/3)N^{2−2σ₁} + C_G²N^{−2σ₁}T)/T ≤ (4 CMc + 3 CMc C_G²) T^{−κ}`:
this is the term that fixes the balance `X = T^{(2σ₁−1)/(2σ₁)}`. -/
lemma cross_le {σ₁ T X N C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hTN : T ≤ N) (hN2 : N ≤ 2 * T)
    (_hCG : 0 ≤ C_G) :
    (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      ≤ (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have h1σ : 0 < 1 - σ₁ := by linarith
  have hκ0 : 0 < (2 * σ₁ - 1) ^ 2 / (2 * σ₁) := kappa_pos hσ
  have hTκ : 0 < T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have hTκ1 : 1 ≤ T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := Real.one_le_rpow hT1 hκ0.le
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hk0' : 0 < T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_pos_of_pos hT0 _
  -- (a) `1 + 1/E₀ ≤ (3/2) T^κ`
  have hE := le_E0gen hσ hσ' hT0 hX1 hXp hN0.le
  have hE0 : 0 < E0gen σ₁ X N T := lt_of_lt_of_le (by linarith) hE
  have ha : 1 + 1 / E0gen σ₁ X N T ≤ (3 / 2) * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
    have h := one_div_le_one_div_of_le (by linarith : 0 < 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) hE
    have h' : 1 / (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
        = T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) / 2 := by
      rw [Real.rpow_neg hT0.le, one_div, mul_inv, inv_inv]
      ring
    rw [h'] at h
    linarith
  -- (b) `M̄² ≤ CMc · T^{θ(2−2σ₁)}`
  have hXσ : 1 ≤ X ^ (1 - σ₁) := Real.one_le_rpow hX1 h1σ.le
  have hM : 1 + X ^ (1 - σ₁) / (1 - σ₁) ≤ (1 + 1 / (1 - σ₁)) * X ^ (1 - σ₁) := by
    have : X ^ (1 - σ₁) / (1 - σ₁) = (1 / (1 - σ₁)) * X ^ (1 - σ₁) := by ring
    rw [this]
    nlinarith
  have hM0 : 0 ≤ 1 + X ^ (1 - σ₁) / (1 - σ₁) := by
    have := div_nonneg (Real.rpow_nonneg hX0.le (1 - σ₁)) h1σ.le
    linarith
  have hb : (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
      ≤ CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) := by
    calc (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2 ≤ ((1 + 1 / (1 - σ₁)) * X ^ (1 - σ₁)) ^ 2 :=
          pow_le_pow_left₀ hM0 hM 2
      _ = CMc σ₁ * X ^ (2 - 2 * σ₁) := by
          rw [mul_pow, rpow_sq_eq hX0.le, show 2 * (1 - σ₁) = 2 - 2 * σ₁ by ring]
          rfl
      _ ≤ CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [Real.rpow_mul hT0.le]
          exact Real.rpow_le_rpow hX0.le hXp (by linarith)
  -- (c) `((2/3) N^{2−2σ₁} + C_G² N^{−2σ₁} T)/T ≤ (4/3) T^{1−2σ₁} + C_G² T^{−2σ₁}`
  have hN1 : N ^ (2 - 2 * σ₁) ≤ 2 * T ^ (2 - 2 * σ₁) := by
    calc N ^ (2 - 2 * σ₁) ≤ (2 * T) ^ (2 - 2 * σ₁) :=
          Real.rpow_le_rpow hN0.le hN2 (by linarith)
      _ = (2:ℝ) ^ (2 - 2 * σ₁) * T ^ (2 - 2 * σ₁) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 * T ^ (2 - 2 * σ₁) :=
          mul_le_mul_of_nonneg_right (two_rpow_le_two (by linarith)) (Real.rpow_nonneg hT0.le _)
  have hN2' : N ^ (-2 * σ₁) ≤ T ^ (-2 * σ₁) :=
    Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith)
  have hc : ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T) / T
      ≤ (4 / 3) * T ^ (1 - 2 * σ₁) + C_G ^ 2 * T ^ (-2 * σ₁) := by
    rw [add_div]
    have e1 : (2 / 3) * N ^ (2 - 2 * σ₁) / T ≤ (4 / 3) * T ^ (1 - 2 * σ₁) := by
      have : T ^ (1 - 2 * σ₁) = T ^ (2 - 2 * σ₁) / T := by
        rw [← Real.rpow_sub_one hT0.ne']
        congr 1
        ring
      rw [this]
      calc (2 / 3) * N ^ (2 - 2 * σ₁) / T ≤ (2 / 3) * (2 * T ^ (2 - 2 * σ₁)) / T :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN1 (by norm_num)) hT0.le
        _ = (4 / 3) * (T ^ (2 - 2 * σ₁) / T) := by ring
    have e2 : C_G ^ 2 * N ^ (-2 * σ₁) * T / T ≤ C_G ^ 2 * T ^ (-2 * σ₁) := by
      rw [mul_div_assoc, div_self hT0.ne', mul_one]
      exact mul_le_mul_of_nonneg_left hN2' (sq_nonneg _)
    linarith
  -- combine
  have hcross0 : 0 ≤ (2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T :=
    add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0.le _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hN0.le _)) hT0.le)
  have key1 : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))
      * T ^ (1 - 2 * σ₁) = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, cross_exponent hσ]
  have key2 : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))
      * T ^ (-2 * σ₁) = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, cross_exponent' hσ]
  have key3 : T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1) ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hE1 : 0 ≤ 1 + 1 / E0gen σ₁ X N T := by positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  calc (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      = (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2)
        * (((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T) / T) := by ring
    _ ≤ ((3 / 2) * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
        * (2 * (CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))))
        * ((4 / 3) * T ^ (1 - 2 * σ₁) + C_G ^ 2 * T ^ (-2 * σ₁)) := by
        apply mul_le_mul (mul_le_mul ha (by linarith [hb]) (by positivity)
          (mul_nonneg (by norm_num) hTκ.le)) hc (div_nonneg hcross0 hT0.le)
        exact mul_nonneg (mul_nonneg (by norm_num) hTκ.le)
          (mul_nonneg (by norm_num) (mul_nonneg hCM0 (Real.rpow_nonneg hT0.le _)))
    _ = 3 * CMc σ₁ * ((4 / 3) * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))
            * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) * T ^ (1 - 2 * σ₁))
          + C_G ^ 2 * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))
            * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) * T ^ (-2 * σ₁))) := by ring
    _ = 3 * CMc σ₁ * ((4 / 3) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          + C_G ^ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1)) := by rw [key1, key2]
    _ ≤ 3 * CMc σ₁ * ((4 / 3) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          + C_G ^ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCM0)
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left key3 (sq_nonneg _)
    _ = (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring

/-- The assembled bound on `Egen` with real parameters. -/
lemma Egen_le {σ₁ T X N C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX4 : 4 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hTN : T ≤ N) (hN2 : N ≤ 2 * T)
    (hCG : 0 ≤ C_G) :
    Egen σ₁ C_G X N T
      ≤ Ksingle σ₁ C_G * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hLT1 : 1 ≤ (1 + Real.log T) ^ 3 := one_le_pow₀ (by linarith [Real.log_nonneg hT1])
  -- `T^{−κ} ≤ (1 + log T)³ T^{−κ}`
  have hQ : T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
      ≤ (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    le_mul_of_one_le_left hk0 hLT1
  have hQ0 : 0 ≤ (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    mul_nonneg (by linarith) hk0
  have h_inv := inv_X_le hσ hσ' hT1 hX0 hpX
  have h_E0 := E0gen_le hσ hσ' hT hX1 hXp hpX hN0 hN2
  have h_E0c := E0gen_le_const hσ hσ' hT hX1 hXp hpX hN0 hN2
  have h_E0ge := le_E0gen hσ hσ' hT0 hX1 hXp hN0
  have h_E0nn : 0 ≤ E0gen σ₁ X N T := by linarith
  have h_cross := cross_le hσ hσ' hT hX1 hXp hTN hN2 hCG
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hEb : 0 ≤ Ebarc σ₁ := by
    have := kappa_pos hσ
    unfold Ebarc
    positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  -- each term against `Q := (1 + log T)³ T^{−κ}`
  have h_inv' : 1 / X ≤ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) :=
    h_inv.trans (by linarith)
  have h_quad : E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
      ≤ (2 + Ebarc σ₁) * K1c σ₁
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    calc E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
        = E0gen σ₁ X N T * (2 + E0gen σ₁ X N T) := by ring
      _ ≤ E0gen σ₁ X N T * (2 + Ebarc σ₁) := by
          apply mul_le_mul_of_nonneg_left _ h_E0nn
          linarith
      _ ≤ (K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
            * (2 + Ebarc σ₁) :=
          mul_le_mul_of_nonneg_right h_E0 (by linarith)
      _ = (2 + Ebarc σ₁) * K1c σ₁
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by ring
  have h_cross' : (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      ≤ (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2)
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) :=
    h_cross.trans (mul_le_mul_of_nonneg_left hQ
      (add_nonneg (mul_nonneg (by norm_num) hCM0)
        (mul_nonneg (mul_nonneg (by norm_num) hCM0) (sq_nonneg _))))
  have h_pi : Real.pi ^ 2 / X
      ≤ 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    calc Real.pi ^ 2 / X = Real.pi ^ 2 * (1 / X) := by ring
      _ ≤ Real.pi ^ 2 * (2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))) :=
          mul_le_mul_of_nonneg_left h_inv' (sq_nonneg _)
      _ = 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
          ring
  calc Egen σ₁ C_G X N T
      = (1 / 2) * (1 / X + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
          + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T))
        + Real.pi ^ 2 / X := rfl
    _ ≤ (1 / 2) * (2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
          + ((2 + Ebarc σ₁) * K1c σ₁
              * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
            + (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2)
              * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))))
        + 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply add_le_add _ h_pi
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h_inv' (add_le_add h_quad h_cross')
    _ = Ksingle σ₁ C_G * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
        unfold Ksingle
        ring

/-- `Ksingle > 0`. -/
lemma Ksingle_pos {σ₁ C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) : 0 < Ksingle σ₁ C_G := by
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hEb : 0 ≤ Ebarc σ₁ := by
    have := kappa_pos hσ
    unfold Ebarc
    positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  have h1 : 0 ≤ (2 + Ebarc σ₁) * K1c σ₁ := mul_nonneg (by linarith) hK1
  have h2 : 0 ≤ CMc σ₁ * C_G ^ 2 := mul_nonneg hCM0 (sq_nonneg _)
  have h3 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  unfold Ksingle
  nlinarith

/-! #### The main statement -/

/-- The exponent arithmetic for the single-window estimate: with
`X = ⌊T^{(2σ₁−1)/(2σ₁)}⌋₊`, `N = ⌈T⌉₊ + 5`, for `T ≥ T₀` one has `4 ≤ X ≤ N` and the error term
`Esingle σ₁ C_G T` (the single-window error term) is `≤ K (1 + log T)³ T^{−(2σ₁−1)²/(2σ₁)}`.
`C_G ≥ 0` is the free constant of the approximate formula; `K` depends on `σ₁, C_G`, `T₀` only
on `σ₁`. -/
theorem exponent_single {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) {C_G : ℝ} (hCG : 0 ≤ C_G) :
    ∃ K T₀ : ℝ, 0 < K ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (4 ≤ ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊) ∧
      (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ≤ ⌈T⌉₊ + 5) ∧
      Esingle σ₁ C_G T ≤ K * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  obtain ⟨T₀, hT₀, hall⟩ := single_params h1 h1'
  refine ⟨Ksingle σ₁ C_G, T₀, Ksingle_pos h1 h1', hT₀, fun T hT => ?_⟩
  obtain ⟨hT8, hX4, hXN, hXp, hpX, hTN, hN2⟩ := hall T hT
  refine ⟨hX4, hXN, ?_⟩
  have hX4' : (4:ℝ) ≤ (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) := by exact_mod_cast hX4
  exact Egen_le h1 h1' hT8 hX4' hXp hpX hTN hN2 hCG

/-! #### Glue for the assembly: the right-hand side of `meanSquare_fz_window` is `T * (1 + E)` -/

/-- The right-hand side of `meanSquare_fz_window` at `ℓ = T`, `η = E₀ = E0gen σ₁ X N T`, any `a ≥ 3/2`, is at most
`T * (1 + E)` with `E` the `a`-free excess inside `Egen` (so `hMS` of `count_le_meanSquare_fz` holds with this `E`,
uniformly in `a ∈ [3/2, 9/2]` and in `σ`). -/
lemma w4_rhs_le {σ₁ T X N a C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT0 : 0 < T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) (ha : 3 / 2 ≤ a) :
    (1 + E0gen σ₁ X N T)
        * (T * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁))
      + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T))
    ≤ T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
        + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T)) := by
  have hX0 : 0 < X := by linarith
  have hE := le_E0gen hσ hσ' hT0 hX1 hXp hN0
  have hE0 : 0 < E0gen σ₁ X N T :=
    lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hT0 (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))); linarith) hE
  have hE1 : 0 ≤ 1 + 1 / E0gen σ₁ X N T := by positivity
  have hfirst : (1 + E0gen σ₁ X N T)
        * (T * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁))
      = T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T)) := by
    have hT' : T ≠ 0 := hT0.ne'
    unfold E0gen
    field_simp
    ring
  have hNpow : 0 ≤ N ^ (2 - 2 * σ₁) := Real.rpow_nonneg hN0 _
  have hdiv : N ^ (2 - 2 * σ₁) / a ≤ (2 / 3) * N ^ (2 - 2 * σ₁) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hNpow (sub_nonneg.2 ha)]
  have hsecond : (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T))
      ≤ (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by
    apply mul_le_mul_of_nonneg_left _ hE1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add_left hdiv _
  have hT' : T * ((1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T)
      = (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by
    rw [mul_div_assoc', mul_comm T, mul_div_assoc, div_self hT0.ne', mul_one]
  calc _ = T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T))
        + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by rw [hfirst]
    _ ≤ T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T))
        + T * ((1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T) := by
        rw [hT']
        exact add_le_add_right hsecond _
    _ = _ := by ring

end ExponentArithmetic


/-! ## The geometric factor `2 hwin log(Rout/rin)` -/

section GeometricFactor

open Zeta23.BL

/-- With `Δ := δ − (σ₁ − 1/2)`: `2·hwin·log(Rout/rin) ≥ Δ^{3/2}/3`.
Proof: `rin = A + Δ/2`, `Rout = A + Δ` with `A = 3/2 − δ ≥ 1`, so `rin² − A² ≥ Δ`, hence
`2·hwin ≥ √Δ`; and `log(Rout/rin) ≥ 1 − rin/Rout = (Δ/2)/Rout ≥ Δ/3` since `Rout < 3/2`. -/
theorem geom_lower {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    (δ - (σ₁ - 1 / 2)) ^ (3/2 : ℝ) / 3 ≤ 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) := by
  obtain ⟨hrin_pos, hrin_lt, hRout, hwin_pos, _, -⟩ := geom_facts h1 hδσ hδ
  have hΔpos : 0 < δ - (σ₁ - 1 / 2) := by linarith
  have hA1 : (1 : ℝ) ≤ 3 / 2 - δ := by linarith
  have hrin : rin σ₁ δ = (3 / 2 - δ) + (δ - (σ₁ - 1 / 2)) / 2 := by unfold rin Rout; ring
  have hRo : Rout σ₁ = (3 / 2 - δ) + (δ - (σ₁ - 1 / 2)) := by unfold Rout; ring
  have hRout_pos : 0 < Rout σ₁ := by linarith
  -- (i) `√Δ ≤ 2 hwin`
  have hsq : δ - (σ₁ - 1 / 2) ≤ rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2 := by
    rw [hrin]; nlinarith
  have h2h : Real.sqrt (δ - (σ₁ - 1 / 2)) ≤ 2 * hwin σ₁ δ := by
    unfold hwin
    rw [show 2 * (Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2)
        = Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) by ring]
    exact Real.sqrt_le_sqrt hsq
  -- (ii) `Δ/3 ≤ log (Rout / rin)`
  have hlog : (δ - (σ₁ - 1 / 2)) / 3 ≤ Real.log (Rout σ₁ / rin σ₁ δ) := by
    have hq : 0 < rin σ₁ δ / Rout σ₁ := div_pos hrin_pos hRout_pos
    have hl := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div hrin_pos.ne' hRout_pos.ne'] at hl
    rw [Real.log_div hRout_pos.ne' hrin_pos.ne']
    have h3 : rin σ₁ δ / Rout σ₁ ≤ 1 - (δ - (σ₁ - 1 / 2)) / 3 := by
      rw [div_le_iff₀ hRout_pos]
      have hR32 : Rout σ₁ < 3 / 2 := hRout
      rw [hrin, hRo]
      rw [hRo] at hR32
      nlinarith [mul_pos hΔpos (sub_pos.2 hR32)]
    linarith
  -- (iii) assemble: `Δ^{3/2} = √Δ · Δ`
  have hpow : (δ - (σ₁ - 1 / 2)) ^ (3/2 : ℝ)
      = Real.sqrt (δ - (σ₁ - 1 / 2)) * (δ - (σ₁ - 1 / 2)) := by
    rw [show (3/2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hΔpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hpow, mul_div_assoc]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (δ - (σ₁ - 1 / 2)) := Real.sqrt_nonneg _
  have hΔ3 : 0 ≤ (δ - (σ₁ - 1 / 2)) / 3 := by linarith
  exact mul_le_mul h2h hlog hΔ3 (by linarith)

end GeometricFactor


/-! ## Assembly: the single-window zero-density estimate -/

section Assembly

/-- The assembly core at explicit parameters: for `T ≥ 8`, naturals `4 ≤ X ≤ N` with
`X ≤ T^{(2σ₁−1)/(2σ₁)}` and `T + 9/2 ≤ N`, and the sharp approximate formula `hG` with constant
`C_G ≥ 0` (the shape of `BLClosure.zeta_approx_sharp`), the window mean-square hypothesis `hMS` of `count_le_meanSquare_fz` is
discharged by `meanSquare_fz_window` (`η := E₀ = E0gen σ₁ X N T`, windows `[a, a + T]` with `a ∈ [3/2, 9/2]`, so
`1 ≤ a` and `a + T ≤ N`) and `w4_rhs_le`; with `ε := √(1/X)` the right-hand side of `count_le_meanSquare_fz` is
literally `T · Egen σ₁ C_G X N T`. -/
theorem count_le_Egen {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {C_G : ℝ} (hCG : 0 ≤ C_G)
    (hG : ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C_G * (N : ℝ) ^ (-σ))
    {T : ℝ} (hT : 8 ≤ T) {X N : ℕ} (hX4 : 4 ≤ X) (hXN : X ≤ N)
    (hXp : (X : ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hTN : T + 9 / 2 ≤ (N : ℝ)) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
        * ((Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4)
      ≤ T * Egen σ₁ C_G X N T := by
  have h2 : σ₁ < 1 := by linarith
  have hT0 : 0 < T := by linarith
  have hT4 : 4 ≤ T := by linarith
  have hX1 : 1 ≤ X := by omega
  have hX1' : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hX0' : (0:ℝ) < X := by linarith
  have hN1 : 1 ≤ N := le_trans hX1 hXN
  have hN0' : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have h1σ : 0 < 1 - σ₁ := by linarith
  -- `η := E₀ > 0`
  have hE0le := le_E0gen h1 h2 hT0 hX1' hXp hN0'
  have hη : 0 < E0gen σ₁ X N T :=
    lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hT0 (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))); linarith)
      hE0le
  -- `ε := √(1/X)`, so `ε² = 1/X`
  have hε : 0 < Real.sqrt (1 / (X:ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hε2 : Real.sqrt (1 / (X:ℝ)) ^ 2 = 1 / (X:ℝ) := Real.sq_sqrt (by positivity)
  -- the `a`-free excess `E`
  have hE0' : 0 ≤ E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
      + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + (X:ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * (N:ℝ) ^ (2 - 2 * σ₁) + C_G ^ 2 * (N:ℝ) ^ (-2 * σ₁) * T)) / T := by
    positivity
  -- the window mean-square hypothesis `hMS` of `count_le_meanSquare_fz`, from `meanSquare_fz_window`
  have hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a : ℝ, 3 / 2 ≤ a → a ≤ 9 / 2 →
      ∫ t in a..(a + T), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2
        ≤ T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
          + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + (X:ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((2 / 3) * (N:ℝ) ^ (2 - 2 * σ₁) + C_G ^ 2 * (N:ℝ) ^ (-2 * σ₁) * T)) / T)) := by
    intro σ hσ1 hσ2 a ha1 ha2
    have hEt : ∀ t ∈ Set.Icc a (a + T),
        ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)
          - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ) := by
      intro t ht
      have hs1 : (σ : ℂ) + t * I ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith [ht.1]
      exact hG σ t hσ1 hσ2 (by linarith [ht.1]) N hN1 (by linarith [ht.2]) hs1
    have hW4 := meanSquare_fz_window h1 h2 hσ1 hX1 hXN (by linarith : 1 ≤ a) hT0.le hCG hEt hη
    rw [Nat.cast_mul] at hW4
    exact hW4.trans (w4_rhs_le (C_G := C_G) h1 h2 hT0 hX1' hXp hN0' ha1)
  -- `count_le_meanSquare_fz`
  have hA0 := count_le_meanSquare_fz h1 hδσ hδ hX4 hε hT4 hE0' hMS
  rw [hε2] at hA0
  exact hA0

/-- Zero-density with a power saving, single-window form
(Carlson's method, weaker exponent): for `1/2 < σ₁`, `σ₁ − 1/2 < δ ≤ 1/2` there is `C` with
`NRight δ T ≤ C · T^{1 − (2σ₁−1)²/(2σ₁)} · (1 + log T)³` for all `T ≥ 2`.  Here `NRight` is
`Zeta23.BL.NRight` (the convention of this file; it has the same body as `MNF.RH.NRight`).
Taking `σ₁` just below `1/2 + δ`, the saving `(2σ₁−1)²/(2σ₁)` approaches `4δ²/(1+2δ)`, which
agrees with Carlson's `4δ²` to leading order as `δ → 0`; Carlson's exponent `4σ₁(1−σ₁)` itself
is not proved here.
Proof: `C_G := max C₀ 0` with `C₀` from `BLClosure.zeta_approx_sharp (σ₀ := σ₁)`; `K, T₀` from
`exponent_single`; for `T ≥ T₀` the core `count_le_Egen` at `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`
(`count_le_meanSquare_fz` + `meanSquare_fz_window`), the bound `Egen ≤ K (1 + log T)³ T^{−κ}`, and the geometric factor
`2 hwin log(Rout/rin) > 0` (`geom_lower`); for `2 ≤ T < T₀` monotonicity (`NRight_mono`).
Constant: `C = NRight δ T₀ + K / (2 hwin σ₁ δ · log (Rout σ₁ / rin σ₁ δ))`. -/
theorem density_single_window {σ₁ δ : ℝ}
    (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      (Zeta23.BL.NRight δ T : ℝ)
        ≤ C * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3 := by
  have h2 : σ₁ < 1 := by linarith
  -- the sharp approximate formula, with a nonnegative constant
  obtain ⟨C₀, hC₀⟩ := BLClosure.zeta_approx_sharp (σ₀ := σ₁) (by linarith)
  have hCG : 0 ≤ max C₀ 0 := le_max_right _ _
  have hG : ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ max C₀ 0 * (N : ℝ) ^ (-σ) := fun σ t hσ1 hσ2 ht N hN htN hs1 =>
    (hC₀ σ t hσ1 hσ2 ht N hN htN hs1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  -- the exponent arithmetic (`exponent_single`)
  obtain ⟨K, T₀, hK, hT₀, hall⟩ := exponent_single h1 h2 hCG
  -- the geometric factor (`geom_lower`)
  have hKg : 0 < 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) := by
    have hΔ : 0 < δ - (σ₁ - 1 / 2) := by linarith
    have hG8 := geom_lower h1 hδσ hδ
    have hpos : 0 < (δ - (σ₁ - 1 / 2)) ^ (3/2 : ℝ) / 3 := by
      have := Real.rpow_pos_of_pos hΔ (3/2 : ℝ)
      positivity
    linarith
  -- the exponent `1 − κ ≥ 0`
  have hκ : 0 ≤ 1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁) := by
    have := kappa_le_theta h1 h2
    have := theta_le_one h1
    linarith
  have hN0 : (0:ℝ) ≤ Zeta23.BL.NRight δ T₀ := Nat.cast_nonneg _
  have hKKg : 0 ≤ K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)) :=
    div_nonneg hK.le hKg.le
  refine ⟨(Zeta23.BL.NRight δ T₀ : ℝ) + K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)),
    fun T hT => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  -- `Q := T^{1−κ} (1 + log T)³ ≥ 1`
  have hQ1 : 1 ≤ T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3 := by
    have ha := Real.one_le_rpow hT1 hκ
    have hb : 1 ≤ (1 + Real.log T) ^ 3 := one_le_pow₀ (by linarith [Real.log_nonneg hT1])
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3 :=
          mul_le_mul ha hb zero_le_one (by linarith)
  rcases le_or_gt T₀ T with hTT₀ | hTT₀
  · -- `T ≥ T₀`: the core at `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`
    obtain ⟨hX4, hXN, hEs⟩ := hall T hTT₀
    have hT8 : 8 ≤ T := hT₀.trans hTT₀
    have hXp : (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
      Nat.floor_le (Real.rpow_nonneg hT0.le _)
    have hTN : T + 9 / 2 ≤ ((⌈T⌉₊ + 5 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil T]
    have hA0 := count_le_Egen h1 hδσ hδ hCG hG hT8 hX4 hXN hXp hTN
    have hEs' : Egen σ₁ (max C₀ 0) (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ)
        ((⌈T⌉₊ + 5 : ℕ) : ℝ) T
        ≤ K * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := hEs
    have hpow : T * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
        = T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
      rw [show 1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁) = 1 + -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) by ring,
        Real.rpow_add hT0, Real.rpow_one]
    have hR : T * Egen σ₁ (max C₀ 0) (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ)
          ((⌈T⌉₊ + 5 : ℕ) : ℝ) T
        ≤ K * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by
      calc T * Egen σ₁ (max C₀ 0) (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ)
            ((⌈T⌉₊ + 5 : ℕ) : ℝ) T
          ≤ T * (K * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) :=
            mul_le_mul_of_nonneg_left hEs' hT0.le
        _ = K * (1 + Real.log T) ^ 3 * (T * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by ring
        _ = K * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by
            rw [hpow]; ring
    -- divide by the geometric factor
    have hKgK : 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
          * (K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ))
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3))
        = K * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by
      have hc : K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ))
          * (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)) = K := div_mul_cancel₀ K hKg.ne'
      calc 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)
            * (K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ))
              * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3))
          = (K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ))
              * (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)))
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by ring
        _ = K * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by rw [hc]
    have hD : (Zeta23.BL.NRight δ T : ℝ) - Zeta23.BL.NRight δ 4
        ≤ K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ))
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) :=
      le_of_mul_le_mul_left (hA0.trans (hR.trans_eq hKgK.symm)) hKg
    -- `NRight δ 4 ≤ NRight δ T₀ ≤ NRight δ T₀ · Q`
    have h4 : (Zeta23.BL.NRight δ 4 : ℝ) ≤ Zeta23.BL.NRight δ T₀ := by
      exact_mod_cast Zeta23.BL.NRight_mono (by linarith : (4:ℝ) ≤ T₀)
    have hT₀Q : (Zeta23.BL.NRight δ T₀ : ℝ)
        ≤ Zeta23.BL.NRight δ T₀ * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) :=
      le_mul_of_one_le_right hN0 hQ1
    calc (Zeta23.BL.NRight δ T : ℝ)
        ≤ (Zeta23.BL.NRight δ T₀ + K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)))
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) := by
          linarith
      _ = (Zeta23.BL.NRight δ T₀ + K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)))
            * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3 := by ring
  · -- `2 ≤ T < T₀`: monotonicity
    have hmono : (Zeta23.BL.NRight δ T : ℝ) ≤ Zeta23.BL.NRight δ T₀ := by
      exact_mod_cast Zeta23.BL.NRight_mono hTT₀.le
    calc (Zeta23.BL.NRight δ T : ℝ)
        ≤ Zeta23.BL.NRight δ T₀ := hmono
      _ ≤ Zeta23.BL.NRight δ T₀
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) :=
          le_mul_of_one_le_right hN0 hQ1
      _ ≤ (Zeta23.BL.NRight δ T₀ + K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)))
            * (T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = (Zeta23.BL.NRight δ T₀ + K / (2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)))
            * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3 := by ring

end Assembly


end Zeta23.Density
