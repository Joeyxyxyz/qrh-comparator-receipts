/-
G4.lean — `Density/Divisor.lean` (node G4 of STRIP_PLAN, 2026-11-03):
ζ-multiplicities are counted by the divisor of the mollified function `fz X = ζ · M_X`
on a closed ball avoiding the pole `1`.

Items (STRIP_PLAN §(C), block **G4**):
  * G4a  `Mx_ne_zero_of_le_re`                     : `M_X(s) ≠ 0` for `Re s ≥ 3`, `X ≥ 1`
  * G4b  `analyticOrderAt_Mx_ne_top`               : the analytic order of `M_X` is finite everywhere
  * G4   `zeta_order_le_divisor_fz`                : `zeta_order ρ ≤ divisor (fz X) (closedBall c r) ρ`
  * G4'  `finset_sum_zeta_order_le_finsum_divisor_fz`
Helpers (local copies of plan items C1 / C1', which live in the sibling node C; scratch files
cannot be imported, so they are re-proved here with the plan's exact statements so that the
merger can drop either copy):
  * C1   `analyticOnNhd_Mx`
  * C1'  `analyticOnNhd_fz`
Pattern: `Zeta23.BL.divisor_riemannZeta_eq_int` and `Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor`
(`Zeta23/BL/BohrLandauPartial.lean`).  No `sorry`.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

/- `zeta_order`, `is_nontrivial_zero` are `MNF.RH.*` (plan "Conventions"); the frozen DEFINITIONS
block below uses `zeta_order` unqualified, so this `open` precedes it (it does not alter any
definition body). -/
open MNF.RH

/-! ## DEFINITIONS block — FROZEN, copied verbatim from STRIP_PLAN.md §(C) Stage 0 -/

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

/-! ## C1 (local copy): `M_X` is entire -/

/-- `M_X` is entire: a finite sum of `s ↦ μ(n) n^{-s}` with `n ≥ 1`. -/
theorem analyticOnNhd_Mx (X : ℕ) : AnalyticOnNhd ℂ (Mx X) Set.univ := by
  have hd : Differentiable ℂ (Mx X) := by
    have hfun : Mx X = ∑ n ∈ Icc 1 X, fun s : ℂ => ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s) := by
      ext s; simp only [Mx, Finset.sum_apply]
    rw [hfun]
    apply Differentiable.sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    exact (differentiable_neg.const_cpow (Or.inl hn0)).const_mul _
  exact fun z _ => hd.analyticAt z

/-- C1' (local copy): `fz X = ζ · M_X` is analytic on every set avoiding `1`. -/
theorem analyticOnNhd_fz {X : ℕ} {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ (fz X) S :=
  (Zeta23.RvM.analyticOnNhd_riemannZeta hS).mul ((analyticOnNhd_Mx X).mono (Set.subset_univ S))

/-! ## G4a: `M_X` does not vanish on `Re s ≥ 3` -/

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

/-! ## G4b: the analytic order of `M_X` is finite everywhere (identity theorem on `ℂ`) -/

/-- G4b. `M_X` is not locally identically zero anywhere: it is entire, `ℂ` is connected, and
`M_X(3) ≠ 0` (G4a). -/
theorem analyticOrderAt_Mx_ne_top {X : ℕ} (hX : 1 ≤ X) (z : ℂ) :
    analyticOrderAt (Mx X) z ≠ ⊤ := by
  refine (analyticOnNhd_Mx X).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (3 : ℂ)) (Set.mem_univ z) ?_
  rw [((analyticOnNhd_Mx X) 3 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
    (Mx_ne_zero_of_le_re hX (by simp))]
  exact ENat.zero_ne_top

/-! ## G4: `zeta_order ρ ≤ divisor (fz X) ρ` on a closed ball avoiding `1` -/

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

/-! ## G4': Finset form -/

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

end Zeta23.Density

#print axioms Zeta23.Density.analyticOnNhd_Mx
#print axioms Zeta23.Density.analyticOnNhd_fz
#print axioms Zeta23.Density.Mx_ne_zero_of_le_re
#print axioms Zeta23.Density.analyticOrderAt_Mx_ne_top
#print axioms Zeta23.Density.zeta_order_le_divisor_fz
#print axioms Zeta23.Density.finset_sum_zeta_order_le_finsum_divisor_fz
