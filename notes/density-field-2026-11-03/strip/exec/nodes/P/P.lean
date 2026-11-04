/-
Density/Product.lean (node P of STRIP_PLAN) — the product polynomial S_N · M_X.

P1  `S_mul_Mx_eq`  : S_N(s) · M_X(s) = Σ_{m ≤ NX} cm(N,X,m) m^{−s}
P2  `cm_eq_of_le`  : for X ≤ N and m ≤ X, cm(N,X,m) = [m = 1]   (Möbius inversion μ * ζ = 1)
P3  `abs_cm_le`    : |cm(N,X,m)| ≤ dX(X,m)

The DEFINITIONS block below is the frozen block of STRIP_PLAN (C), copied verbatim; the single
addition is `open MNF.RH` before the namespace, so that the unqualified `zeta_order` in `NSigma`
resolves (it is `MNF.RH.zeta_order`, as the plan's conventions say).
-/
import Zeta23.BL.BohrLandauClosure

open MNF.RH

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

/-! ## P3. `|cm N X m| ≤ dX X m` -/

/-- P3: the coefficient is bounded by the number of divisors `≤ X`
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

/-! ## P2. `cm N X m = [m = 1]` for `m ≤ X ≤ N` -/

/-- P2: for `m ≤ X ≤ N` every divisor `d` of `m` has `d ≤ X` and `m / d ≤ N`, so
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

/-! ## P1. `S N s * Mx X s = Σ_{m ≤ NX} cm N X m · m^{-s}` -/

/-- P1: the product of the two Dirichlet polynomials, reindexed by `m = n * d`. -/
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

end Zeta23.Density
