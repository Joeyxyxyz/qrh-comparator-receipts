/-
E.lean — STRIP_PLAN node E (Density/DivisorSum.lean): plan items E1a, E1b, E1c, E1d, E1.

The divisor-sum bound  ∑_{m ≤ Y} dX(X,m)^2 ≤ Y (1 + log X)^3  (log in X, not Y).

Header per plan: `import Zeta23.BL.BohrLandauClosure`.  `open MNF.RH` is added (outside the
frozen DEFINITIONS block) so that the frozen body `zeta_order ρ` of `NSigma` resolves, exactly as
in `Zeta23/BohrLandau.lean:10`.  The DEFINITIONS block below is copied verbatim from the plan.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

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

/-! ## E1a — common multiples in `[1, Y]` -/

/-- E1a: the number of `m ∈ [1, Y]` divisible by both `d₁` and `d₂` is at most
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

/-! ## E1b — `gcd` is one of the common divisors -/

/-- E1b: `gcd d₁ d₂` is one term of the sum of the common divisors of `d₁` and `d₂`. -/
theorem gcd_le_sum_dvd (d₁ d₂ : ℕ) (h₁ : 0 < d₁) :
    (Nat.gcd d₁ d₂ : ℝ) ≤ ∑ g ∈ d₁.divisors.filter (· ∣ d₂), (g : ℝ) := by
  have hmem : Nat.gcd d₁ d₂ ∈ d₁.divisors.filter (· ∣ d₂) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_left d₁ d₂, h₁.ne'⟩, Nat.gcd_dvd_right d₁ d₂⟩
  exact Finset.single_le_sum (fun g _ => Nat.cast_nonneg g) hmem

/-- E1b, indexed over `Icc 1 X` (the form used in E1d): for `1 ≤ d₁ ≤ X`,
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

/-! ## E1c — harmonic sum over the multiples of `g` -/

/-- E1c: `∑_{d ≤ X, g ∣ d} 1/d ≤ (1/g)(1 + log X)`. -/
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

/-! ## E1d — the gcd double sum -/

/-- Pointwise identity used in E1d. -/
theorem ite_and_div_eq (g d₁ d₂ : ℕ) :
    (if g ∣ d₁ ∧ g ∣ d₂ then (g : ℝ) else 0) / (d₁ * d₂)
      = (g : ℝ) * ((if g ∣ d₁ then 1 / (d₁ : ℝ) else 0) * (if g ∣ d₂ then 1 / (d₂ : ℝ) else 0)) := by
  by_cases h1 : g ∣ d₁
  · by_cases h2 : g ∣ d₂
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]; ring
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring

/-- E1d: `∑_{d₁,d₂ ≤ X} gcd(d₁,d₂)/(d₁ d₂) ≤ (1 + log X)³`. -/
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

/-! ## E1 — the divisor-sum bound -/

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

/-- E1: `∑_{m ≤ Y} dX(X,m)² ≤ Y (1 + log X)³`.  The logarithm is in `X`, not `Y`. -/
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

end Zeta23.Density

#print axioms Zeta23.Density.card_filter_dvd_dvd_le
#print axioms Zeta23.Density.gcd_le_sum_dvd
#print axioms Zeta23.Density.sum_div_of_dvd_le
#print axioms Zeta23.Density.sum_gcd_div_le
#print axioms Zeta23.Density.sum_dX_sq_le
