/-
W2.lean — STRIP_PLAN node W2 (Density/Window.lean): plan item W2 `meanSquare_prodPoly`,
the mean square of the product polynomial `S_N · M_X` over a window `[a, a+ℓ]`:

  ∫_a^{a+ℓ} ‖S_N(σ+it) M_X(σ+it)‖² dt
    ≤ ℓ · (1 + (2 + 1/(2σ₁−1)) (1+log X)³ X^{1−2σ₁}) + 26 (2 + 2/(2−2σ₁)) (1+log X)³ (NX)^{2−2σ₁}

for `1/2 < σ₁ < 1`, `σ₁ ≤ σ`, `1 ≤ X ≤ N`, `0 ≤ ℓ`.  The `1 +` is isolated: it is the single
coefficient `cm N X 1 = 1` (P2), all other coefficients below `X` vanish by Möbius inversion.

Route (plan §(C), W2): P1 rewrites the integrand as `Σ_{m ≤ NX} cm·m^{-s}`; W1 translates the
window to `[0, ℓ]`; the tree's `M1.dirichlet_meanSquare_le` (Montgomery–Vaughan form) gives
`ℓ Σ‖a_m‖² + 26 Σ (m+1)‖a_m‖²` with `a_m = cm·m^{-σ}·m^{-ia}`, `‖a_m‖² = |cm|² m^{-2σ}`;
the diagonal is split at `X` (P2 gives exactly `1` below `X`), and both the tail and the
off-diagonal sum are bounded through `|cm|² ≤ dX²` (P3), `m^{-2σ} ≤ m^{-2σ₁}`, the divisor-sum
bound E1 (`w m = dX X m ^ 2`, `L = (1 + log X)³`) and the partial-summation lemmas D1, D2.

Upstream nodes P, E, D and W1 (node G8W) are copied verbatim below (scratch files cannot be
imported).  The DEFINITIONS block is the frozen block of STRIP_PLAN (C), copied verbatim; the
single addition is `open MNF.RH` before the namespace, so that the unqualified `zeta_order` in
`NSigma` resolves (it is `MNF.RH.zeta_order`, as the plan's conventions say).
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

/-! ### End of the frozen DEFINITIONS block. -/

/-! ## Upstream node P (Density/Product.lean) — copied verbatim -/

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

/-! ## Upstream node E (Density/DivisorSum.lean) — copied verbatim -/

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

/-! ## Upstream node D (Density/Abel.lean) — copied verbatim -/

/-! ### D0: Abel summation with generic weights -/

set_option linter.unusedVariables false in
/-- D0. Partial summation: if `0 ≤ w`, `∑_{m ≤ Y} w m ≤ Y L` for every `Y`, and `g ≥ 0` is
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

/-- D0'. Tail version of D0 (start at `X`): the price of starting late is the single term
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

/-! ### D1: the tail `∑_{m > X} w m m^{-2σ}` -/

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

/-- D1. Tail of the weighted sum against `m^{-2σ}`:
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

/-! ### D2: the off-diagonal weight `(m+1) m^{-2σ}` -/

/-- D2. Weighted off-diagonal sum:
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

/-! ## Upstream node G8W, item W1 (Density/Window.lean) — copied verbatim -/

/-! ## W1 — the window translation `t ↦ u = t − a` (`Density/Window.lean`) -/

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


/-! ## W2 — the mean square of the product polynomial `S_N · M_X` over a window -/

/-- Squared norm of the translated coefficient `cm · m^{-σ} · m^{-ia}`: `|cm|² m^{-2σ}`. -/
theorem norm_coeff_sq (N X : ℕ) (σ a : ℝ) {m : ℕ} (hm : 0 < m) :
    ‖((cm N X m : ℤ) : ℂ) * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)‖ ^ 2
      = |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ) := by
  rw [norm_mul, norm_mul, M1.norm_cpow_neg_mul_I m hm a, mul_one, mul_pow, M1.norm_sq_rpow,
    Complex.norm_intCast]

/-- `|cm|² ≤ dX²` (P3 squared). -/
theorem abs_cm_sq_le (N X m : ℕ) : |((cm N X m : ℤ) : ℝ)| ^ 2 ≤ (dX X m : ℝ) ^ 2 :=
  pow_le_pow_left₀ (abs_nonneg _) (abs_cm_le N X m) 2

/-- **W2.** Mean square of the product polynomial `S_N · M_X` on the window `[a, a+ℓ]`,
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
  -- the weight `w m = dX X m ^ 2` and its partial-sum bound E1
  have hw : ∀ m : ℕ, 0 ≤ (dX X m : ℝ) ^ 2 := fun m => sq_nonneg _
  have hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, (dX X m : ℝ) ^ 2 ≤ Y * (1 + Real.log X) ^ 3 :=
    fun Y => sum_dX_sq_le X Y
  -- pointwise: `|cm|² m^{-2σ} ≤ dX² m^{-2σ₁}` for `m ≥ 1` (P3 and `σ₁ ≤ σ`)
  have hpt : ∀ m ∈ Icc 1 (N * X),
      |((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ)
        ≤ (dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    exact mul_le_mul (abs_cm_sq_le N X m)
      (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
      (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
  -- the diagonal: exactly `1` below `X` (P2), the tail by D1
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
  -- the off-diagonal: D2
  have hoff : ∑ m ∈ Icc 1 (N * X),
      ((m : ℝ) + 1) * (|((cm N X m : ℤ) : ℝ)| ^ 2 * (m : ℝ) ^ (-2 * σ))
        ≤ (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) := by
    have hD2 : ∑ m ∈ Icc 1 (N * X), ((m : ℝ) + 1) * ((dX X m : ℝ) ^ 2 * (m : ℝ) ^ (-2 * σ₁))
        ≤ (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁) :=
      weight_sum_le (w := fun m => (dX X m : ℝ) ^ 2) hw hL hW h1 h1' hM
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) hD2
    exact mul_le_mul_of_nonneg_left (hpt m hm) (by positivity)
  -- assemble: P1, W1, Montgomery–Vaughan, then the two sums
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

end Zeta23.Density
