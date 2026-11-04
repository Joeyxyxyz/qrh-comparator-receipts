/-
B2.lean — node B2 of the Bohr–Landau closure (2026-11-03).

Target B of BohrLandauClosure.lean: the Fourier series of the periodic second Bernoulli
function B₂per(u) = {u}² − {u} + 1/6, plus the properties of P(u) = (B₂per u − 1/6)/2 needed by
nodes E and F (Fourier series of P, |P| ≤ 1/8, P(n) = 0, continuity, P' = ψ off the integers).
Everything here is Mathlib-only; no ζ.
-/
import Mathlib

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace BLClosure

/-- the sawtooth ψ(u) = {u} − 1/2 -/
noncomputable def psi (u : ℝ) : ℝ := Int.fract u - 1 / 2

/-- the periodic second Bernoulli function B₂({u}) = {u}² − {u} + 1/6 -/
noncomputable def B2per (u : ℝ) : ℝ := Int.fract u ^ 2 - Int.fract u + 1 / 6

/-- P = (B₂per − 1/6)/2, the continuous periodic antiderivative of ψ with P(n) = 0 -/
noncomputable def P (u : ℝ) : ℝ := (B2per u - 1 / 6) / 2

/-- Mathlib's `hasSum_one_div_nat_pow_mul_cos` with k = 1, unfolded:
Σ_{n ≥ 0} cos(2πnx)/n² = π² (x² − x + 1/6) for x ∈ [0, 1] (the n = 0 term is 0 in Lean). -/
lemma hasSum_cos_div_sq_bernoulli {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * x))
      (π ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval x
      = x ^ 2 - x + 1 / 6 := by
    have := bernoulliFun_two x
    rw [bernoulliFun] at this
    rw [show 2 * 1 = 2 by norm_num, this]
    norm_num
  rw [hb] at h
  have hval : (-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)
      * (x ^ 2 - x + 1 / 6) = π ^ 2 * (x ^ 2 - x + 1 / 6) := by
    have h2 : ((2 * 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2]; ring
  rw [hval] at h
  simpa using h

/-- periodicity of the cosine mode: cos(2π(ν+1)u) = cos(2π(ν+1){u}) -/
lemma cos_mode_fract (ν : ℕ) (u : ℝ) :
    Real.cos (2 * π * ((ν : ℝ) + 1) * u) = Real.cos (2 * π * ((ν : ℝ) + 1) * Int.fract u) := by
  have hu := Int.floor_add_fract u
  have : 2 * π * ((ν : ℝ) + 1) * u
      = 2 * π * ((ν : ℝ) + 1) * Int.fract u + ((((ν + 1 : ℕ) : ℤ) * ⌊u⌋ : ℤ) : ℝ) * (2 * π) := by
    push_cast
    linear_combination (-(2 * π * ((ν : ℝ) + 1))) * hu
  rw [this, Real.cos_add_int_mul_two_pi]

/-! ## B. The Fourier series of B₂per  (absolutely convergent) -/
theorem B2per_fourier (u : ℝ) :
    HasSum (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      (B2per u) := by
  have hx : Int.fract u ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have h := (hasSum_cos_div_sq_bernoulli hx).div_const (π ^ 2)
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one] at h2
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hf : (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      = fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos (2 * π * ((n + 1 : ℕ) : ℝ) * Int.fract u)
          / π ^ 2 := by
    funext ν
    rw [cos_mode_fract]
    push_cast
    have hν : ((ν : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hv : B2per u = π ^ 2 * (Int.fract u ^ 2 - Int.fract u + 1 / 6) / π ^ 2
      - 1 / ((0 : ℕ) : ℝ) ^ 2 * Real.cos (2 * π * ((0 : ℕ) : ℝ) * Int.fract u) / π ^ 2 := by
    simp only [B2per, Nat.cast_zero, zero_pow (two_ne_zero), div_zero, zero_mul]
    field_simp
    ring
  rw [hf, hv]
  exact h2

/-- Fourier series of P: P(u) + 1/12 = Σ_{ν≥1} cos(2πνu)/(2π²ν²). -/
theorem P_fourier (u : ℝ) :
    HasSum (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      (P u + 1 / 12) := by
  have h := (B2per_fourier u).div_const 2
  have hf : (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      = fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2) / 2 := by
    funext ν; rw [div_div]; ring
  have hv : P u + 1 / 12 = B2per u / 2 := by unfold P; ring
  rw [hf, hv]
  exact h

/-- |P u| ≤ 1/8 (in fact −1/8 ≤ P u ≤ 0). -/
theorem P_bound (u : ℝ) : |P u| ≤ 1 / 8 := by
  unfold P B2per
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract u - 1 / 2)]

theorem P_nonpos (u : ℝ) : P u ≤ 0 := by
  unfold P B2per
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  nlinarith

/-- P vanishes at the integers. -/
theorem P_intCast (n : ℤ) : P n = 0 := by
  simp [P, B2per, Int.fract_intCast]

theorem P_natCast (n : ℕ) : P n = 0 := by
  simp [P, B2per, Int.fract_natCast]

/-- P is continuous (B₂ is 1-periodic because B₂(0) = B₂(1)). -/
theorem P_continuous : Continuous P := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 2 - x) (Icc 0 1) := by fun_prop
  have h := ContinuousOn.comp_fract'' hf (by norm_num)
  have hP : P = fun u => ((fun x : ℝ => x ^ 2 - x) ∘ Int.fract) u / 2 := by
    funext u; simp only [P, B2per, Function.comp]; ring
  rw [hP]
  exact h.div_const 2

/-- P′ = ψ off the integers. -/
theorem hasDerivAt_P {u : ℝ} (hu : ∀ n : ℤ, u ≠ n) : HasDerivAt P (psi u) u := by
  have hlt : (⌊u⌋ : ℝ) < u := lt_of_le_of_ne (Int.floor_le u) (fun h => hu ⌊u⌋ h.symm)
  have hlt2 : u < ⌊u⌋ + 1 := Int.lt_floor_add_one u
  set c : ℝ := (⌊u⌋ : ℝ) with hc
  have hev : P =ᶠ[𝓝 u] fun x : ℝ => ((x - c) ^ 2 - (x - c)) / 2 := by
    filter_upwards [Ioo_mem_nhds hlt hlt2] with x hx
    have hfl : ⌊x⌋ = ⌊u⌋ := Int.floor_eq_on_Ico _ _ (Ioo_subset_Ico_self hx)
    simp only [P, B2per, ← Int.self_sub_floor, hfl, hc]
    ring
  have h1 : HasDerivAt (fun x : ℝ => x - c) 1 u := (hasDerivAt_id u).sub_const c
  have h2 : HasDerivAt (fun x : ℝ => (x - c) ^ 2) (2 * (u - c)) u := by
    have := h1.fun_pow 2
    simpa using this
  have hd : HasDerivAt (fun x : ℝ => ((x - c) ^ 2 - (x - c)) / 2)
      ((2 * (u - c) - 1) / 2) u := (h2.sub h1).div_const 2
  have hpsi : psi u = (2 * (u - c) - 1) / 2 := by
    rw [psi, ← Int.self_sub_floor, hc]; ring
  rw [hpsi]
  exact hd.congr_of_eventuallyEq hev

/-- the same with the hypothesis in the `Int.fract u ≠ 0` form -/
theorem hasDerivAt_P' {u : ℝ} (hu : Int.fract u ≠ 0) : HasDerivAt P (psi u) u := by
  apply hasDerivAt_P
  intro n hn
  apply hu
  rw [hn, Int.fract_intCast]

end BLClosure
