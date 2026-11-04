/-
G8W.lean — STRIP_PLAN node G8W: plan items G8 (Density/Geometry.lean) and W0, W1, W3
(Density/Window.lean).  Scratch file on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e).

Header and the DEFINITIONS block are copied verbatim from STRIP_PLAN.md §(C) (frozen; the
bodies of `Mx`, `fz`, `cm`, `dX`, `Leps`, `NSigma` are compared by Comparator and must not
change).  `open MNF.RH` is added before the block only so that `zeta_order` resolves; it does
not alter any definition body.
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

open Zeta23.BL

/-! ## W0 — the η-weighted square inequality (`Density/Window.lean`) -/

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

/-! ## W3 — pointwise bound for the mollifier (`Density/Window.lean`) -/

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

/-! ## G8 — the geometric factor (`Density/Geometry.lean`) -/

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

end Zeta23.Density
