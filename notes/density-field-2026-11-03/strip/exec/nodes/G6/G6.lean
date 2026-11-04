/-
G6.lean — node G6 of STRIP_PLAN.md: the Fubini swap for `Leps ε (fz X)` on the discs centred
`2 + t I`, with its integrability lemmas (target module `Density/Fubini.lean`).  Scratch file,
compiled against the zeta23 tree with `lake env lean`.  No `sorry`.

Pattern copy of `BohrLandauPartial.lean:1605-1652` and `:1676-1686` with `Lz` replaced by
`Leps ε (fz X)` and the window `[3, T + 3]` replaced by `[a, a + ℓ]`, `3 ≤ a`:
  * `continuousOn_Leps_circleMap`          (`:1605`)  joint continuity on `{t ≥ 3} × ℝ`
  * `integrableOn_Leps_circleMap_prod`     (`:1616`)  product integrability on the rectangle
  * `integrable_Leps_circleMap_prod_restrict` (`:1626`) the same for the product measure
  * `intervalIntegrable_circleAverage_Leps` (`:1634`)  the marginal `t ↦ circleAverage`
  * `integral_circleAverage_Leps_eq_swap`  (`:1649`)  G6, Fubini
  * `intervalIntegrable_Leps_segment`      (`:1676`)  `Leps ε (fz X)` along a vertical segment
  * `intervalIntegrable_normSq_fz_segment` (`:1682`)  `‖fz X‖²` along a vertical segment

Scratch files cannot be imported, so the upstream lemmas used (C1 `analyticOnNhd_Mx`, C1'
`analyticOnNhd_fz` / `continuousOn_fz` from exec/C/C.lean, and `continuousOn_Leps` from
exec/G1/G1.lean) are copied verbatim below, marked as such.
-/
import Zeta23.BL.BohrLandauClosure

/-! ## DEFINITIONS — the frozen block of STRIP_PLAN.md §(C), copied verbatim
(`open MNF.RH` is added only so that `zeta_order` resolves, as in `Zeta23/BohrLandau.lean:10`;
no definition body is changed). -/

namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius
open MNF.RH

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

/-! ## Upstream lemmas, copied verbatim (C1, C1' from exec/C/C.lean; `continuousOn_Leps` from
exec/G1/G1.lean) -/

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

/-- `Leps ε f` is continuous wherever `f` is (since `ε² + ‖f‖² > 0`). -/
theorem continuousOn_Leps {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ContinuousOn f U) : ContinuousOn (Leps ε f) U := by
  unfold Leps
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · exact continuousOn_const.add (hf.norm.pow 2)
  · intro z _
    have := pow_pos hε 2
    positivity

/-! ## G6 — Fubini for `Leps ε (fz X)` on the discs centred `2 + t I` -/

open Real (circleAverage circleAverage_def)
open scoped Real

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

end Zeta23.Density

#print axioms Zeta23.Density.continuousOn_Leps_fz_ne_one
#print axioms Zeta23.Density.continuousOn_Leps_circleMap
#print axioms Zeta23.Density.integrableOn_Leps_circleMap_prod
#print axioms Zeta23.Density.integrable_Leps_circleMap_prod_restrict
#print axioms Zeta23.Density.intervalIntegrable_circleAverage_Leps
#print axioms Zeta23.Density.integral_circleAverage_Leps_eq_swap
#print axioms Zeta23.Density.intervalIntegrable_Leps_segment
#print axioms Zeta23.Density.intervalIntegrable_normSq_fz_segment
