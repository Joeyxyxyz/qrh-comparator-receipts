/-
G1.lean — node G1 of STRIP_PLAN.md: the ε-majorant `Leps` (plan items G1a, G1b, G1c, G1d, G3;
target module `Density/Majorant.lean`).  Scratch file, compiled against the zeta23 tree with
`lake env lean`.  No `sorry`.

`Leps ε f z = (1/2) log (ε² + ‖f z‖²)` replaces the tree's `Lz z = (1/2) log (1 + ‖ζ z‖²)`
(`BohrLandauPartial.lean:1426`): it still majorises `log ‖f z‖` wherever `f z ≠ 0` (G1a), it is
concave in `‖f‖²` (G1b), so an interval average of it is bounded by the value at the mean square
(G1c, Jensen), and on a circle it majorises the circle average of `log ‖f‖` (G3, the a.e. form of
`JensenDisc.lean:63-116` with `log ‖f‖ ≤ (1/2) log ‖f‖²` replaced by G1a).
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

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

/-! ## G1 — the ε-majorant, generic `f` -/

open Real (circleAverage circleAverage_def)
open scoped Real

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

end Zeta23.Density

#print axioms Zeta23.Density.log_norm_le_Leps
#print axioms Zeta23.Density.concaveOn_half_log_add
#print axioms Zeta23.Density.half_log_le_half
#print axioms Zeta23.Density.segment_average_Leps_le
#print axioms Zeta23.Density.continuousOn_Leps
#print axioms Zeta23.Density.circleAverage_log_norm_le_Leps
