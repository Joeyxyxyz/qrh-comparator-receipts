/-
J45.lean — plan nodes J4 and J5 of BOHR_LANDAU_PLAN (route B, Jensen on discs centred 2 + t·I).

J4: per-t count. For t ≥ 3 and radii 0 < r < R < 3, the multiplicity-weighted number of zeros of
    ζ in the closed inner ball `closedBall (2 + t I) r` times log(R/r) is at most
    circleAverage (log ‖ζ‖) (2 + t I) R − log ‖ζ(2 + t I)‖ ≤ circleAverage (log ‖ζ‖) (2 + t I) R + log 3.
J5: the majorant Lz z := (1/2)·log(1 + ‖ζ z‖²) ≥ log ‖ζ z‖, continuous and ≥ 0 away from 1, and
    circleAverage Lz c R ≤ (1/2)·log(1 + circleAverage ‖ζ‖² c R) by concavity of x ↦ log(1+x) on Ici 0.
-/
import Zeta23.BohrLandau
import Zeta23.RvM.ZetaGrowth
import Zeta23.BL.JensenDisc

open Set Complex MeasureTheory Metric MeromorphicOn
open Real (circleAverage circleAverage_mono circleAverage_eq_intervalAverage)
open scoped Real

namespace Zeta23.BL
open MNF.RH

/-! ## Geometry: the pole is outside every disc centred `2 + t I` of radius `< 3` when `t ≥ 3` -/

theorem one_notMem_closedBall_two_add {t R : ℝ} (ht : 3 ≤ t) (hR : R < 3) :
    (1 : ℂ) ∉ closedBall (2 + t * I) R := by
  intro h
  rw [mem_closedBall, dist_eq_norm] at h
  have him := Complex.abs_im_le_norm ((1 : ℂ) - (2 + t * I))
  have : ((1 : ℂ) - (2 + t * I)).im = -t := by simp
  rw [this, abs_neg, abs_of_pos (by linarith)] at him
  linarith

theorem one_notMem_sphere_two_add {t R : ℝ} (ht : 3 ≤ t) (hR : R < 3) :
    (1 : ℂ) ∉ sphere (2 + t * I) R :=
  fun h => one_notMem_closedBall_two_add ht hR (sphere_subset_closedBall h)

/-! ## J2: the divisor of ζ on a pole-free disc is `zeta_order` -/

theorem divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    (MeromorphicOn.divisor riemannZeta (closedBall c r) ρ : ℝ) = (zeta_order ρ : ℝ) := by
  rw [(Zeta23.RvM.analyticOnNhd_riemannZeta h1).divisor_apply hρ]
  have hne : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    Zeta23.analyticOrderAt_riemannZeta_ne_top (fun h => h1 (h ▸ hρ))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  unfold zeta_order
  rw [← hn]
  simp

/-! ## J4: per-t count in divisor form and in Finset form -/

/-- `-log ‖ζ(2 + t I)‖ ≤ log 3`, from `zeta_lower_bound_two`. -/
theorem neg_log_norm_riemannZeta_two_add_le (t : ℝ) :
    -Real.log ‖riemannZeta (2 + t * I)‖ ≤ Real.log 3 := by
  have h := Zeta23.RvM.zeta_lower_bound_two t
  have h' : Real.log (1 / 3) ≤ Real.log ‖riemannZeta (2 + t * I)‖ :=
    Real.log_le_log (by norm_num) h
  rw [one_div, Real.log_inv] at h'
  linarith

/-- J4, divisor form: Jensen's disc inequality for ζ on `closedBall (2 + t I) R`, `t ≥ 3`. -/
theorem count_disc_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3) :
    (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall (2 + t * I) r) u : ℝ))
        * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
          - Real.log ‖riemannZeta (2 + t * I)‖ :=
  sum_divisor_mul_log_le (2 + t * I) r R riemannZeta hr hrR
    (Zeta23.RvM.analyticOnNhd_riemannZeta (one_notMem_closedBall_two_add ht hR))
    (Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re (by simp))

/-- A finite set of nontrivial zeros inside the inner ball is dominated by the divisor sum. -/
theorem finset_sum_zeta_order_le_finsum_divisor {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall c r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ))
      ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) := by
  set D : ℂ → ℝ := fun u => (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) with hD
  have hζ := Zeta23.RvM.analyticOnNhd_riemannZeta h1
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor riemannZeta (closedBall c r)).finiteSupport (isCompact_closedBall ..)
      |>.subset fun _ _ ↦ (by simp_all)
  have hnn : ∀ u, 0 ≤ D u := fun u => by
    simp only [hD]
    exact_mod_cast hζ.divisor_nonneg u
  have h1' : ∑ ρ ∈ S, (zeta_order ρ : ℝ) = ∑ ρ ∈ S, D ρ := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [hD]
    exact (divisor_riemannZeta_eq h1 (hS ρ hρ).2).symm
  have h2 : ∑ᶠ u, D u = ∑ u ∈ S ∪ hfin.toFinset, D u :=
    finsum_eq_sum_of_support_subset D (by
      intro u hu
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inr hu)
  rw [h1', h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun u _ _ => hnn u)

/-- J4, Finset form (the plan's `count_window_le` with the ball membership as hypothesis):
for `t ≥ 3`, `0 < r < R < 3` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + t I) r`,
`(∑ ρ ∈ S, zeta_order ρ) · log (R/r) ≤ circleAverage (log ‖ζ‖) (2 + t I) R + log 3`. -/
theorem count_finset_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R + Real.log 3 := by
  have hlog : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).mpr hrR.le)
  have h1 := finset_sum_zeta_order_le_finsum_divisor
    (one_notMem_closedBall_two_add ht (hrR.trans hR)) S hS
  have h2 := count_disc_le ht hr hrR hR
  have h3 := neg_log_norm_riemannZeta_two_add_le t
  calc (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall (2 + t * I) r) u : ℝ))
          * Real.log (R / r) := mul_le_mul_of_nonneg_right h1 hlog
    _ ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
          - Real.log ‖riemannZeta (2 + t * I)‖ := h2
    _ ≤ _ := by linarith

/-! ## J5: the majorant `Lz` -/

/-- `Lz z = (1/2) log (1 + ‖ζ z‖²)`: a continuous, nonnegative majorant of `log ‖ζ z‖`. -/
noncomputable def Lz (z : ℂ) : ℝ := (1 / 2) * Real.log (1 + ‖riemannZeta z‖ ^ 2)

theorem Lz_nonneg (z : ℂ) : 0 ≤ Lz z := by
  unfold Lz
  have : (1 : ℝ) ≤ 1 + ‖riemannZeta z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have := Real.log_nonneg this
  positivity

/-- `log x ≤ (1/2) log (1 + x²)` for `x ≥ 0` (with the convention `log 0 = 0`). -/
theorem log_le_half_log_one_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ (1 / 2) * Real.log (1 + x ^ 2) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    simp only [Real.log_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.log_one, mul_zero, le_refl]
  · have h1 : Real.log (x ^ 2) ≤ Real.log (1 + x ^ 2) :=
      Real.log_le_log (pow_pos h 2) (le_add_of_nonneg_left zero_le_one)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

theorem log_norm_le_Lz (z : ℂ) : Real.log ‖riemannZeta z‖ ≤ Lz z :=
  log_le_half_log_one_add_sq (norm_nonneg _)

theorem continuousOn_Lz {U : Set ℂ} (hU : (1 : ℂ) ∉ U) : ContinuousOn Lz U := by
  have hζ : ContinuousOn riemannZeta U :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta hU).continuousOn
  unfold Lz
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · exact continuousOn_const.add (hζ.norm.pow 2)
  · intro z _
    positivity

theorem circleIntegrable_Lz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h1 : (1 : ℂ) ∉ sphere c R) :
    CircleIntegrable Lz c R :=
  (continuousOn_Lz h1).circleIntegrable hR

/-- J5 (first half): `circleAverage (log ‖ζ‖) c R ≤ circleAverage Lz c R` on pole-free circles. -/
theorem circleAverage_log_norm_le_Lz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h1 : (1 : ℂ) ∉ sphere c R) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) c R ≤ circleAverage Lz c R :=
  circleAverage_mono
    ((Zeta23.RvM.analyticOnNhd_riemannZeta h1).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR)
    (circleIntegrable_Lz hR h1)
    (fun z _ => log_norm_le_Lz z)

/-- `x ↦ (1/2) log (1 + x)` is concave on `Ici 0`. -/
theorem concaveOn_half_log_one_add :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => (1 / 2) * Real.log (1 + x)) := by
  have h1 : ConcaveOn ℝ ((fun z : ℝ => (1 : ℝ) + z) ⁻¹' Ioi 0) (Real.log ∘ fun z : ℝ => 1 + z) :=
    strictConcaveOn_log_Ioi.concaveOn.translate_right 1
  have h2 : ConcaveOn ℝ (Ici (0 : ℝ)) (Real.log ∘ fun z : ℝ => 1 + z) :=
    h1.subset (fun x hx => by simp only [mem_preimage, mem_Ioi]; linarith [mem_Ici.mp hx])
      (convex_Ici 0)
  have h3 := h2.smul (c := (1 / 2 : ℝ)) (by norm_num)
  simpa [smul_eq_mul, Function.comp] using h3

/-- J5 (second half): Jensen's inequality for the concave function `x ↦ (1/2) log (1 + x)`:
`circleAverage Lz c R ≤ (1/2) log (1 + circleAverage ‖ζ‖² c R)` on pole-free circles. -/
theorem circleAverage_Lz_le {c : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ sphere c R) :
    circleAverage Lz c R
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) c R) := by
  have hI : uIoc (0:ℝ) (2 * π) = Ioc 0 (2 * π) := uIoc_of_le (by positivity)
  have : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) (2 * π))) := by
    rw [hI]; infer_instance
  have : NeZero (volume (uIoc (0:ℝ) (2 * π))) := ⟨by simp⟩
  have hζ : ContinuousOn riemannZeta (sphere c R) :=
    (Zeta23.RvM.analyticOnNhd_riemannZeta h1).continuousOn
  have hcont : Continuous (fun θ : ℝ ↦ ‖riemannZeta (circleMap c R θ)‖ ^ 2) :=
    ((hζ.comp_continuous (continuous_circleMap c R)
      (fun θ ↦ circleMap_mem_sphere c hR.le θ)).norm).pow 2
  have hcont2 : Continuous (fun θ : ℝ ↦ (1 / 2) * Real.log (1 + ‖riemannZeta (circleMap c R θ)‖ ^ 2)) :=
    continuous_const.mul ((continuous_const.add hcont).log (fun θ => by
      show (1 : ℝ) + ‖riemannZeta (circleMap c R θ)‖ ^ 2 ≠ 0
      positivity))
  rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
  have key := concaveOn_half_log_one_add.le_map_average
    (μ := volume.restrict (uIoc (0:ℝ) (2 * π)))
    (f := fun θ : ℝ ↦ ‖riemannZeta (circleMap c R θ)‖ ^ 2)
    (by
      refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
      · exact continuousOn_const.add continuousOn_id
      · intro x hx; have := mem_Ici.mp hx; positivity)
    isClosed_Ici
    (by filter_upwards; simp)
    hcont.integrableOn_uIoc
    hcont2.integrableOn_uIoc
  exact key

/-- J4 + J5 combined: the per-t count against the log of the mean square on the outer circle.
For `t ≥ 3`, `0 < r < R < 3` and any finite set `S` of nontrivial zeros of ζ in
`closedBall (2 + t I) r`. -/
theorem count_finset_le_log_meanSq {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R)
    (hR : R < 3) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) R)
          + Real.log 3 := by
  have h1 := count_finset_le ht hr hrR hR S hS
  have h2 := circleAverage_log_norm_le_Lz (hr.trans hrR).le (one_notMem_sphere_two_add ht hR)
    (c := 2 + t * I)
  have h3 := circleAverage_Lz_le (hr.trans hrR) (one_notMem_sphere_two_add ht hR) (c := 2 + t * I)
  linarith

/-! ## J3 (plan §3): the disc geometry `Rout`, `rin`, `hwin`, and J4 in the plan's window form -/

/-- outer radius `2 - σ₁` (so the closed outer ball stays in `Re s ≥ σ₁`). -/
noncomputable def Rout (σ₁ : ℝ) : ℝ := 2 - σ₁
/-- inner radius: midpoint of `3/2 - δ` (the reach needed for `Re ρ ≥ 1/2 + δ`) and `Rout σ₁`. -/
noncomputable def rin (σ₁ δ : ℝ) : ℝ := (Rout σ₁ + (3 / 2 - δ)) / 2
/-- half-window in `t`: zeros with `|t - Im ρ| ≤ hwin` and `Re ρ ≥ 1/2 + δ` lie in the inner ball. -/
noncomputable def hwin (σ₁ δ : ℝ) : ℝ := Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2

theorem geom_facts {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧
    ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ →
      ρ ∈ Metric.closedBall (2 + t * I) (rin σ₁ δ) := by
  have hRout : Rout σ₁ = 2 - σ₁ := rfl
  have hrin : rin σ₁ δ = (Rout σ₁ + (3 / 2 - δ)) / 2 := rfl
  have hrin_pos : 0 < rin σ₁ δ := by rw [hrin, hRout]; linarith
  have hrR : rin σ₁ δ < Rout σ₁ := by rw [hrin, hRout]; linarith
  have hR32 : Rout σ₁ < 3 / 2 := by rw [hRout]; linarith
  have hreach : 3 / 2 - δ < rin σ₁ δ := by rw [hrin, hRout]; linarith
  have hreach0 : 0 ≤ 3 / 2 - δ := by linarith
  have hdisc : 0 < rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2 := by nlinarith
  have hhw : hwin σ₁ δ ^ 2 = (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 4 := by
    unfold hwin
    rw [div_pow, Real.sq_sqrt hdisc.le]; norm_num
  have hhw_pos : 0 < hwin σ₁ δ := by
    unfold hwin; exact div_pos (Real.sqrt_pos.mpr hdisc) two_pos
  have hhw_le : hwin σ₁ δ ≤ 1 := by
    unfold hwin
    rw [div_le_iff₀ two_pos, Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ⟨hrin_pos, hrR, hR32, hhw_pos, hhw_le, ?_⟩
  intro ρ hρ1 hρ2 t ht
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hrin_pos.le two_ne_zero, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, sub_im, add_im, mul_im, re_ofNat, im_ofNat, zero_add]
  have hre : 0 < 2 - ρ.re := by linarith
  have hre' : 2 - ρ.re ≤ 3 / 2 - δ := by linarith
  have habs : (t - ρ.im) ^ 2 ≤ hwin σ₁ δ ^ 2 := by
    have := abs_le.mp ht
    nlinarith [this.1, this.2]
  have hre2 : (ρ.re - 2) * (ρ.re - 2) ≤ (3 / 2 - δ) ^ 2 := by nlinarith
  have : (ρ.im - t) * (ρ.im - t) = (t - ρ.im) ^ 2 := by ring
  nlinarith

/-- the closed outer ball lies in the half-plane `Re s ≥ σ₁`. -/
theorem closedBall_Rout_subset {σ₁ t : ℝ} :
    Metric.closedBall (2 + t * I) (Rout σ₁) ⊆ {s : ℂ | σ₁ ≤ s.re} := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - (2 + t * I))
  have hre : (z - (2 + t * I)).re = z.re - 2 := by simp
  rw [hre] at h
  have := (abs_le.mp (h.trans hz)).1
  show σ₁ ≤ z.re
  unfold Rout at this
  linarith

/-- J4 in the plan's window form (`count_window_le` of BOHR_LANDAU_PLAN §3). -/
theorem count_window_le {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) (Rout σ₁)
          + Real.log 3 := by
  obtain ⟨hr, hrR, hR, -, -, hmem⟩ := geom_facts h1 hδσ hδ
  refine count_finset_le ht hr hrR (by linarith) S fun ρ hρ => ?_
  obtain ⟨hz, hδρ, hwt⟩ := hS ρ hρ
  exact ⟨hz, hmem ρ (by linarith) hz.2.2 t hwt⟩

/-- J4 + J5 in the plan's window form, with the outer circle average of `log ‖ζ‖` replaced by
`(1/2) log (1 + circleAverage ‖ζ‖²)`. -/
theorem count_window_le_log_meanSq {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2) {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + t * I) (Rout σ₁))
          + Real.log 3 := by
  obtain ⟨hr, hrR, hR, -, -, hmem⟩ := geom_facts h1 hδσ hδ
  refine count_finset_le_log_meanSq ht hr hrR (by linarith) S fun ρ hρ => ?_
  obtain ⟨hz, hδρ, hwt⟩ := hS ρ hρ
  exact ⟨hz, hmem ρ (by linarith) hz.2.2 t hwt⟩

/-- The plan's `circleAverage_log_le_Lz` (J5), specialised to the discs centred `2 + t I`. -/
theorem circleAverage_log_le_Lz {t R : ℝ} (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3 / 2) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
      ≤ circleAverage Lz (2 + t * I) R :=
  circleAverage_log_norm_le_Lz hR.le (one_notMem_sphere_two_add ht (by linarith))

end Zeta23.BL
