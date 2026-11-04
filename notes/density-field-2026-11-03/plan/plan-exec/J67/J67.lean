/-
J67.lean — plan nodes J6 and J7 of BOHR_LANDAU_PLAN.md (route B: Jensen on discs centred
`2 + t I`, averaged in `t`).

J6 (`count_le_integral`): integrate the per-`t` count of J4+J5 over `t ∈ [3, T + 3]`:
    2 h log(R/r) (NRight δ T − NRight δ 4) ≤ ∫ t in 3..T+3, (circleAverage Lz (2 + t I) R + log 3).
J7 (`integral_circleAverage_Lz_eq_swap`, `integral_Lz_circle_le`, `integral_circleAverage_Lz_le`):
    Fubini on the rectangle [3, T+3] × [0, 2π], then for each θ the inner integral runs along the
    vertical segment Re s = 2 + R cos θ ∈ [σ₁, 2 + R], shifted and enlarged to u ∈ [1, T + 5]
    (Lz ≥ 0), and `Lz ≤ (1/2) ‖ζ‖²` (from log(1 + x) ≤ x) reduces it to the uniform mean square
    `∫ u in 1..T', ‖ζ(σ + u I)‖² ≤ C T'`, taken as the hypothesis `hMS`.
J6 + J7 (`count_le_meanSquare`):
    2 h log(R/r) (NRight δ T − NRight δ 4) ≤ (1/2) C (T + 5) + T log 3   (T ≥ 4).

The J0 lemmas of J023.lean and the J4/J5 lemmas of J45.lean are scratch files, not modules of
the tree, so the ones used here are copied verbatim below (sections marked "copied").
-/
import Zeta23.BohrLandau
import Zeta23.RvM.ZetaGrowth
import Zeta23.BL.JensenDisc

set_option lang.lemmaCmd true

open Set Complex MeasureTheory Metric MeromorphicOn
open Real (circleAverage circleAverage_mono circleAverage_eq_intervalAverage circleAverage_def)
open scoped Real

namespace Zeta23.BL
open MNF.RH

/-! ## Copied from J023.lean (J0): splitting `NRight` at height 4 -/

/-- Window splitting for MNF's `zerosIn` (copy of `Zeta23.zerosIn_union`). -/
theorem MNF_zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    MNF.RH.zerosIn a c = MNF.RH.zerosIn a b ∪ MNF.RH.zerosIn b c := by
  ext ρ
  simp only [MNF.RH.zerosIn, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

/-- `NRight` splits at any intermediate height `a`. -/
theorem NRight_add {δ a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    NRight δ T
      = NRight δ a + ∑ᶠ ρ ∈ MNF.RH.zerosIn a T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ := by
  unfold NRight
  rw [MNF_zerosIn_union ha haT, union_inter_distrib_right]
  refine finsum_mem_union ?_ ((MNF.RH.zerosIn_finite 0 a).subset inter_subset_left)
    ((MNF.RH.zerosIn_finite a T).subset inter_subset_left)
  rw [disjoint_left]
  rintro ρ ⟨⟨_, _, hb⟩, _⟩ ⟨⟨_, ha', _⟩, _⟩
  exact absurd hb (not_le.2 ha')

/-- The plan's J0 statement: the count between heights 4 and `T`, as a real finsum. -/
theorem NRight_sub_eq {δ T : ℝ} (hT : 4 ≤ T) :
    (NRight δ T : ℝ) - NRight δ 4
      = ∑ᶠ ρ ∈ MNF.RH.zerosIn 4 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, (zeta_order ρ : ℝ) := by
  rw [NRight_add (by norm_num : (0:ℝ) ≤ 4) hT, Nat.cast_add,
    Nat.cast_finsum_mem ((MNF.RH.zerosIn_finite 4 T).subset inter_subset_left)]
  ring

/-! ## Copied from J45.lean (J2, J4, J5, J3): the per-`t` count and the majorant `Lz` -/

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

/-- J4, Finset form. -/
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

/-- The plan's `circleAverage_log_le_Lz` (J5), specialised to the discs centred `2 + t I`. -/
theorem circleAverage_log_le_Lz {t R : ℝ} (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3 / 2) :
    circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
      ≤ circleAverage Lz (2 + t * I) R :=
  circleAverage_log_norm_le_Lz hR.le (one_notMem_sphere_two_add ht (by linarith))

/-! ## New: J7 preliminaries — the circle points, joint continuity, product integrability -/

/-- `circleMap (2 + t I) R θ = (2 + R cos θ) + (t + R sin θ) I`. -/
theorem circleMap_two_add (t R θ : ℝ) :
    circleMap (2 + t * I) R θ
      = ((2 + R * Real.cos θ : ℝ) : ℂ) + ((t + R * Real.sin θ : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- For `t ≥ 3`, `0 ≤ R < 3`, the circle `circleMap (2 + t I) R` avoids the pole. -/
theorem circleMap_two_add_ne_one {t R : ℝ} (ht : 3 ≤ t) (hR0 : 0 ≤ R) (hR : R < 3) (θ : ℝ) :
    circleMap (2 + t * I) R θ ≠ 1 :=
  fun h => one_notMem_sphere_two_add ht hR (h ▸ circleMap_mem_sphere _ hR0 θ)

/-- `(t, θ) ↦ Lz (circleMap (2 + t I) R θ)` is continuous on `{t ≥ 3} × ℝ`. -/
theorem continuousOn_Lz_circleMap {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    ContinuousOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2)) (Ici 3 ×ˢ univ) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap (2 + p.1 * I) R p.2) := by
    unfold circleMap
    fun_prop
  refine (continuousOn_Lz (U := {z : ℂ | z ≠ 1}) (by simp)).comp hc.continuousOn ?_
  rintro ⟨t, θ⟩ ⟨ht, -⟩
  show circleMap (2 + t * I) R θ ≠ 1
  exact circleMap_two_add_ne_one ht hR0 hR θ

/-- Product integrability of `Lz ∘ circleMap` on the rectangle `(3, T+3] × (0, 2π]`. -/
theorem integrableOn_Lz_circleMap_prod {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    IntegrableOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      (Ioc 3 (T + 3) ×ˢ Ioc 0 (2 * π)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      (Icc 3 (T + 3) ×ˢ Icc 0 (2 * π)) :=
    (continuousOn_Lz_circleMap hR0 hR).mono (prod_mono Icc_subset_Ici_self (subset_univ _))
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The same, for the product of the restricted measures (the form Fubini consumes). -/
theorem integrable_Lz_circleMap_prod_restrict {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) :
    Integrable (fun p : ℝ × ℝ => Lz (circleMap (2 + p.1 * I) R p.2))
      ((volume.restrict (Ioc 3 (T + 3))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact integrableOn_Lz_circleMap_prod hR0 hR

/-- `t ↦ circleAverage Lz (2 + t I) R` is interval integrable on `[3, T + 3]`
(marginal of the product integrability). -/
theorem intervalIntegrable_circleAverage_Lz {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => circleAverage Lz (2 + t * I) R) volume 3 (T + 3) := by
  have h2 := (integrable_Lz_circleMap_prod_restrict (T := T) hR0 hR).integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have heq : (fun t : ℝ => circleAverage Lz (2 + t * I) R)
      = fun t : ℝ => (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), Lz (circleMap (2 + t * I) R θ) := by
    funext t
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
  rw [heq]
  exact h2.const_mul _

/-! ## J7 (first half): Fubini -/

/-- J7, Fubini form: the `t`-integral of the circle averages is `(2π)⁻¹` times the `θ`-integral
of the `t`-integrals along the circle points. -/
theorem integral_circleAverage_Lz_eq_swap {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (hT : 0 ≤ T) :
    ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) R
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) R θ) := by
  simp_rw [circleAverage_def, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral_intervalIntegral_swap ?_
  rw [uIoc_of_le (by linarith : (3:ℝ) ≤ T + 3), uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
  exact integrableOn_Lz_circleMap_prod hR0 hR

/-! ## J7 (second half): the inner integral along a vertical segment -/

/-- `Lz z ≤ (1/2) ‖ζ z‖²`, from `log (1 + x) ≤ x`. -/
theorem Lz_le_half_sq (z : ℂ) : Lz z ≤ (1 / 2) * ‖riemannZeta z‖ ^ 2 := by
  unfold Lz
  have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + ‖riemannZeta z‖ ^ 2)
  exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- The vertical segment `σ + u I`, `u ∈ [a, b]` with `a > 0`, avoids the pole. -/
theorem segment_mapsTo_ne_one {σ a b : ℝ} (ha : 0 < a) :
    MapsTo (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) (Icc a b) {z : ℂ | z ≠ 1} := by
  intro u hu heq
  have := congrArg Complex.im heq
  simp at this
  linarith [hu.1]

theorem intervalIntegrable_Lz_segment {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => Lz ((σ : ℂ) + (u : ℂ) * I)) volume a b :=
  ((continuousOn_Lz (U := {z : ℂ | z ≠ 1}) (by simp)).comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (segment_mapsTo_ne_one ha)).intervalIntegrable_of_Icc hab

theorem intervalIntegrable_normSq_zeta_segment {σ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2) volume a b :=
  (((Zeta23.RvM.analyticOnNhd_riemannZeta (S := {z : ℂ | z ≠ 1}) (by simp)).continuousOn.comp
    (by fun_prop : Continuous fun u : ℝ => (σ : ℂ) + (u : ℂ) * I).continuousOn
    (segment_mapsTo_ne_one ha)).norm.pow 2).intervalIntegrable_of_Icc hab

/-- J7, per-`θ` bound: along the circle points `circleMap (2 + t I) (Rout σ₁) θ`, `t ∈ [3, T+3]`,
the integral of `Lz` is an integral along the vertical segment `Re s = 2 + Rout σ₁ cos θ`
(which lies in `[σ₁, 2 + Rout σ₁]`), enlarged to `u ∈ [1, T + 5]`, and bounded via
`Lz ≤ (1/2)‖ζ‖²` by the uniform mean square `hMS`. -/
theorem integral_Lz_circle_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ} (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) (θ : ℝ) :
    ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ) ≤ (1 / 2) * (C * (T + 5)) := by
  have hRdef : Rout σ₁ = 2 - σ₁ := rfl
  have hR0 : 0 < Rout σ₁ := by rw [hRdef]; linarith
  have hR : Rout σ₁ < 3 / 2 := by rw [hRdef]; linarith
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hR0.le
  have hcos' := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hR0.le
  have hsin : |Rout σ₁ * Real.sin θ| ≤ Rout σ₁ := by
    rw [abs_mul, abs_of_pos hR0]
    exact mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)
  have hsin' := abs_le.1 hsin
  have hσ1 : σ₁ ≤ 2 + Rout σ₁ * Real.cos θ := by rw [hRdef] at hcos ⊢; linarith
  have hσ2 : 2 + Rout σ₁ * Real.cos θ ≤ 2 + Rout σ₁ := by linarith
  simp_rw [circleMap_two_add]
  have hshift := intervalIntegral.integral_comp_add_right (a := 3) (b := T + 3)
    (fun u : ℝ => Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I))
    (Rout σ₁ * Real.sin θ)
  rw [hshift]
  calc ∫ u in (3 + Rout σ₁ * Real.sin θ)..(T + 3 + Rout σ₁ * Real.sin θ),
          Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)
      ≤ ∫ u in (1:ℝ)..(T + 5), Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I) :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun u => Lz_nonneg _)
          (intervalIntegrable_Lz_segment one_pos (by linarith))
    _ ≤ ∫ u in (1:ℝ)..(T + 5),
          (1 / 2) * ‖riemannZeta (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith)
          (intervalIntegrable_Lz_segment one_pos (by linarith))
          ((intervalIntegrable_normSq_zeta_segment one_pos (by linarith)).const_mul _)
          (fun u _ => Lz_le_half_sq _)
    _ = (1 / 2) * ∫ u in (1:ℝ)..(T + 5),
          ‖riemannZeta (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (1 / 2) * (C * (T + 5)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hMS _ hσ1 hσ2 (T + 5) (by linarith)

/-- J7, assembled: the `t`-integral of the circle averages of `Lz` over `[3, T + 3]` is at most
`(1/2) C (T + 5)` under the uniform mean square hypothesis `hMS` on `σ ∈ [σ₁, 2 + Rout σ₁]`. -/
theorem integral_circleAverage_Lz_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ}
    (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) :
    ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) (Rout σ₁) ≤ (1 / 2) * (C * (T + 5)) := by
  have hR0 : 0 < Rout σ₁ := by show 0 < 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  rw [integral_circleAverage_Lz_eq_swap hR0.le hR hT]
  have hG0 : ∀ θ : ℝ, 0 ≤ ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ) :=
    fun θ => intervalIntegral.integral_nonneg (by linarith) (fun t _ => Lz_nonneg _)
  have hGle : ∀ θ : ℝ, ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)
      ≤ (1 / 2) * (C * (T + 5)) := integral_Lz_circle_le h1 h2 hT hMS
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun θ : ℝ => ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ))
    (C := (1 / 2) * (C * (T + 5))) (fun θ _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 θ)]; exact hGle θ)
  rw [sub_zero, abs_of_pos (by positivity)] at hnorm
  have hpi : 0 ≤ (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)
      ≤ (2 * π)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * π),
          ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ)‖ :=
        mul_le_mul_of_nonneg_left (Real.le_norm_self _) hpi
    _ ≤ (2 * π)⁻¹ * ((1 / 2) * (C * (T + 5)) * (2 * π)) :=
        mul_le_mul_of_nonneg_left hnorm hpi
    _ = (1 / 2) * (C * (T + 5)) := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-! ## J6: integrate the per-`t` count over `t ∈ [3, T + 3]` -/

/-- J6 (`count_le_integral` of BOHR_LANDAU_PLAN §3): every zero `ρ` with `Re ρ ≥ 1/2 + δ`,
`4 < Im ρ ≤ T` lies in the inner ball `closedBall (2 + t I) (rin σ₁ δ)` for all `t` in the window
`[Im ρ − hwin, Im ρ + hwin] ⊆ [3, T + 3]`, so integrating the per-`t` bound of J4+J5 over
`t ∈ [3, T + 3]` gives the multiplicity-weighted count times `2 hwin log (Rout/rin)`. -/
theorem count_le_integral {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3) := by
  obtain ⟨hr, hrR, hR, hh, hh1, -⟩ := geom_facts h1 hδσ hδ
  -- the zeros counted by `NRight δ T - NRight δ 4`
  have hZfin : (MNF.RH.zerosIn 4 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2}).Finite :=
    (MNF.RH.zerosIn_finite 4 T).subset inter_subset_left
  have hcount : (NRight δ T : ℝ) - NRight δ 4 = ∑ ρ ∈ hZfin.toFinset, (zeta_order ρ : ℝ) := by
    rw [NRight_sub_eq hT, finsum_mem_eq_finite_toFinset_sum _ hZfin]
  -- the step functions `g ρ`: `zeta_order ρ` on the window of `ρ`, `0` elsewhere
  set g : ℂ → ℝ → ℝ := fun ρ t =>
    (Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)).indicator (fun _ => (zeta_order ρ : ℝ)) t with hg
  -- pointwise, for `t ∈ [3, T + 3]`: J4 + J5 applied to the zeros whose window contains `t`
  have hpt : ∀ t ∈ Icc (3:ℝ) (T + 3),
      (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
        ≤ circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3 := by
    intro t ht
    have ht3 : 3 ≤ t := ht.1
    classical
    set S : Finset ℂ := Finset.filter
      (fun ρ : ℂ => t ∈ Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ)) hZfin.toFinset with hS
    have hsum : ∑ ρ ∈ hZfin.toFinset, g ρ t = ∑ ρ ∈ S, (zeta_order ρ : ℝ) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [hg, Set.indicator_apply]
    rw [hsum]
    have hcw := count_window_le h1 hδσ hδ ht3 S (fun ρ hρ => by
      rw [hS, Finset.mem_filter, Finite.mem_toFinset] at hρ
      obtain ⟨⟨⟨hz, -, -⟩, hδρ⟩, hρt⟩ := hρ
      have h1' : ρ.im - hwin σ₁ δ ≤ t := hρt.1
      have h2' : t ≤ ρ.im + hwin σ₁ δ := hρt.2
      exact ⟨hz, hδρ, abs_le.2 ⟨by linarith, by linarith⟩⟩)
    have hLz := circleAverage_log_le_Lz ht3 (hr.trans hrR) hR
    linarith
  -- the step functions are integrable, with integral `2 hwin · zeta_order ρ`
  have hgi : ∀ ρ ∈ hZfin.toFinset, IntervalIntegrable (g ρ) volume 3 (T + 3) := by
    intro ρ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact (integrable_const _).indicator measurableSet_Icc
  have hgint : ∀ ρ ∈ hZfin.toFinset,
      ∫ t in (3:ℝ)..(T + 3), g ρ t = 2 * hwin σ₁ δ * (zeta_order ρ : ℝ) := by
    intro ρ hρ
    rw [Finite.mem_toFinset] at hρ
    obtain ⟨⟨-, h4, hT'⟩, -⟩ := hρ
    have hsub : Icc (ρ.im - hwin σ₁ δ) (ρ.im + hwin σ₁ δ) ⊆ Ioc 3 (T + 3) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp only [hg]
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
      inter_eq_left.2 hsub, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  -- integrate the pointwise bound
  have hLHSint : IntervalIntegrable
      (fun t => (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)) volume 3 (T + 3) := by
    have := (IntervalIntegrable.sum hZfin.toFinset hgi).mul_const (Real.log (Rout σ₁ / rin σ₁ δ))
    simpa only [Finset.sum_apply] using this
  have hRHSint : IntervalIntegrable
      (fun t => circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3) volume 3 (T + 3) :=
    (intervalIntegrable_circleAverage_Lz (hr.trans hrR).le (by linarith) (by linarith)).add
      intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (by linarith) hLHSint hRHSint hpt
  have hLHS : ∫ t in (3:ℝ)..(T + 3),
        (∑ ρ ∈ hZfin.toFinset, g ρ t) * Real.log (Rout σ₁ / rin σ₁ δ)
      = 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_finsetSum hgi,
      Finset.sum_congr rfl hgint, ← Finset.mul_sum, ← hcount]
    ring
  rw [← hLHS]
  exact hmono

/-! ## J6 + J7 assembled -/

/-- J6 + J7: for `T ≥ 4`, under the uniform mean square hypothesis `hMS` on
`σ ∈ [σ₁, 2 + Rout σ₁]` with constant `C`,
`2 hwin log(Rout/rin) (NRight δ T − NRight δ 4) ≤ (1/2) C (T + 5) + T log 3`. -/
theorem count_le_meanSquare {σ₁ δ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ (1 / 2) * (C * (T + 5)) + T * Real.log 3 := by
  have hR0 : 0 ≤ Rout σ₁ := by show 0 ≤ 2 - σ₁; linarith
  have hR : Rout σ₁ < 3 := by show 2 - σ₁ < 3; linarith
  have h6 := count_le_integral h1 hδσ hδ hT
  have h7 := integral_circleAverage_Lz_le (T := T) h1 h2 (by linarith) hMS
  rw [intervalIntegral.integral_add
    (intervalIntegrable_circleAverage_Lz (T := T) hR0 hR (by linarith))
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h6
  have : (T + 3 - 3) * Real.log 3 = T * Real.log 3 := by ring
  linarith

/-- The same with the mean square hypothesis in the shape of `MeanSquareUnifFrom σ₁`
(no upper bound on `σ`). -/
theorem count_le_meanSquare' {σ₁ δ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ (1 / 2) * (C * (T + 5)) + T * Real.log 3 :=
  count_le_meanSquare h1 h2 hδσ hδ (fun σ hσ _ T hT => hMS σ hσ T hT) hT

/-! ## The region `σ > 1`: the trivial bound, so `hMS` need only be supplied on `[σ₁, σ₂]`, σ₂ > 1 -/

/-- `ζ(σ) ≤ ζ(σ₂)` for `σ ≥ σ₂ > 1` (as sums `∑ 1/n^σ`). -/
theorem tsum_one_div_rpow_anti {σ₂ σ : ℝ} (h2 : 1 < σ₂) (hσ : σ₂ ≤ σ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ σ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ σ₂ := by
  refine (Real.summable_one_div_nat_rpow.2 (h2.trans_le hσ)).tsum_le_tsum (fun n => ?_)
    (Real.summable_one_div_nat_rpow.2 h2)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : σ ≠ 0), Real.zero_rpow (by linarith : σ₂ ≠ 0)]
  · have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn' hσ)

/-- For `σ ≥ σ₂ > 1` the mean square on `[1, T]` is at most `ζ(σ₂)² T` (trivial bound). -/
theorem meanSquare_of_gt_one {σ₂ σ : ℝ} (h2 : 1 < σ₂) (hσ : σ₂ ≤ σ) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ σ₂) ^ 2 * T := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ σ₂ with hZ
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := T) (C := Z ^ 2)
    (f := fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_zeta_le_tsum (h2.trans_le hσ) t).trans (tsum_one_div_rpow_anti h2 hσ)) 2)
  rw [abs_of_nonneg (by linarith)] at h
  calc _ ≤ ‖∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ Z ^ 2 * (T - 1) := h
    _ ≤ Z ^ 2 * T := by nlinarith [sq_nonneg Z]

/-- A mean square hypothesis on `[σ₁, σ₂]` with `σ₂ > 1` extends to all `σ ≥ σ₁`
(constant `max C ζ(σ₂)²`). -/
theorem meanSquare_hyp_extend {σ₁ σ₂ C : ℝ} (h2 : 1 < σ₂)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) :
    ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2
        ≤ max C ((∑' n : ℕ, 1 / (n : ℝ) ^ σ₂) ^ 2) * T := by
  intro σ hσ T hT
  rcases le_or_gt σ σ₂ with h | h
  · exact (hMS σ hσ h T hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · exact (meanSquare_of_gt_one h2 h.le (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

end Zeta23.BL

#print axioms Zeta23.BL.count_le_integral
#print axioms Zeta23.BL.integral_circleAverage_Lz_eq_swap
#print axioms Zeta23.BL.integral_Lz_circle_le
#print axioms Zeta23.BL.integral_circleAverage_Lz_le
#print axioms Zeta23.BL.count_le_meanSquare
#print axioms Zeta23.BL.count_le_meanSquare'
#print axioms Zeta23.BL.meanSquare_hyp_extend
