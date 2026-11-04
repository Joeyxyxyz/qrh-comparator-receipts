/-
J023 — plan nodes J0 (trivialities), J2 (divisor of ζ on a closed ball = `zeta_order`),
J3 (geometry constants) of BOHR_LANDAU_PLAN.md.

Scratch file; imports only built modules of the zeta23 tree.
-/
import Zeta23.BohrLandau
import Zeta23.RvM.ZetaGrowth
import Zeta23.BL.JensenDisc

set_option lang.lemmaCmd true

open Set Complex Metric

namespace Zeta23.BL
open MNF.RH

/-! ## J0 — trivialities about `NRight` -/

/-- δ ≥ 1/2: no nontrivial zero has `Re ρ - 1/2 ≥ δ` (since `Re ρ < 1`), so the count is 0. -/
theorem NRight_eq_zero_of_half_le {δ T : ℝ} (hδ : 1 / 2 ≤ δ) : NRight δ T = 0 := by
  unfold NRight
  have h : MNF.RH.zerosIn 0 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2} = ∅ := by
    ext ρ
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hz, _, _⟩ hδρ
    linarith [hz.2.2]
  rw [h, finsum_mem_empty]

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

/-- `NRight δ T` is monotone in `T` (needed by J8 for `2 ≤ T < 4`). -/
theorem NRight_mono {δ T T' : ℝ} (h : T ≤ T') : NRight δ T ≤ NRight δ T' := by
  unfold NRight
  rw [finsum_mem_eq_finite_toFinset_sum _ ((MNF.RH.zerosIn_finite 0 T).subset inter_subset_left),
    finsum_mem_eq_finite_toFinset_sum _ ((MNF.RH.zerosIn_finite 0 T').subset inter_subset_left)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Finite.mem_toFinset] at hρ ⊢
  exact ⟨MNF.RH.zerosIn_mono le_rfl h hρ.1, hρ.2⟩

/-! ## J2 — the divisor of ζ on a closed ball avoiding the pole -/

/-- At a point `ρ ≠ 1` where ζ does not vanish, `zeta_order ρ = 0`. -/
theorem zeta_order_eq_zero_of_ne_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (h : riemannZeta ρ ≠ 0) :
    zeta_order ρ = 0 := by
  unfold zeta_order
  rw [(MNF.RH.analyticAt_riemannZeta hρ1).analyticOrderAt_eq_zero.2 h]
  rfl

/-- The divisor of ζ on a closed ball not containing 1 is `zeta_order` (ℤ-valued form). -/
theorem divisor_riemannZeta_eq_int {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    MeromorphicOn.divisor riemannZeta (closedBall c r) ρ = (zeta_order ρ : ℤ) := by
  have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hρ)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (Zeta23.RvM.analyticOnNhd_riemannZeta h1) hρ]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1)
  unfold zeta_order
  rw [← hn, ENat.map_natCast, ENat.toNat_natCast]
  simp

/-- The plan's J2 statement (ℝ-valued form). -/
theorem divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r) :
    (MeromorphicOn.divisor riemannZeta (closedBall c r) ρ : ℝ) = (zeta_order ρ : ℝ) := by
  rw [divisor_riemannZeta_eq_int h1 hρ]
  push_cast
  rfl

/-- A finite set of points of the ball contributes at most the full divisor sum
(this is the form J4 consumes: `S ⊆ ball`, no support bookkeeping needed). -/
theorem sum_zeta_order_le_finsum_divisor {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ closedBall c r) :
    ∑ ρ ∈ S, (zeta_order ρ : ℝ)
      ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) := by
  set D := MeromorphicOn.divisor riemannZeta (closedBall c r) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  have hnn : ∀ u, (0:ℝ) ≤ (D u : ℝ) := fun u => by
    have h0 : (0:ℤ) ≤ D u := by
      simpa using
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg (Zeta23.RvM.analyticOnNhd_riemannZeta h1) u
    exact_mod_cast h0
  have hsupp : Function.support (fun u => (D u : ℝ)) ⊆ ↑(S ∪ hfin.toFinset) := by
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Finset.coe_union, Finite.coe_toFinset, mem_union, Function.mem_support]
    exact Or.inr (fun h => hu (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc ∑ ρ ∈ S, (zeta_order ρ : ℝ) = ∑ ρ ∈ S, (D ρ : ℝ) :=
        Finset.sum_congr rfl fun ρ hρ => (divisor_riemannZeta_eq h1 (hS ρ hρ)).symm
    _ ≤ ∑ ρ ∈ S ∪ hfin.toFinset, (D ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun u _ _ => hnn u

/-- The divisor sum over a ball in `Re s > 0`, `s ≠ 1` is the multiplicity-weighted count of the
nontrivial zeros in the ball (zeros with `Re ≥ 1` do not exist). -/
theorem finsum_divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r)
    (hre : ∀ s ∈ closedBall c r, 0 < s.re) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)
      = ∑ᶠ ρ ∈ ZetaZeros ∩ closedBall c r, (zeta_order ρ : ℝ) := by
  rw [finsum_mem_def]
  congr 1
  ext u
  by_cases hu : u ∈ closedBall c r
  · rw [divisor_riemannZeta_eq h1 hu]
    by_cases hz : riemannZeta u = 0
    · have hmem : u ∈ ZetaZeros ∩ closedBall c r := by
        refine ⟨⟨hz, hre u hu, ?_⟩, hu⟩
        by_contra hlt
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hlt) hz
      rw [indicator_of_mem hmem]
    · have hmem : u ∉ ZetaZeros ∩ closedBall c r := fun h => hz h.1.1
      rw [indicator_of_notMem hmem, zeta_order_eq_zero_of_ne_zero (fun h => h1 (h ▸ hu)) hz]
      simp
  · have hmem : u ∉ ZetaZeros ∩ closedBall c r := fun h => hu h.2
    rw [indicator_of_notMem hmem, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
    simp

/-- Same, with the zeros indexed by a `zerosIn` window containing the ball's ordinates. -/
theorem finsum_divisor_riemannZeta_eq_zerosIn {c : ℂ} {r a b : ℝ}
    (h1 : (1 : ℂ) ∉ closedBall c r) (hre : ∀ s ∈ closedBall c r, 0 < s.re)
    (him : ∀ s ∈ closedBall c r, a < s.im ∧ s.im ≤ b) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)
      = ∑ᶠ ρ ∈ MNF.RH.zerosIn a b ∩ closedBall c r, (zeta_order ρ : ℝ) := by
  rw [finsum_divisor_riemannZeta_eq h1 hre]
  refine finsum_mem_congr ?_ (fun _ _ => rfl)
  ext ρ
  constructor
  · rintro ⟨hz, hρ⟩; exact ⟨⟨hz, him ρ hρ⟩, hρ⟩
  · rintro ⟨⟨hz, _⟩, hρ⟩; exact ⟨hz, hρ⟩

/-! ## J3 — geometry constants -/

/-- outer radius, inner radius, half-window; valid for 1/2 < σ₁ < 1/2 + δ, δ ≤ 1/2 -/
noncomputable def Rout (σ₁ : ℝ) : ℝ := 2 - σ₁
noncomputable def rin (σ₁ δ : ℝ) : ℝ := (Rout σ₁ + (3 / 2 - δ)) / 2
noncomputable def hwin (σ₁ δ : ℝ) : ℝ := Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2

/-- Membership in a closed ball of ℂ, in coordinates. -/
theorem mem_closedBall_iff_sq {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    z ∈ closedBall c r ↔ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 ≤ r ^ 2 := by
  rw [mem_closedBall, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_le_left hr]
  simp [sub_re, sub_im]

/-- Coordinate bounds from membership in a closed ball. -/
theorem abs_re_im_sub_le_of_mem_closedBall {c z : ℂ} {r : ℝ} (hz : z ∈ closedBall c r) :
    |z.re - c.re| ≤ r ∧ |z.im - c.im| ≤ r := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h1 : |z.re - c.re| ≤ ‖z - c‖ := by simpa using Complex.abs_re_le_norm (z - c)
  have h2 : |z.im - c.im| ≤ ‖z - c‖ := by simpa using Complex.abs_im_le_norm (z - c)
  exact ⟨h1.trans hz, h2.trans hz⟩

/-- Coordinate bounds for the discs centred `2 + t*I`. -/
theorem bounds_of_mem_closedBall_two {t R : ℝ} {s : ℂ} (hs : s ∈ closedBall (2 + t * I) R) :
    2 - R ≤ s.re ∧ s.re ≤ 2 + R ∧ t - R ≤ s.im ∧ s.im ≤ t + R := by
  obtain ⟨h1, h2⟩ := abs_re_im_sub_le_of_mem_closedBall hs
  simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, im_ofNat, mul_im, zero_add] at h1 h2
  rw [abs_le] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The pole is outside every disc centred `2 + t*I` of radius `R < t`. -/
theorem one_notMem_closedBall_two {t R : ℝ} (hRt : R < t) :
    (1 : ℂ) ∉ closedBall (2 + t * I) R := by
  intro h
  have := (bounds_of_mem_closedBall_two h).2.2.1
  simp at this
  linarith

/-- `closedBall (2 + t*I) (Rout σ₁) ⊆ {s | σ₁ ≤ s.re}`. -/
theorem re_ge_of_mem_closedBall_Rout {σ₁ t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + t * I) (Rout σ₁)) : σ₁ ≤ s.re := by
  have := (bounds_of_mem_closedBall_two hs).1
  unfold Rout at this
  linarith

/-- The outer disc for `t ≥ 3`, `1/2 < σ₁`: contained in `{Re s ≥ σ₁} ∩ {s ≠ 1}`, and avoids 1. -/
theorem outer_disc_facts {σ₁ t : ℝ} (h1 : 1 / 2 < σ₁) (ht : 3 ≤ t) :
    (1 : ℂ) ∉ closedBall (2 + t * I) (Rout σ₁) ∧
    closedBall (2 + t * I) (Rout σ₁) ⊆ {s : ℂ | σ₁ ≤ s.re ∧ s ≠ 1} := by
  have hR : Rout σ₁ < 3 / 2 := by unfold Rout; linarith
  have hnot : (1 : ℂ) ∉ closedBall (2 + t * I) (Rout σ₁) :=
    one_notMem_closedBall_two (by linarith)
  exact ⟨hnot, fun s hs => ⟨re_ge_of_mem_closedBall_Rout hs, fun h => hnot (h ▸ hs)⟩⟩

/-- The plan's J3 statement. -/
theorem geom_facts {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧
    ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ →
      ρ ∈ closedBall (2 + t * I) (rin σ₁ δ) := by
  set A : ℝ := 3 / 2 - δ with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hrA : A < rin σ₁ δ := by unfold rin Rout; rw [hA]; linarith
  have hrin_pos : 0 < rin σ₁ δ := by linarith
  have hrin_lt : rin σ₁ δ < Rout σ₁ := by unfold rin Rout; linarith
  have hRout : Rout σ₁ < 3 / 2 := by unfold Rout; linarith
  have hsq_pos : 0 < rin σ₁ δ ^ 2 - A ^ 2 := by nlinarith
  have hhwin_sq : hwin σ₁ δ ^ 2 = (rin σ₁ δ ^ 2 - A ^ 2) / 4 := by
    unfold hwin
    rw [div_pow, Real.sq_sqrt hsq_pos.le]
    norm_num
  have hwin_pos : 0 < hwin σ₁ δ := by
    unfold hwin
    exact div_pos (Real.sqrt_pos.2 hsq_pos) (by norm_num)
  have hwin_le : hwin σ₁ δ ≤ 1 := by
    unfold hwin
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), one_mul, Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ⟨hrin_pos, hrin_lt, hRout, hwin_pos, hwin_le, fun ρ hρ1 hρ2 t ht => ?_⟩
  rw [mem_closedBall_iff_sq hrin_pos.le]
  simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, im_ofNat, mul_im, zero_add]
  have hre_sq : (ρ.re - 2) ^ 2 ≤ A ^ 2 := sq_le_sq' (by rw [hA]; linarith) (by linarith)
  have him_sq : (ρ.im - t) ^ 2 ≤ hwin σ₁ δ ^ 2 := by
    have : (ρ.im - t) ^ 2 = |t - ρ.im| ^ 2 := by rw [sq_abs]; ring
    rw [this]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [hhwin_sq] at him_sq
  linarith

end Zeta23.BL

#print axioms Zeta23.BL.NRight_eq_zero_of_half_le
#print axioms Zeta23.BL.NRight_sub_eq
#print axioms Zeta23.BL.NRight_mono
#print axioms Zeta23.BL.divisor_riemannZeta_eq
#print axioms Zeta23.BL.sum_zeta_order_le_finsum_divisor
#print axioms Zeta23.BL.finsum_divisor_riemannZeta_eq_zerosIn
#print axioms Zeta23.BL.outer_disc_facts
#print axioms Zeta23.BL.geom_facts
