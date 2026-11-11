/- LOCAL ONLY. Bohr–Landau scoping: MNF's statement, the reduction to the right half-strip
(functional-equation reflection, multiplicity-weighted), and the analytic inputs as named sorries. -/
import MNF.RH.GapDensity
import Zeta23.Statement.SeamClosed
import Mathlib.Analysis.Complex.JensenFormula

open Set Complex

namespace Zeta23.BL
open MNF.RH

/-- MNF's statement, verbatim (restated for reference): `MNF.RH.BohrLandau`. -/
example : MNF.RH.BohrLandau ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    (NOff δ 0 T : ℝ) ≤ C * T := Iff.rfl

noncomputable def NRight (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ
noncomputable def NLeft (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ 1 / 2 - ρ.re}, zeta_order ρ

/-- the multiplicity convention: off-line count splits exactly into the two halves (δ > 0). -/
theorem NOff_eq_right_add_left {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    NOff δ 0 T = NRight δ T + NLeft δ T := by
  have hf := MNF.RH.zerosIn_finite 0 T
  unfold NOff NRight NLeft
  have hd : Disjoint (MNF.RH.zerosIn 0 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2})
      (MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ 1 / 2 - ρ.re}) :=
    disjoint_left.2 fun x h1 h2 => by
      have a : δ ≤ x.re - 1/2 := h1.2; have b : δ ≤ 1/2 - x.re := h2.2; linarith
  have hs : {ρ : ℂ | δ ≤ |ρ.re - 1 / 2|} = {ρ | δ ≤ ρ.re - 1 / 2} ∪ {ρ | δ ≤ 1 / 2 - ρ.re} := by
    ext ρ; simp only [mem_union, le_abs', mem_ofPred_eq]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  rw [← finsum_mem_union hd (hf.subset inter_subset_left) (hf.subset inter_subset_left),
    ← inter_union_distrib_left, hs]

/-- reduction to the right half: ρ ↦ 1 − ρ̄ (zeta23's `reflect`) preserves Im, multiplicity. -/
theorem NLeft_eq_NRight (δ T : ℝ) : NLeft δ T = NRight δ T := by
  unfold NLeft NRight
  refine finsum_mem_eq_of_bijOn reflect ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · rintro ρ ⟨⟨hz, h1, h2⟩, hδ⟩
      have hm := zetaZeroConfig.reflect_mem ρ hz
      refine ⟨⟨hm, ?_, ?_⟩, ?_⟩ <;> simp_all [reflect] <;> linarith
    · intro x _ y _ h; simpa using congrArg (starRingEnd ℂ) (by simpa [reflect] using h : (starRingEnd ℂ) x = (starRingEnd ℂ) y)
    · rintro σ ⟨⟨hz, h1, h2⟩, hδ⟩
      refine ⟨reflect σ, ⟨⟨zetaZeroConfig.reflect_mem σ hz, ?_, ?_⟩, ?_⟩, ?_⟩
      · simpa [reflect] using h1
      · simpa [reflect] using h2
      · have : δ ≤ σ.re - 1/2 := hδ; simp [reflect]; linarith
      · simp [reflect]
  · rintro ρ ⟨⟨hz, _, _⟩, _⟩
    exact (zetaZeroConfig.mult_reflect ρ hz).symm

/-- Bohr–Landau for the right half-strip only. -/
def RightHalfBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T

/-- Sorry-free reduction: right-half bound ⇒ MNF's BohrLandau. -/
theorem bohrLandau_of_right (h : RightHalfBound) : MNF.RH.BohrLandau := by
  intro δ hδ
  obtain ⟨C, hC⟩ := h δ hδ
  refine ⟨2 * C, fun T hT => ?_⟩
  rw [NOff_eq_right_add_left hδ, NLeft_eq_NRight]; push_cast; linarith [hC T hT]

/-! ### The analytic inputs (classical proof, Titchmarsh §9.15). -/

/-- [MISSING 1, hardest] mean square of ζ on vertical lines right of 1/2 (Hardy–Littlewood). -/
def ZetaMeanSquare : Prop := ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
  ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T

theorem norm_zeta_le_tsum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta (σ + t * I)‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ σ := by
  have hre : 1 < (σ + t * I : ℂ).re := by simpa using hσ
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) := Real.summable_one_div_nat_rpow.2 hσ
  have hn : ∀ n : ℕ, ‖1 / (n : ℂ) ^ (σ + t * I : ℂ)‖ = 1 / (n : ℝ) ^ σ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (σ + t * I : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      simp [Complex.zero_cpow h0, Real.zero_rpow (by linarith : σ ≠ 0)]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]; simp
  calc _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ (σ + t * I : ℂ)‖ :=
        norm_tsum_le_tsum_norm (by simp_rw [hn]; exact hs)
    _ = _ := by simp_rw [hn]

theorem meanSquare_gt_one {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ σ
  refine ⟨Z ^ 2, fun T hT => ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := Z ^ 2)
    (f := fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_zeta_le_tsum hσ t) 2)
  rw [sub_zero, abs_of_nonneg (by linarith)] at h
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ h)

/-- [MISSING 1a] the critical-strip part 1/2 < σ ≤ 1 (approximate functional equation +
Dirichlet-polynomial mean value theorem). -/
theorem meanSquare_strip {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  sorry

theorem zetaMeanSquare : ZetaMeanSquare := fun σ hσ =>
  if h : 1 < σ then meanSquare_gt_one h else meanSquare_strip hσ (not_lt.1 h)

/-- [MISSING 2] Littlewood's lemma on rectangles + Jensen/concavity of log, applied to ζ (or a
mollified 1 − (1 − ζ M)²), turning the mean square into a count of zeros with Re ρ ≥ 1/2 + δ. -/
theorem rightHalfBound_of_meanSquare (h : ZetaMeanSquare) : RightHalfBound := by
  sorry

theorem bohrLandau : MNF.RH.BohrLandau :=
  bohrLandau_of_right (rightHalfBound_of_meanSquare zetaMeanSquare)

end Zeta23.BL
#print axioms Zeta23.BL.NLeft_eq_NRight
#print axioms Zeta23.BL.bohrLandau_of_right
#print axioms Zeta23.BL.bohrLandau
#print axioms Zeta23.BL.meanSquare_gt_one
