/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE DENSITY FIELD  (MNF/RH/Density.lean)
[RESTATEMENT | zeta23] + [BOOKKEEPING]  —  for-every-δ density versus density on the line itself
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e), on top of
MNF/RH/GapDensity.lean (ported unchanged from add-on v3) and the three LOCAL-ONLY files
Zeta23/Superlinear.lean, Zeta23/OffLine.lean, Zeta23/BohrLandau.lean.

What this file settles, in MNF's own vocabulary:

  §1  The reservoir count `NNear δ` (zeros with |Re ρ − 1/2| < δ, with multiplicity) is exactly
      the multiplicity-weighted count of zeros whose shifted real part is NULLIFIED at
      threshold δ (`NNear_eq_nullified_count`): N_near(δ) = Σ_{ρ : nullify δ (Re ρ − 1/2) = 0}
      ord(ρ).  Every window splits
      as N = N_near(δ) + N_off(δ) for every δ (`Ncount_eq_near_add_off`), with no hypothesis.
  §2  `NcountSuperlinear` is a theorem of this tree (`ncountSuperlinear`), delegated to
      `Zeta23.ncountSuperlinear`, which zeta23 proves from its unconditional Riemann–von
      Mangoldt formula `riemannVonMangoldt_zeta` (dyadic form: |N(T,2T) − (T/2π)(log(T/2π)
      + 2 log 2 − 1)| ≤ C log T for T ≥ T₀; only the main term is used, and it gives
      N(T,2T) ≥ cT for every c eventually).  No theorem in this file takes it as a hypothesis;
      GapDensity.lean's `on_line_density_one_of_gap` still carries it as a binder, and
      `onLineDensityOne_of_gap` below is that statement with the binder discharged.
  §3  Unconditionally, off-line zeros (by any margin) carry at most 1/3 + ε of N(0,T):
      zeta23's Theorem B in MNF vocabulary (`offLine_le_one_third`, `NOff_le_one_third`).
  §4  The two density notions.
      `ReservoirDensityOne` (nicknamed "st()-density one"): for every fixed δ > 0,
        N_off(δ; 0,T) ≤ ε·N(0,T) eventually (the threshold T₀ depends on δ) — equivalently, the
        zeros nullified at δ have density one.  The nickname is the standard-words reading of
        "infinitesimal": nullified at every fixed threshold; no nonstandard object is formalized
        and the name carries no content beyond the definition.  Bohr–Landau gives it with no
        other hypothesis (`reservoirDensityOne_of_bohrLandau`; `NcountSuperlinear` is §2).
      `OnLineDensityOne` (density one on the line itself): (1 − ε)·N(0,T) ≤ N₀(0,T) eventually.
        In this file the gap is used once, through `NNear_eq_N0_of_gap`: under a gap at Δ the
        Δ-reservoir is empty, so the δ = Δ instance of `ReservoirDensityOne` is
        `OnLineDensityOne` (`onLineDensityOne_of_reservoir_of_gap`); the other instances of δ
        are not used.  The hypothesis itself is much stronger than this use
        (`spectralGapHyp_iff_zeroFree_strip`).
  §5  Bohr–Landau is reduced, sorry-free, to its right half-strip form (`bohrLandau_of_right`,
      by the reflection ρ ↦ 1 − ρ̄, delegated to Zeta23.BL): a symmetry step; all analytic content
      of Bohr–Landau remains in `RightHalfBound`.  What is not yet formalized is `RightHalfBound`
      itself (classical: Bohr–Landau 1914, Titchmarsh §9.15; a theorem of the literature, not an
      open problem): the mean square of ζ right of the line and a Jensen/Littlewood count, named
      in Zeta23/BohrLandau.lean as two `sorry` lemmas and NOT used by anything in this file.

What this file does NOT do.  Nothing here proves, weakens or replaces `SpectralGapHyp`; it
appears only as an explicit binder: for Δ ≥ 1/2 it is RH (`riemannHypothesis_iff_gap_half`),
and for 0 < Δ < 1/2 it is an unknown zero-free strip.  Nothing here uses the 7/8 theorem.
`OnLineDensityOne` is implied by RH and is not known to imply it; here it is proved only under
Bohr–Landau (or its right-half form) together with a gap, never under the gap alone.  No new
analytic estimate about ζ is proved here; §3 and §2 are zeta23's theorems under a change of
names the kernel verifies by unfolding.
-/
import MNF.RH.GapDensity
import Zeta23.Superlinear
import Zeta23.OffLine
import Zeta23.BohrLandau

namespace MNF.RH

open Complex Set
open scoped BigOperators

/-! ### §1 The reservoir count and its nullification reading -/

/-- N_near(δ; T₁,T₂): the nontrivial zeros with T₁ < Im ρ ≤ T₂ and |Re ρ − 1/2| < δ (on the
line or in the δ-reservoir), counted WITH multiplicity. -/
noncomputable def NNear (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | |ρ.re - 1 / 2| < δ}, zeta_order ρ

/-- N_offline(T₁,T₂): the nontrivial zeros with T₁ < Im ρ ≤ T₂ and Re ρ ≠ 1/2 (off the line by
any margin), counted WITH multiplicity. -/
noncomputable def NOffLine (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}, zeta_order ρ

/-- Right-half count (zeros with Re ρ ≥ 1/2 + δ), with multiplicity; the body of
`Zeta23.BL.NRight`. -/
noncomputable def NRight (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ

/-- Left-half count (zeros with Re ρ ≤ 1/2 − δ), with multiplicity; the body of
`Zeta23.BL.NLeft`. -/
noncomputable def NLeft (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | δ ≤ 1 / 2 - ρ.re}, zeta_order ρ

/-- Bohr–Landau for the right half-strip only: the body of `Zeta23.BL.RightHalfBound`. -/
def RightHalfBound : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T

/-- At a positive threshold, MNF's `nullify` sends x to 0 exactly when |x| < Δ. -/
theorem nullify_eq_zero_iff {Δ : ℝ} (hΔ : 0 < Δ) (x : ℝ) : nullify Δ x = 0 ↔ |x| < Δ := by
  unfold nullify
  by_cases h : Δ ≤ |x|
  · rw [if_pos h]
    constructor
    · intro h0
      rw [h0, abs_zero] at h
      exact absurd h (not_le.mpr hΔ)
    · intro hlt
      exact absurd h (not_le.mpr hlt)
  · rw [if_neg h]
    exact ⟨fun _ => not_le.mp h, fun _ => rfl⟩

/-- **The reservoir count is the nullified count.**  N_near(Δ) counts exactly the zeros whose
shifted real part Re ρ − 1/2 is sent to 0 by N(Δ, ·). -/
theorem NNear_eq_nullified_count {Δ : ℝ} (hΔ : 0 < Δ) (T₁ T₂ : ℝ) :
    NNear Δ T₁ T₂ = ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | nullify Δ (ρ.re - 1 / 2) = 0}, zeta_order ρ := by
  have hset : {ρ : ℂ | |ρ.re - 1 / 2| < Δ} = {ρ | nullify Δ (ρ.re - 1 / 2) = 0} := by
    ext ρ
    simp only [mem_setOf_eq, nullify_eq_zero_iff hΔ]
  unfold NNear
  rw [hset]

/-- Every window splits as near + off, at every δ, with no hypothesis. -/
theorem Ncount_eq_near_add_off (δ T₁ T₂ : ℝ) : Ncount T₁ T₂ = NNear δ T₁ T₂ + NOff δ T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have hunion : zerosIn T₁ T₂ =
      (zerosIn T₁ T₂ ∩ {ρ | |ρ.re - 1 / 2| < δ}) ∪ (zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}) := by
    ext ρ
    constructor
    · intro hρ
      rcases lt_or_ge |ρ.re - 1 / 2| δ with h | h
      · exact Or.inl ⟨hρ, h⟩
      · exact Or.inr ⟨hρ, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint (zerosIn T₁ T₂ ∩ {ρ | |ρ.re - 1 / 2| < δ})
      (zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}) := by
    rw [disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    have h1' : |ρ.re - 1 / 2| < δ := h1
    have h2' : δ ≤ |ρ.re - 1 / 2| := h2
    linarith
  have hsum := finsum_mem_union hdisj (hfin.subset inter_subset_left)
    (hfin.subset inter_subset_left) (f := zeta_order)
  rw [← hunion] at hsum
  exact hsum

/-- The on-line count is at most the near count, at every positive δ. -/
theorem N0_le_NNear {δ : ℝ} (hδ : 0 < δ) (T₁ T₂ : ℝ) : N0 T₁ T₂ ≤ NNear δ T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have h1 : (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).Finite := hfin.subset inter_subset_left
  have h2 : (zerosIn T₁ T₂ ∩ {ρ | |ρ.re - 1 / 2| < δ}).Finite := hfin.subset inter_subset_left
  unfold N0 NNear
  rw [finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finite.toFinset_subset_toFinset.2 ?_)
    (fun _ _ _ => Nat.zero_le _)
  rintro ρ ⟨hρ, h⟩
  refine ⟨hρ, ?_⟩
  have h' : ρ.re = 1 / 2 := h
  show |ρ.re - 1 / 2| < δ
  rw [h', sub_self, abs_zero]
  exact hδ

/-- Off by at least δ > 0 is off. -/
theorem NOff_le_NOffLine {δ : ℝ} (hδ : 0 < δ) (T₁ T₂ : ℝ) : NOff δ T₁ T₂ ≤ NOffLine T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have h1 : (zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}).Finite := hfin.subset inter_subset_left
  have h2 : (zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}).Finite := hfin.subset inter_subset_left
  unfold NOff NOffLine
  rw [finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finite.toFinset_subset_toFinset.2 ?_)
    (fun _ _ _ => Nat.zero_le _)
  rintro ρ ⟨hρ, h⟩
  refine ⟨hρ, ?_⟩
  have h' : δ ≤ |ρ.re - 1 / 2| := h
  show ρ.re ≠ 1 / 2
  intro heq
  rw [heq, sub_self, abs_zero] at h'
  linarith

/-- **The one use made of the gap here**: under a gap at Δ > 0 the Δ-reservoir is empty, so
the near count at Δ is the on-line count. -/
theorem NNear_eq_N0_of_gap {Δ : ℝ} (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) (T₁ T₂ : ℝ) :
    NNear Δ T₁ T₂ = N0 T₁ T₂ := by
  have h1 := gap_forces_NOff_eq hΔ hgap T₁ T₂
  have h2 := Ncount_eq_near_add_off Δ T₁ T₂
  omega

/-! ### §2 `NcountSuperlinear` is a theorem of this tree -/

/-- [RESTATEMENT | zeta23] N(T)/T → ∞: `MNF.RH.NcountSuperlinear` holds.  Delegated to
`Zeta23.ncountSuperlinear` (Zeta23/Superlinear.lean), which zeta23 derives from its
unconditional Riemann–von Mangoldt formula `riemannVonMangoldt_zeta`; MNF's `Ncount` unfolds
to zeta23's, so the kernel accepts the delegation by unfolding. -/
theorem ncountSuperlinear : NcountSuperlinear := Zeta23.ncountSuperlinear

/-! ### §3 Off-line zeros are at most a third, unconditionally -/

/-- [RESTATEMENT | zeta23] Theorem B (two thirds simple and on the line, with multiplicity on
the left) read as an off-line bound: for every ε > 0 and all large T, the zeros with
Re ρ ≠ 1/2, with multiplicity, number at most (1/3 + ε)·N(0,T).  Delegated to
`Zeta23.offLine_le_one_third`. -/
theorem offLine_le_one_third :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOffLine 0 T : ℝ) ≤ (1 / 3 + ε) * Ncount 0 T :=
  Zeta23.offLine_le_one_third

/-- The same bound for the zeros off by at least δ > 0: an unconditional proportion bound,
N_off(δ; 0,T) ≤ (1/3 + ε)·N(0,T) eventually.  Bohr–Landau's O(T) is o(N(0,T)) and so sharper. -/
theorem NOff_le_one_third {δ : ℝ} (hδ : 0 < δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ (1 / 3 + ε) * Ncount 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := offLine_le_one_third ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (h T hT)⟩
  exact_mod_cast NOff_le_NOffLine hδ 0 T

/-! ### §4 The two density notions -/

/-- **For-every-δ density one** (nickname: st()-density one).  For every fixed δ > 0,
N_off(δ; 0,T) ≤ ε·N(0,T) eventually; T₀ depends on δ.  By `NNear_eq_nullified_count` this
says: at every fixed threshold δ, the zeros nullified by N(δ,·) have density one.  No
nonstandard object is involved. -/
def ReservoirDensityOne : Prop :=
  ∀ δ > 0, ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T

/-- **Density one on the line itself.**  (1 − ε)·N(0,T) ≤ N₀(0,T) eventually. -/
def OnLineDensityOne : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T

/-- **Bohr–Landau gives `ReservoirDensityOne`** with no other hypothesis (the superlinear
growth of N is §2). -/
theorem reservoirDensityOne_of_bohrLandau (hBL : BohrLandau) : ReservoirDensityOne := by
  intro δ hδ ε hε
  obtain ⟨C, hC⟩ := hBL δ hδ
  have hCpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨T₀, hT₀⟩ := ncountSuperlinear (max C 1 / ε) (by positivity)
  refine ⟨max T₀ 2, fun T hT => ?_⟩
  have h1 := hT₀ T (le_trans (le_max_left _ _) hT)
  have h2 := hC T (le_trans (le_max_right _ _) hT)
  have hT2 : (0 : ℝ) ≤ T := by linarith [le_trans (le_max_right _ _) hT]
  have h3 : (NOff δ 0 T : ℝ) ≤ max C 1 * T :=
    le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hT2)
  have h4 : ε * (max C 1 / ε * T) ≤ ε * Ncount 0 T := mul_le_mul_of_nonneg_left h1 hε.le
  have h4' : ε * (max C 1 / ε * T) = max C 1 * T := by field_simp
  linarith

/-- `ReservoirDensityOne` in the near-count form: (1 − ε)·N(0,T) ≤ N_near(δ; 0,T) eventually. -/
theorem near_line_density_one (hR : ReservoirDensityOne) {δ : ℝ} (hδ : 0 < δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ NNear δ 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := hR δ hδ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (Ncount 0 T : ℝ) = NNear δ 0 T + NOff δ 0 T := by
    exact_mod_cast Ncount_eq_near_add_off δ 0 T
  have h6 : (1 - ε) * (Ncount 0 T : ℝ) = Ncount 0 T - ε * Ncount 0 T := by ring
  linarith [h T hT]

/-- `ReservoirDensityOne` in the nullification form: at threshold Δ, the zeros whose shifted real
part N(Δ,·) sends to 0 have density one. -/
theorem nullified_density_one (hR : ReservoirDensityOne) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤
      ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | nullify Δ (ρ.re - 1 / 2) = 0}, zeta_order ρ := by
  intro ε hε
  obtain ⟨T₀, h⟩ := near_line_density_one hR hΔ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [← NNear_eq_nullified_count hΔ 0 T]
  exact h T hT

/-- **Under a gap at Δ, the δ = Δ instance of `ReservoirDensityOne` is `OnLineDensityOne`**
(via `NNear_eq_N0_of_gap`); the other instances of δ are not used. -/
theorem onLineDensityOne_of_reservoir_of_gap (hR : ReservoirDensityOne) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : SpectralGapHyp Δ) : OnLineDensityOne := by
  intro ε hε
  obtain ⟨T₀, h⟩ := near_line_density_one hR hΔ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [← NNear_eq_N0_of_gap hΔ hgap 0 T]
  exact h T hT

/-- v3's `on_line_density_one_of_gap` with `NcountSuperlinear` discharged: Bohr–Landau and a
gap at some Δ > 0 give density one on the line. -/
theorem onLineDensityOne_of_gap (hBL : BohrLandau) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : SpectralGapHyp Δ) : OnLineDensityOne :=
  onLineDensityOne_of_reservoir_of_gap (reservoirDensityOne_of_bohrLandau hBL) hΔ hgap

/-! ### §5 Bohr–Landau reduced to the right half-strip -/

/-- For δ > 0 the off-line count is the sum of the two half-counts (delegated to
`Zeta23.BL.NOff_eq_right_add_left`; same definition bodies). -/
theorem NOff_eq_right_add_left {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    NOff δ 0 T = NRight δ T + NLeft δ T :=
  Zeta23.BL.NOff_eq_right_add_left hδ T

/-- [RESTATEMENT | zeta23] The functional-equation reflection ρ ↦ 1 − ρ̄ preserves the ordinate
and the multiplicity, so the two half-counts agree.  Delegated to `Zeta23.BL.NLeft_eq_NRight`,
whose proof uses zeta23's `zetaZeroConfig.reflect_mem` and `mult_reflect`. -/
theorem NLeft_eq_NRight (δ T : ℝ) : NLeft δ T = NRight δ T :=
  Zeta23.BL.NLeft_eq_NRight δ T

/-- **Sorry-free reduction** by the reflection ρ ↦ 1 − ρ̄ (a symmetry step; the analytic
content stays in `RightHalfBound`): the right-half bound gives Bohr–Landau. -/
theorem bohrLandau_of_right (h : RightHalfBound) : BohrLandau :=
  Zeta23.BL.bohrLandau_of_right h

/-- Density one on the line from the right-half bound and a gap. -/
theorem onLineDensityOne_of_right (h : RightHalfBound) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : SpectralGapHyp Δ) : OnLineDensityOne :=
  onLineDensityOne_of_gap (bohrLandau_of_right h) hΔ hgap

/-- `ReservoirDensityOne` from the right-half bound alone. -/
theorem reservoirDensityOne_of_right (h : RightHalfBound) : ReservoirDensityOne :=
  reservoirDensityOne_of_bohrLandau (bohrLandau_of_right h)

end MNF.RH
