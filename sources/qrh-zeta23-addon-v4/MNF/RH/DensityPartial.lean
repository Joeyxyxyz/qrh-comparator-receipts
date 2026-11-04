/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — BOHR–LANDAU FOR δ > 1/6, AND WHAT IT GIVES THE DENSITY FIELD
(MNF/RH/DensityPartial.lean)
[PROVED | this tree] + [BOOKKEEPING]
Register: `[PROVED | this tree]` marks a theorem delegated by unfolding to
Zeta23/BL/BohrLandauPartial.lean, which is proved on this tree (not in upstream zeta23) from
Mathlib and the tree's sorry-free files; axioms in `MNF_AuditDensity.lean`.
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree, on top of MNF/RH/Density.lean and
Zeta23/BL/BohrLandauPartial.lean (145 declarations, no sorry; the route of
BOHR_LANDAU_PLAN.md, a planning note outside this tree: the tree's approximate formula ζ = ζ₀ N with its naive error bound, the
Dirichlet-polynomial mean value with the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen`,
Jensen's formula on discs centred 2 + it averaged in t, and Fubini).

What is proved there with no hypothesis beyond Mathlib (axioms audited in `MNF_AuditDensity.lean`),
except that the second bullet is an implication whose hypothesis the first bullet discharges
for σ₁ ≥ 2/3:
  * the mean square ∫₁ᵀ ‖ζ(σ+it)‖² dt is ≤ C(σ₁)·T for all T ≥ 1, uniformly in σ ≥ σ₁, for every
    2/3 ≤ σ₁ < 1 (`Zeta23.BL.M3.meanSquareUnif_explicit`, explicit constant), and the instances
    2/3 ≤ σ ≤ 1 of the sorried statement `meanSquare_strip` of Zeta23/BohrLandau.lean are proved
    (`Zeta23.BL.M45.meanSquare_strip_of`; the sorry itself, which also covers 1/2 < σ < 2/3,
    stays; at σ = 1 the ∫₀ᵀ form holds only because ‖ζ(1+it)‖² is not integrable at t = 0 and Mathlib's
    Bochner integral of a non-integrable function is 0 — the honest statement there is
    `meanSquare_one_from_one` on [1, T]);
  * for 1/2 < σ₁ < 1, from a uniform mean square ∫₁ᵀ on Re s ≥ σ₁ (`MeanSquareUnifFrom σ₁`), the
    right-half count NRight δ T is O(T) for every δ > σ₁ − 1/2 (`Zeta23.BL.rightHalf_of_meanSquareUnif`);
  * hence **for every δ > 1/6 the nontrivial zeros ρ with 0 < Im ρ ≤ T and Re ρ − 1/2 ≥ δ, counted
    with multiplicity, number at most C_δ·T for all T ≥ 2** (`Zeta23.BL.rightHalf_gt_sixth`), and
    by the reflection ρ ↦ 1 − ρ̄ **the same for |Re ρ − 1/2| ≥ δ, i.e. N_off(δ; 0,T) ≤ C_δ·T**
    (`Zeta23.BL.bohrLandau_gt_sixth`).

This file restates the last two facts in MNF's vocabulary (`rightHalf_gt_sixth`,
`bohrLandau_gt_sixth`) and draws the density consequences: for every δ > 1/6, all but a
vanishing (multiplicity-weighted) proportion of the zeros with 0 < Im ρ ≤ T lie within δ of the
line (`reservoirDensity_gt_sixth`, `near_line_density_gt_sixth`, `nullified_density_gt_sixth`;
T₀ depends on δ and ε), with no hypothesis beyond δ > 1/6; and a gap at any Δ > 1/6 gives density
one ON the line with no further hypothesis (`onLineDensityOne_of_gap_gt_sixth`).

What this is and is not.  Bohr–Landau (1914) gives the bound for every δ > 0; what is formalized
here is the part δ > 1/6, because the approximate formula available on the tree carries the naive
error term ‖s‖N^{−σ}/σ: with that error term and the Dirichlet-polynomial mean value, the
exponent count (N = T^a needs 1/σ ≤ a ≤ 1/(2 − 2σ), a window that is non-empty exactly when
σ ≥ 2/3; the proof takes a = 3/2) closes the mean square for σ ≥ 2/3 and not below — a limitation
of this route, not a theorem about ζ (classically the mean square is O(T) for every σ > 1/2).
Nothing here says anything about zeros with 1/3 ≤ Re ρ ≤ 2/3 beyond what Density.lean already
says (a zero on Re ρ = 2/3 is at distance exactly 1/6 and is counted by no δ > 1/6).  Nothing here touches
`SpectralGapHyp`: a gap at Δ ∈ (1/6, 1/2) is a zero-free strip of width > 1/6 next to the line,
which is not known; for Δ ≥ 1/2 it is RH.  Nothing here uses the 7/8 theorem.  The conclusion
`OnLineDensityOne` follows from RH and is not known to imply it.
-/
import MNF.RH.Density
import Zeta23.BL.BohrLandauPartial

namespace MNF.RH

open Complex Set

/-- [PROVED | this tree] Bohr–Landau restricted to δ > 1/6, right-half form: for every δ > 1/6
there is C with NRight δ T ≤ C·T for all T ≥ 2: the nontrivial zeros with 0 < Im ρ ≤ T and
Re ρ − 1/2 ≥ δ, counted with multiplicity, number O(T).  Delegated to `Zeta23.BL.rightHalf_gt_sixth`
(same definition body for `NRight`). -/
theorem rightHalf_gt_sixth : ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T :=
  Zeta23.BL.rightHalf_gt_sixth

/-- [PROVED | this tree] Bohr–Landau restricted to δ > 1/6: for every δ > 1/6 there is C with
NOff δ 0 T ≤ C·T for all T ≥ 2: the nontrivial zeros with 0 < Im ρ ≤ T at distance ≥ δ from the
line, counted with multiplicity, number O(T) — `MNF.RH.BohrLandau` with `0 < δ` replaced by
`1/6 < δ`.  Delegated to `Zeta23.BL.bohrLandau_gt_sixth`; `NOff` is
MNF's own definition. -/
theorem bohrLandau_gt_sixth : ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T :=
  Zeta23.BL.bohrLandau_gt_sixth

/-- A linear bound on the off-line count at one δ gives a vanishing proportion at that δ (the
proof of `reservoirDensityOne_of_bohrLandau`, at a single δ). -/
theorem reservoirDensity_of_linear_bound {δ : ℝ}
    (hb : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T := by
  intro ε hε
  obtain ⟨C, hC⟩ := hb
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

/-- **Unconditional** (the only hypothesis is the range δ > 1/6): for every δ > 1/6, all but a vanishing proportion of the zeros lie within
δ of the line. -/
theorem reservoirDensity_gt_sixth {δ : ℝ} (hδ : 1 / 6 < δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T :=
  reservoirDensity_of_linear_bound (bohrLandau_gt_sixth δ hδ)

/-- The same in the near-count form: (1 − ε)·N(0,T) ≤ N_near(δ; 0,T) eventually, δ > 1/6. -/
theorem near_line_density_gt_sixth {δ : ℝ} (hδ : 1 / 6 < δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ NNear δ 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := reservoirDensity_gt_sixth hδ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hsplit : (Ncount 0 T : ℝ) = NNear δ 0 T + NOff δ 0 T := by
    exact_mod_cast Ncount_eq_near_add_off δ 0 T
  have h6 : (1 - ε) * (Ncount 0 T : ℝ) = Ncount 0 T - ε * Ncount 0 T := by ring
  linarith [h T hT]

/-- The same in the nullification form: at every threshold Δ > 1/6, the zeros whose shifted real
part N(Δ,·) sends to 0 have density one, unconditionally. -/
theorem nullified_density_gt_sixth {Δ : ℝ} (hΔ : 1 / 6 < Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤
      ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | nullify Δ (ρ.re - 1 / 2) = 0}, zeta_order ρ := by
  intro ε hε
  obtain ⟨T₀, h⟩ := near_line_density_gt_sixth hΔ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [← NNear_eq_nullified_count (by linarith : (0 : ℝ) < Δ) 0 T]
  exact h T hT

/-- **A gap at any Δ > 1/6 gives density one on the line, with no other hypothesis.**  (For
Δ ≥ 1/2 the gap is RH; for 1/6 < Δ < 1/2 it is an unknown zero-free strip of width > 1/6.) -/
theorem onLineDensityOne_of_gap_gt_sixth {Δ : ℝ} (hΔ : 1 / 6 < Δ) (hgap : SpectralGapHyp Δ) :
    OnLineDensityOne := by
  intro ε hε
  obtain ⟨T₀, h⟩ := near_line_density_gt_sixth hΔ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [← NNear_eq_N0_of_gap (by linarith : (0 : ℝ) < Δ) hgap 0 T]
  exact h T hT

end MNF.RH
