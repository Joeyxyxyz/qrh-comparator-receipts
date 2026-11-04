/- LOCAL ONLY. MNF.RH (v3 GapDensity) on the zeta23 tree: discharge NcountSuperlinear. -/
import Zeta23.Superlinear
import Zeta23.OffLine
import Zeta23.BohrLandau

namespace Zeta23.Bridge

theorem Ncount_eq (T₁ T₂ : ℝ) : MNF.RH.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := rfl

theorem ncountSuperlinear_iff : MNF.RH.NcountSuperlinear ↔ Zeta23.NcountSuperlinear := Iff.rfl

theorem mnf_ncountSuperlinear : MNF.RH.NcountSuperlinear := Zeta23.ncountSuperlinear

/-- the off-line bound in MNF vocabulary (off-line = Re ≠ 1/2, multiplicity-weighted). -/
theorem mnf_offLine_le_one_third : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ((∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | ρ.re ≠ 1 / 2}, MNF.RH.zeta_order ρ : ℕ) : ℝ)
      ≤ (1 / 3 + ε) * MNF.RH.Ncount 0 T :=
  Zeta23.offLine_le_one_third

/-- **Final**: a zero-free strip 1/2 < Re s < 1/2 + Δ next to the line, plus Bohr–Landau, gives
density one of the zeros (with multiplicity) on the critical line. `NcountSuperlinear` is gone. -/
theorem on_line_density_one_of_gap' (hBL : MNF.RH.BohrLandau) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : MNF.RH.SpectralGapHyp Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (MNF.RH.Ncount 0 T : ℝ) ≤ MNF.RH.N0 0 T :=
  MNF.RH.on_line_density_one_of_gap hBL mnf_ncountSuperlinear hΔ hgap

/-- same, with Bohr–Landau reduced to the right half-strip bound (sorry-free reduction). -/
theorem on_line_density_one_of_gap_right (hR : Zeta23.BL.RightHalfBound) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : MNF.RH.SpectralGapHyp Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (MNF.RH.Ncount 0 T : ℝ) ≤ MNF.RH.N0 0 T :=
  on_line_density_one_of_gap' (Zeta23.BL.bohrLandau_of_right hR) hΔ hgap

/-- only the strip remains; uses the two sorried analytic lemmas of BohrLandau.lean. -/
theorem on_line_density_one_of_gap_strip_only {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : MNF.RH.SpectralGapHyp Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (MNF.RH.Ncount 0 T : ℝ) ≤ MNF.RH.N0 0 T :=
  on_line_density_one_of_gap' Zeta23.BL.bohrLandau hΔ hgap

end Zeta23.Bridge
#print axioms Zeta23.Bridge.mnf_ncountSuperlinear
#print axioms Zeta23.Bridge.mnf_offLine_le_one_third
#print axioms Zeta23.Bridge.on_line_density_one_of_gap'
#print axioms Zeta23.Bridge.on_line_density_one_of_gap_right
#print axioms Zeta23.Bridge.on_line_density_one_of_gap_strip_only
