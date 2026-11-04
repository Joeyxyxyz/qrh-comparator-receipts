/-
LOCAL ONLY. N(T)/T → ∞ for the nontrivial zeros of ζ (counted with multiplicity, 0 < Im ρ ≤ T),
derived from zeta23's unconditional `riemannVonMangoldt_zeta`.
-/
import Zeta23.Final

open Filter Topology

namespace Zeta23

/-- MNF.RH's `NcountSuperlinear`, stated over zeta23's `Ncount` (same definition body as
MNF.RH.Counting's `Ncount`). -/
def NcountSuperlinear : Prop := ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ T ≥ T₀, c * T ≤ (Ncount 0 T : ℝ)

theorem ell1_tendsto_atTop : Tendsto ell1 atTop atTop := by
  unfold ell1 l
  have : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ this)

/-- Lower bound on dyadic windows: eventually `c·(2T) ≤ N(T,2T)`. -/
theorem eventually_dyadic_lower (c : ℝ) :
    ∀ᶠ T in atTop, c * (2 * T) ≤ (Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hR⟩ := riemannVonMangoldt_zeta.main
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : ∀ᶠ T in atTop, (2 * c + 1) * (2 * Real.pi) ≤ ell1 T :=
    ell1_tendsto_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ T in atTop, C * Real.log T ≤ T := by
    have := (Real.isLittleO_log_id_atTop.bound (c := 1 / (|C| + 1)) (by positivity))
    filter_upwards [this, eventually_ge_atTop 1] with T hT hT1
    have hl : 0 ≤ Real.log T := Real.log_nonneg hT1
    simp only [id, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg (by linarith : (0:ℝ) ≤ T)] at hT
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    have : (|C| + 1) * Real.log T ≤ T := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0:ℝ) ≤ |C| + 1)
      rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    nlinarith
  filter_upwards [h1, h2, eventually_ge_atTop T₀, eventually_ge_atTop 0] with T h1 h2 hT hT0
  have hb := hR T hT
  rw [zetaZeroConfig_N] at hb
  have hlow := (abs_le.1 hb).1
  have : T / (2 * Real.pi) * ell1 T ≥ (2 * c + 1) * T := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith
  linarith

/-- **N(T)/T → ∞**: the count of nontrivial zeros with `0 < Im ρ ≤ T` (with multiplicity)
eventually dominates every linear function. Discharges MNF.RH's `NcountSuperlinear`. -/
theorem ncountSuperlinear : NcountSuperlinear := by
  intro c hc
  obtain ⟨T₁, hT₁⟩ := (eventually_dyadic_lower c).and (eventually_ge_atTop (0:ℝ)) |>.exists_forall_of_atTop
  refine ⟨2 * T₁, fun T hT => ?_⟩
  obtain ⟨hlow, hpos⟩ := hT₁ (T / 2) (by linarith)
  have h2 : 2 * (T / 2) = T := by ring
  rw [h2] at hlow
  have hsplit := Assembly.N_add zetaZeroConfig (a := 0) (b := T / 2) (c := T) (by linarith)
    (by linarith)
  simp only [zetaZeroConfig_N] at hsplit
  have : (Ncount (T / 2) T : ℝ) ≤ Ncount 0 T := by exact_mod_cast hsplit ▸ Nat.le_add_left _ _
  linarith

theorem tendsto_Ncount_div_atTop :
    Tendsto (fun T => (Ncount 0 T : ℝ) / T) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨T₀, h⟩ := ncountSuperlinear (|b| + 1) (by positivity)
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop 0] with T hT hT0
  rw [le_div_iff₀ hT0]
  nlinarith [h T hT, le_abs_self b]

end Zeta23

#print axioms Zeta23.ncountSuperlinear
#print axioms Zeta23.tendsto_Ncount_div_atTop
