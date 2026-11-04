/-
DE.lean — node DE of the Bohr–Landau closure (2026-11-03).

Targets D (`zeta_eq_euler_maclaurin`) and E (`tail_by_parts`) of
  notes/density-field-2026-11-03/aristotle/BohrLandauClosure.lean,
proved on the zeta23 tree from `Zeta0EqZeta` (Zeta23.FromPNTPlus.ZetaBounds) and Mathlib.
Definitions `psi`, `B2per`, `P`, `S` are copied verbatim from the targets file.
-/
import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace BLClosure

/-- the sawtooth ψ(u) = {u} − 1/2 -/
noncomputable def psi (u : ℝ) : ℝ := Int.fract u - 1 / 2

/-- the periodic second Bernoulli function B₂({u}) = {u}² − {u} + 1/6 -/
noncomputable def B2per (u : ℝ) : ℝ := Int.fract u ^ 2 - Int.fract u + 1 / 6

/-- P = (B₂per − 1/6)/2, the continuous periodic antiderivative of ψ with P(n) = 0 -/
noncomputable def P (u : ℝ) : ℝ := (B2per u - 1 / 6) / 2

/-- the Dirichlet polynomial S_N(s) = Σ_{n=1}^{N} n^{−s} -/
noncomputable def S (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

/-! ### Elementary facts about ψ and P -/

lemma P_eq (u : ℝ) : P u = (Int.fract u ^ 2 - Int.fract u) / 2 := by
  simp only [P, B2per]; ring

lemma psi_abs_le (u : ℝ) : |psi u| ≤ 1 / 2 := by
  rw [psi, abs_le]
  constructor <;> linarith [Int.fract_nonneg u, Int.fract_lt_one u]

lemma P_abs_le (u : ℝ) : |P u| ≤ 1 / 8 := by
  rw [P_eq, abs_le]
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  constructor <;> nlinarith [sq_nonneg (Int.fract u - 1 / 2)]

lemma P_natCast (n : ℕ) : P n = 0 := by
  simp [P_eq, Int.fract_natCast]

lemma continuous_P : Continuous P := by
  have : P = (fun x : ℝ => (x ^ 2 - x) / 2) ∘ Int.fract := by
    ext u; simp [P_eq]
  rw [this]
  exact ContinuousOn.comp_fract'' (by fun_prop) (by norm_num)

lemma measurable_psi : Measurable psi := by
  unfold psi
  exact measurable_fract.sub measurable_const

/-- P' = ψ off the integers. -/
lemma hasDerivAt_P {u : ℝ} (hu : u ∉ Set.range ((↑) : ℤ → ℝ)) : HasDerivAt P (psi u) u := by
  have hlt : (⌊u⌋ : ℝ) < u := by
    rcases (Int.floor_le u).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨⌊u⌋, h⟩ hu
  have hmem : Ioo (⌊u⌋ : ℝ) (⌊u⌋ + 1) ∈ 𝓝 u := Ioo_mem_nhds hlt (Int.lt_floor_add_one u)
  have h1 : HasDerivAt (fun x : ℝ => x - ⌊u⌋) 1 u := (hasDerivAt_id u).sub_const _
  have h2 : HasDerivAt (fun x : ℝ => (x - ⌊u⌋) ^ 2) (2 * (u - ⌊u⌋)) u := by
    have := h1.fun_pow 2
    simpa using this
  have hpsi : psi u = (2 * (u - ⌊u⌋) - 1) / 2 := by
    rw [psi, ← Int.self_sub_floor]; ring
  have hd : HasDerivAt (fun x : ℝ => ((x - ⌊u⌋) ^ 2 - (x - ⌊u⌋)) / 2) (psi u) u := by
    rw [hpsi]; exact (h2.sub h1).div_const 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [hmem] with x hx
  have hfl : ⌊x⌋ = ⌊u⌋ := Int.floor_eq_iff.mpr ⟨hx.1.le, hx.2⟩
  rw [P_eq, ← Int.self_sub_floor, hfl]

/-! ### Integrability of the tails -/

lemma integrableOn_bdd_mul_cpow {g : ℝ → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ u, |g u| ≤ c)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.re < -1) :
    IntegrableOn (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ w) (Ioi a) := by
  apply Integrable.bdd_mul (c := c) ((integrableOn_Ioi_cpow_iff ha).mpr hw)
    (Complex.measurable_ofReal.comp hg).aestronglyMeasurable
  refine ae_of_all _ (fun u => ?_)
  show ‖(g u : ℂ)‖ ≤ c
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hc u

lemma integrableOn_psi_mul {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => (psi u : ℂ) * (u : ℂ) ^ (-s - 1)) (Ioi a) :=
  integrableOn_bdd_mul_cpow measurable_psi psi_abs_le ha (by simp; linarith)

lemma integrableOn_P_mul {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => (P u : ℂ) * (u : ℂ) ^ (-s - 2)) (Ioi a) :=
  integrableOn_bdd_mul_cpow continuous_P.measurable P_abs_le ha (by simp; linarith)

/-! ### E. Integration by parts on [N, M], then M → ∞ -/

lemma tail_by_parts_interval {s : ℂ} (hs : 0 < s.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∫ u in (N : ℝ)..M, (psi u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ u in (N : ℝ)..M, (P u : ℂ) * (u : ℂ) ^ (-s - 2) := by
  have hle : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs1 : -s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have hA : IntervalIntegrable (fun u : ℝ => (psi u : ℂ) * (u : ℂ) ^ (-s - 1)) volume N M :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
      ((integrableOn_psi_mul hs hNpos).mono_set Ioc_subset_Ioi_self)
  have hB : IntervalIntegrable (fun u : ℝ => (P u : ℂ) * (u : ℂ) ^ (-s - 2)) volume N M :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
      ((integrableOn_P_mul hs hNpos).mono_set Ioc_subset_Ioi_self)
  have key : ∫ u in (N : ℝ)..M, ((psi u : ℂ) * (u : ℂ) ^ (-s - 1)
      + (-s - 1) * ((P u : ℂ) * (u : ℂ) ^ (-s - 2))) = 0 := by
    rw [integral_eq_of_hasDerivAt_off_countable_of_le
      (fun u : ℝ => (P u : ℂ) * (u : ℂ) ^ (-s - 1))
      (fun u : ℝ => (psi u : ℂ) * (u : ℂ) ^ (-s - 1) + (-s - 1) * ((P u : ℂ) * (u : ℂ) ^ (-s - 2)))
      hle (Set.countable_range ((↑) : ℤ → ℝ)) ?_ ?_ ?_]
    · simp [P_natCast]
    · apply ContinuousOn.mul (continuous_ofReal.comp continuous_P).continuousOn
      apply continuous_ofReal.continuousOn.cpow_const
      intro x hx
      exact ofReal_mem_slitPlane.mpr (by linarith [hx.1])
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1.1]
      have h1 := (hasDerivAt_P hx.2).ofReal_comp
      have h2 := hasDerivAt_ofReal_cpow_const hxpos.ne' hs1
      have h3 : HasDerivAt (fun u : ℝ => (P u : ℂ) * (u : ℂ) ^ (-s - 1))
          ((psi x : ℂ) * (x : ℂ) ^ (-s - 1) + (P x : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 2))) x := by
        have := h1.fun_mul h2
        rwa [show (-s - 1 - 1 : ℂ) = -s - 2 by ring] at this
      show HasDerivAt _ ((psi x : ℂ) * (x : ℂ) ^ (-s - 1)
        + (-s - 1) * ((P x : ℂ) * (x : ℂ) ^ (-s - 2))) x
      rw [show (psi x : ℂ) * (x : ℂ) ^ (-s - 1) + (-s - 1) * ((P x : ℂ) * (x : ℂ) ^ (-s - 2))
        = (psi x : ℂ) * (x : ℂ) ^ (-s - 1) + (P x : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 2)) by ring]
      exact h3
    · exact hA.add (hB.const_mul _)
  rw [intervalIntegral.integral_add hA (hB.const_mul _), intervalIntegral.integral_const_mul] at key
  linear_combination key

/-- **E.** The second Euler–Maclaurin step: ∫_N^∞ ψ(u) u^{−s−1} du = (s+1) ∫_N^∞ P(u) u^{−s−2} du. -/
theorem tail_by_parts {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ u in Ioi (N : ℝ), (P u : ℂ) * (u : ℂ) ^ (-s - 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_psi_mul hs hNpos)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := (intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_P_mul hs hNpos)
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (s + 1)
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (tail_by_parts_interval hs hN hM).symm

/-! ### D. Euler–Maclaurin for ζ, one step, from the tree's `Zeta0EqZeta` -/

/-- **D.** For Re s > 0, s ≠ 1 and N ≥ 1:
  ζ(s) = S_N(s) + N^{1−s}/(s − 1) − N^{−s}/2 − s ∫_N^∞ ψ(u) u^{−s−1} du. -/
theorem zeta_eq_euler_maclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = S N s + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
      - s * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [← Zeta0EqZeta (N := N) (by omega) hs hs1, riemannZeta0]
  have h1 : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = S N s := by
    rw [Finset.sum_range_eq_add_Ico _ (by omega)]
    simp only [Nat.cast_zero, zero_cpow hs0, div_zero, zero_add, S]
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [one_div, cpow_neg]
  have h2 : ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
      = -∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [psi, ← Int.self_sub_floor]
    push_cast
    rw [show -s - 1 = -(s + 1) by ring, cpow_neg, div_eq_mul_inv]
    ring
  have h3 : (N : ℂ) ^ (1 - s) / (s - 1) = -((N : ℂ) ^ (1 - s) / (1 - s)) := by
    rw [← div_neg, neg_sub]
  rw [h1, h2, h3]
  ring

end BLClosure
