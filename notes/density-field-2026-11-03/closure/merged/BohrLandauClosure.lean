/-
BohrLandauClosure.lean — MERGED file of the Bohr–Landau closure (2026-11-03).

Assembled from the node files FDT1, FDT2, B2, DE, CF, G, I, CLOSE of the closure run.  Each
proved lemma appears once; where two nodes proved the same statement the variant used
downstream is kept (DE's `hasDerivAt_P` / `P_abs_le` / `continuous_P` over B2's
`hasDerivAt_P` / `P_bound` / `P_continuous`; FDT2's argument order for
`first_derivative_test_amp_smooth`, which is FDT1's statement up to the order of the
arguments).  Sections, in dependency order:

  * NodeB2   (B)    `B2per_fourier`, `P_fourier`, plus B2's `P_nonpos`, `P_intCast`
  * NodeDE   (E)    facts about ψ, P; integrability; `tail_by_parts`; B2's `hasDerivAt_P'`
  * NodeFDT  (A/A′) `first_derivative_test_amp_smooth'` (CF's form, sign hypothesis on G/F'),
                    `first_derivative_test_amp_smooth`, `first_derivative_test_smooth`
  * NodeCF   (C, F) `tail_mode_bound` (and ′, ⁻), `tail_sharp`
  * NodeD    (D)    `zeta_eq_euler_maclaurin` (from the tree's `Zeta0EqZeta`)
  * NodeG    (G)    `zeta_approx_sharp`, segment specialisations
  * NodeI    (I)    `meanSquareUnif_all`, `meanSquareUnifFrom_all`, `rightHalfBound`,
                    `bohrLandau_all`
  * CLOSEpart       the tree's statements: `Zeta23.BL.rightHalf_all`, `rightHalfBound`,
                    `bohrLandau_full`, `rightHalfBound_of_meanSquare'`, `meanSquare_strip'`,
                    `MNF.RH.reservoirDensityOne_unconditional`, `onLineDensityOne_of_gap_only`
  * ContractNotProved  the four contract statements NO node proved, kept as `sorry` and
                    CLEARLY MARKED: A and A′ in their original monotone/antitone form (the
                    smooth strengthenings above are what the downstream nodes use) and H
                    (`dirichlet_mean_value`, `offdiag_pow_bound`, "proved in the author's
                    tree; a proof not required").  Nothing above depends on them.

`#print axioms` for every theorem is at the end.
-/
import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.BL.BohrLandauPartial
import Zeta23.BohrLandau
import MNF.RH.DensityPartial

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real ComplexConjugate

namespace BLClosure

/-- the sawtooth ψ(u) = {u} − 1/2 -/
noncomputable def psi (u : ℝ) : ℝ := Int.fract u - 1 / 2

/-- the periodic second Bernoulli function B₂({u}) = {u}² − {u} + 1/6 -/
noncomputable def B2per (u : ℝ) : ℝ := Int.fract u ^ 2 - Int.fract u + 1 / 6

/-- P = (B₂per − 1/6)/2, the continuous periodic antiderivative of ψ with P(n) = 0 -/
noncomputable def P (u : ℝ) : ℝ := (B2per u - 1 / 6) / 2

/-- the Dirichlet polynomial S_N(s) = Σ_{n=1}^{N} n^{−s} -/
noncomputable def S (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

section NodeB2

/-! ### From node B2: the Fourier series of B₂per and of P -/

/-- Mathlib's `hasSum_one_div_nat_pow_mul_cos` with k = 1, unfolded:
Σ_{n ≥ 0} cos(2πnx)/n² = π² (x² − x + 1/6) for x ∈ [0, 1] (the n = 0 term is 0 in Lean). -/
lemma hasSum_cos_div_sq_bernoulli {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * x))
      (π ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval x
      = x ^ 2 - x + 1 / 6 := by
    have := bernoulliFun_two x
    rw [bernoulliFun] at this
    rw [show 2 * 1 = 2 by norm_num, this]
    norm_num
  rw [hb] at h
  have hval : (-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)
      * (x ^ 2 - x + 1 / 6) = π ^ 2 * (x ^ 2 - x + 1 / 6) := by
    have h2 : ((2 * 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2]; ring
  rw [hval] at h
  simpa using h

/-- periodicity of the cosine mode: cos(2π(ν+1)u) = cos(2π(ν+1){u}) -/
lemma cos_mode_fract (ν : ℕ) (u : ℝ) :
    Real.cos (2 * π * ((ν : ℝ) + 1) * u) = Real.cos (2 * π * ((ν : ℝ) + 1) * Int.fract u) := by
  have hu := Int.floor_add_fract u
  have : 2 * π * ((ν : ℝ) + 1) * u
      = 2 * π * ((ν : ℝ) + 1) * Int.fract u + ((((ν + 1 : ℕ) : ℤ) * ⌊u⌋ : ℤ) : ℝ) * (2 * π) := by
    push_cast
    linear_combination (-(2 * π * ((ν : ℝ) + 1))) * hu
  rw [this, Real.cos_add_int_mul_two_pi]

/-- **B.** The Fourier series of B₂per (absolutely convergent). -/
theorem B2per_fourier (u : ℝ) :
    HasSum (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      (B2per u) := by
  have hx : Int.fract u ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have h := (hasSum_cos_div_sq_bernoulli hx).div_const (π ^ 2)
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one] at h2
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hf : (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      = fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 * Real.cos (2 * π * ((n + 1 : ℕ) : ℝ) * Int.fract u)
          / π ^ 2 := by
    funext ν
    rw [cos_mode_fract]
    push_cast
    have hν : ((ν : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hv : B2per u = π ^ 2 * (Int.fract u ^ 2 - Int.fract u + 1 / 6) / π ^ 2
      - 1 / ((0 : ℕ) : ℝ) ^ 2 * Real.cos (2 * π * ((0 : ℕ) : ℝ) * Int.fract u) / π ^ 2 := by
    simp only [B2per, Nat.cast_zero, zero_pow (two_ne_zero), div_zero, zero_mul]
    field_simp
    ring
  rw [hf, hv]
  exact h2

/-- Fourier series of P: P(u) + 1/12 = Σ_{ν≥1} cos(2πνu)/(2π²ν²). -/
theorem P_fourier (u : ℝ) :
    HasSum (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      (P u + 1 / 12) := by
  have h := (B2per_fourier u).div_const 2
  have hf : (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      = fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2) / 2 := by
    funext ν; rw [div_div]; ring
  have hv : P u + 1 / 12 = B2per u / 2 := by unfold P; ring
  rw [hf, hv]
  exact h


/-- P ≤ 0 (in fact −1/8 ≤ P ≤ 0); node B2. -/
theorem P_nonpos (u : ℝ) : P u ≤ 0 := by
  unfold P B2per
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  nlinarith

/-- P vanishes at the integers; node B2. -/
theorem P_intCast (n : ℤ) : P n = 0 := by
  simp [P, B2per, Int.fract_intCast]

end NodeB2

section NodeDE

/-! ### From node DE: elementary facts about ψ and P, integrability, `tail_by_parts` -/

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


/-- `hasDerivAt_P` with the hypothesis in the `Int.fract u ≠ 0` form (node B2's variant). -/
theorem hasDerivAt_P' {u : ℝ} (hu : Int.fract u ≠ 0) : HasDerivAt P (psi u) u := by
  apply hasDerivAt_P
  rintro ⟨n, hn⟩
  apply hu
  rw [← hn, Int.fract_intCast]

end NodeDE

section NodeFDT

/-! ### The first-derivative test (node FDT2), with the sign hypothesis on G/F' only -/

/-- **First-derivative test with a nonnegative amplitude**, smooth form: on `[a, b]` the phase
`F` has `F' ≥ lam > 0`, the amplitude `G ≥ 0`, and `G/F'` is nonincreasing
(`G' F' − G F'' ≤ 0`); then `‖∫ₐᵇ G(x) e^{i F(x)} dx‖ ≤ 4 G(a) / lam`. -/
theorem first_derivative_test_amp_smooth' {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b))
    (G G' : ℝ → ℝ) (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G' x) x)
    (hG0 : ∀ x ∈ Set.Icc a b, 0 ≤ G x)
    (hGc : ContinuousOn G' (Set.Icc a b))
    (hw' : ∀ x ∈ Set.Icc a b, G' x * F' x - G x * F'' x ≤ 0) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hF'pos : ∀ x ∈ Icc a b, 0 < F' x := fun x hx => lt_of_lt_of_le hlam (hlow x hx)
  have hF'ne : ∀ x ∈ Icc a b, F' x ≠ 0 := fun x hx => (hF'pos x hx).ne'
  -- the real weight w = G / F' and its derivative w'
  set w : ℝ → ℝ := fun x => G x / F' x with hw_def
  set w' : ℝ → ℝ := fun x => (G' x * F' x - G x * F'' x) / F' x ^ 2 with hw'_def
  have hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x := fun x hx =>
    (hG x hx).div (hF' x hx) (hF'ne x hx)
  have hw'nonpos : ∀ x ∈ Icc a b, w' x ≤ 0 := by
    intro x hx
    simp only [hw'_def]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact hw' x hx
    · positivity
  have hwnonneg : ∀ x ∈ Icc a b, 0 ≤ w x := fun x hx =>
    div_nonneg (hG0 x hx) (hF'pos x hx).le
  -- continuity facts
  have hFc : ContinuousOn F (Icc a b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' (Icc a b) := fun x hx =>
    (hF' x hx).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (Icc a b) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have hw'c : ContinuousOn w' (Icc a b) := by
    simp only [hw'_def]
    exact ((hGc.mul hF'c).sub (hGcont.mul hcont)).div (hF'c.pow 2)
      (fun x hx => pow_ne_zero 2 (hF'ne x hx))
  -- complex versions for integration by parts
  set u : ℝ → ℂ := fun x => ((w x : ℝ) : ℂ) with hu_def
  set u' : ℝ → ℂ := fun x => ((w' x : ℝ) : ℂ) with hu'_def
  set v : ℝ → ℂ := fun x => Complex.exp (Complex.I * (F x : ℂ)) with hv_def
  set v' : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (F x : ℂ)) * (Complex.I * (F' x : ℂ)) with hv'_def
  have hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    rw [hI] at hx
    exact (hw x hx).ofReal_comp
  have hv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x := by
    intro x hx
    rw [hI] at hx
    exact ((hF x hx).ofReal_comp.const_mul Complex.I).cexp
  have hu'int : IntervalIntegrable u' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hI]
    exact Complex.continuous_ofReal.comp_continuousOn hw'c
  have hv'int : IntervalIntegrable v' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hI]
    have h1 : ContinuousOn (fun x : ℝ => Complex.I * (F x : ℂ)) (Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hFc)
    have h2 : ContinuousOn (fun x : ℝ => Complex.I * (F' x : ℂ)) (Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hF'c)
    exact h1.cexp.mul h2
  -- integration by parts
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int
  -- the left side of IBP is I times the integral we want
  have hkey : ∫ x in a..b, u x * v' x
      = Complex.I * ∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hI] at hx
    have hne : (F' x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hF'ne x hx)
    simp only [hu_def, hv'_def, hw_def]
    push_cast
    field_simp
  have hnorm_eq : ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖
      = ‖∫ x in a..b, u x * v' x‖ := by
    rw [hkey, norm_mul, Complex.norm_I, one_mul]
  rw [hnorm_eq, hibp]
  -- norms of the pieces
  have hvnorm : ∀ x, ‖v x‖ = 1 := fun x => Complex.norm_exp_I_mul_ofReal (F x)
  have hunorm : ∀ x ∈ Icc a b, ‖u x‖ = w x := by
    intro x hx
    simp only [hu_def, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hwnonneg x hx)
  have hu'norm : ∀ x ∈ Icc a b, ‖u' x * v x‖ = -(w' x) := by
    intro x hx
    rw [norm_mul, hvnorm, mul_one]
    simp only [hu'_def, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonpos (hw'nonpos x hx)
  -- ∫ ‖u' v‖ = w a − w b by the fundamental theorem of calculus
  have hint_norm : ∫ x in a..b, ‖u' x * v x‖ = w a - w b := by
    have h1 : ∫ x in a..b, ‖u' x * v x‖ = ∫ x in a..b, -(w' x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [hI] at hx
      exact hu'norm x hx
    have h2 : ∫ x in a..b, w' x = w b - w a := by
      apply integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [hI] at hx
        exact hw x hx
      · exact hw'c.intervalIntegrable_of_Icc hab
    rw [h1, intervalIntegral.integral_neg, h2]
    ring
  have hbound : ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖ ≤ w b + w a + (w a - w b) := by
    calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
        ≤ ‖u b * v b - u a * v a‖ + ‖∫ x in a..b, u' x * v x‖ := norm_sub_le _ _
      _ ≤ (‖u b * v b‖ + ‖u a * v a‖) + ‖∫ x in a..b, u' x * v x‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (w b + w a) + ∫ x in a..b, ‖u' x * v x‖ := by
          apply add_le_add
          · apply add_le_add
            · rw [norm_mul, hvnorm, mul_one, hunorm b hb]
            · rw [norm_mul, hvnorm, mul_one, hunorm a ha]
          · exact intervalIntegral.norm_integral_le_integral_norm hab
      _ = w b + w a + (w a - w b) := by rw [hint_norm]
  have hwa : w a ≤ G a / lam := by
    simp only [hw_def]
    exact div_le_div_of_nonneg_left (hG0 a ha) hlam (hlow a ha)
  have hGa : 0 ≤ G a / lam := div_nonneg (hG0 a ha) hlam.le
  calc ‖u b * v b - u a * v a - ∫ x in a..b, u' x * v x‖
      ≤ w b + w a + (w a - w b) := hbound
    _ = 2 * w a := by ring
    _ ≤ 2 * (G a / lam) := by linarith
    _ ≤ 4 * G a / lam := by rw [mul_div_assoc]; linarith


/-- **First-derivative test with a nonnegative nonincreasing amplitude** (Titchmarsh Lemma 4.3),
smooth form (nodes FDT1/FDT2): if on `[a, b]` the phase `F` has `F' ≥ lam > 0` and `F'' ≥ 0`,
and the amplitude `G ≥ 0` has `G' ≤ 0`, then `‖∫ₐᵇ G(x) e^{i F(x)} dx‖ ≤ 4 G(a) / lam`. -/
theorem first_derivative_test_amp_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x) (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b))
    (G G' : ℝ → ℝ) (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Set.Icc a b, G' x ≤ 0) (hG0 : ∀ x ∈ Set.Icc a b, 0 ≤ G x)
    (hGc : ContinuousOn G' (Set.Icc a b)) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  refine first_derivative_test_amp_smooth' hab hlam F F' F'' hF hF' hlow hcont G G' hG hG0 hGc
    (fun x hx => ?_)
  have h1 : G' x * F' x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hG' x hx) (le_trans hlam.le (hlow x hx))
  have h2 : 0 ≤ G x * F'' x := mul_nonneg (hG0 x hx) (hconv x hx)
  linarith

/-- **First-derivative test** (Titchmarsh Lemma 4.2), smooth form (nodes FDT1/FDT2): if on
`[a, b]` the phase `F` has `F' ≥ lam > 0` and `F'' ≥ 0`, then `‖∫ₐᵇ e^{i F(x)} dx‖ ≤ 4 / lam`. -/
theorem first_derivative_test_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x) (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b)) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 / lam := by
  have h := first_derivative_test_amp_smooth hab hlam F F' F'' hF hF' hconv hlow hcont
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun x _ => hasDerivAt_const x (1 : ℝ))
    (fun _ _ => le_rfl) (fun _ _ => zero_le_one) continuousOn_const
  simpa using h

end NodeFDT

section NodeCF

/-! ## C. One Fourier mode of the tail -/

/-- the integrand of C as amplitude × phase: for u > 0,
e^{2πiνu} u^{−σ−it−2} = u^{−σ−2} · e^{i(2πνu − t log u)}. -/
lemma mode_integrand_eq (σ t : ℝ) (ν : ℕ) {u : ℝ} (hu : 0 < u) :
    Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ)) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
      = ((u ^ (-σ - 2) : ℝ) : ℂ)
        * Complex.exp (I * ((2 * π * ν * u - t * Real.log u : ℝ) : ℂ)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu0, ← Complex.ofReal_log hu.le, Real.rpow_def_of_pos hu,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- the first-derivative test applied on [x, X] to F(u) = 2πνu − t log u, G(u) = u^{−σ−2}. -/
lemma mode_bound_interval {σ t x X : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (hxt : t ≤ π * x)
    (hX : x ≤ X) {ν : ℕ} (hν : 1 ≤ ν) :
    ‖∫ u in x..X, ((u ^ (-σ - 2) : ℝ) : ℂ)
        * Complex.exp (I * ((2 * π * ν * u - t * Real.log u : ℝ) : ℂ))‖
      ≤ 4 * x ^ (-σ - 2) / (π * ν) := by
  have hν' : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hπ : 0 < π := Real.pi_pos
  have hlam : 0 < π * ν := by positivity
  have hpos : ∀ u ∈ Icc x X, 0 < u := fun u hu => by linarith [hu.1]
  have hr : ∀ u ∈ Icc x X, t / u ≤ π := by
    intro u hu
    rw [div_le_iff₀ (hpos u hu)]
    calc t ≤ π * x := hxt
      _ ≤ π * u := by gcongr; exact hu.1
  have hπν : π ≤ π * ν := le_mul_of_one_le_right hπ.le hν'
  refine first_derivative_test_amp_smooth' hX hlam
    (fun u => 2 * π * ν * u - t * Real.log u) (fun u => 2 * π * ν - t / u) (fun u => t / u ^ 2)
    ?_ ?_ ?_ ?_
    (fun u => u ^ (-σ - 2)) (fun u => (-σ - 2) * u ^ (-σ - 2 - 1))
    ?_ ?_ ?_ ?_
  · -- hF
    intro u hu
    have h := ((hasDerivAt_id' u).const_mul (2 * π * ν)).sub
      ((Real.hasDerivAt_log (hpos u hu).ne').const_mul t)
    exact h.congr_deriv (by ring)
  · -- hF'
    intro u hu
    have h := ((hasDerivAt_inv (hpos u hu).ne').const_mul t).const_sub (2 * π * ν)
    have e : (fun u : ℝ => 2 * π * ν - t / u) = fun y => 2 * π * ν - t * y⁻¹ := by
      funext y; rw [div_eq_mul_inv]
    rw [e]
    exact h.congr_deriv (by ring)
  · -- hlow
    intro u hu
    have := hr u hu
    show π * ν ≤ 2 * π * ν - t / u
    linarith
  · -- hcont
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun u hu => pow_ne_zero 2 (hpos u hu).ne')
  · -- hG
    intro u hu
    exact Real.hasDerivAt_rpow_const (Or.inl (hpos u hu).ne')
  · -- hG0
    intro u hu
    exact Real.rpow_nonneg (hpos u hu).le _
  · -- hGc
    exact continuousOn_const.mul
      (fun u hu => (Real.continuousAt_rpow_const u _ (Or.inl (hpos u hu).ne')).continuousWithinAt)
  · -- hw'
    intro u hu
    have hu0 := hpos u hu
    have hru := hr u hu
    show (-σ - 2) * u ^ (-σ - 2 - 1) * (2 * π * ν - t / u) - u ^ (-σ - 2) * (t / u ^ 2) ≤ 0
    rw [Real.rpow_sub_one hu0.ne']
    have hg : 0 < u ^ (-σ - 2) := Real.rpow_pos_of_pos hu0 _
    have e : (-σ - 2) * (u ^ (-σ - 2) / u) * (2 * π * ν - t / u) - u ^ (-σ - 2) * (t / u ^ 2)
        = (u ^ (-σ - 2) / u) * ((-σ - 2) * (2 * π * ν - t / u) - t / u) := by
      field_simp
    rw [e]
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · have h1 : (σ + 1) * (t / u) ≤ (σ + 1) * π :=
        mul_le_mul_of_nonneg_left hru (by linarith)
      have h2 : (σ + 2) * (2 * π) ≤ (σ + 2) * (2 * π * ν) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hν') (by linarith)
      have h3 : 0 < σ * π := mul_pos hσ hπ
      nlinarith

/-- a bounded measurable factor times an integrable complex power is integrable on (a, ∞) -/
lemma integrableOn_bdd_mul_cpow' {e : ℝ → ℂ} (he : Measurable e) (hb : ∀ u, ‖e u‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.re < -1) :
    IntegrableOn (fun u : ℝ => e u * (u : ℂ) ^ w) (Ioi a) :=
  Integrable.bdd_mul (c := 1) ((integrableOn_Ioi_cpow_iff ha).mpr hw) he.aestronglyMeasurable
    (ae_of_all _ hb)

lemma integrableOn_exp_mul_cpow {α : ℂ} (hα : α.re = 0) {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun u : ℝ => Complex.exp (α * (u : ℂ)) * (u : ℂ) ^ w) (Ioi a) := by
  apply integrableOn_bdd_mul_cpow' (e := fun u : ℝ => Complex.exp (α * (u : ℂ))) _ _ ha hw
  · exact (by fun_prop : Continuous fun u : ℝ => Complex.exp (α * (u : ℂ))).measurable
  · intro u
    rw [Complex.norm_exp]
    simp [hα]

lemma integrableOn_exp_neg_mul_cpow {α : ℂ} (hα : α.re = 0) {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(α * (u : ℂ))) * (u : ℂ) ^ w) (Ioi a) := by
  have e : (fun u : ℝ => Complex.exp (-(α * (u : ℂ))) * (u : ℂ) ^ w)
      = fun u : ℝ => Complex.exp ((-α) * (u : ℂ)) * (u : ℂ) ^ w := by
    funext u; rw [neg_mul]
  rw [e]
  exact integrableOn_exp_mul_cpow (by simp [hα]) ha hw

lemma re_w (σ t : ℝ) : (-(σ : ℂ) - t * I - 2).re = -σ - 2 := by simp

lemma re_w_lt {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : (-(σ : ℂ) - t * I - 2).re < -1 := by
  rw [re_w]; linarith

lemma re_phase (ν : ℕ) : (2 * π * I * (ν : ℂ)).re = 0 := by simp

lemma re_phase' (ν : ℕ) : (2 * π * I * ((ν : ℂ) + 1)).re = 0 := by simp

/-- **C′.** The mode bound for every real t with t ≤ πx. -/
theorem tail_mode_bound' {σ t x : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (hxt : t ≤ π * x)
    {ν : ℕ} (hν : 1 ≤ ν) :
    ‖∫ u in Ioi x, Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ)) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 8 / (π * ν) * x ^ (-σ - 2) := by
  have hxpos : 0 < x := by linarith
  have hν' : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hπ : 0 < π := Real.pi_pos
  have hlam : 0 < π * ν := by positivity
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ))
      * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) (Ioi x) :=
    integrableOn_exp_mul_cpow (re_phase ν) hxpos (re_w_lt hσ t)
  have hlim := (intervalIntegral_tendsto_integral_Ioi x hint
    (tendsto_id (x := (atTop : Filter ℝ)))).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with X hX
  show ‖∫ u in x..X, Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ))
      * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖ ≤ 8 / (π * ν) * x ^ (-σ - 2)
  have heq : ∫ u in x..X, Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ))
        * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
      = ∫ u in x..X, ((u ^ (-σ - 2) : ℝ) : ℂ)
          * Complex.exp (I * ((2 * π * ν * u - t * Real.log u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hX] at hu
    exact mode_integrand_eq σ t ν (by linarith [hu.1])
  rw [heq]
  have hx0 : 0 ≤ x ^ (-σ - 2) := Real.rpow_nonneg hxpos.le _
  calc ‖∫ u in x..X, ((u ^ (-σ - 2) : ℝ) : ℂ)
          * Complex.exp (I * ((2 * π * ν * u - t * Real.log u : ℝ) : ℂ))‖
      ≤ 4 * x ^ (-σ - 2) / (π * ν) := mode_bound_interval hσ hx1 hxt hX hν
    _ = 4 / (π * ν) * x ^ (-σ - 2) := by ring
    _ ≤ 8 / (π * ν) * x ^ (-σ - 2) := by
        apply mul_le_mul_of_nonneg_right _ hx0
        exact div_le_div_of_nonneg_right (by norm_num) hlam.le

set_option linter.unusedVariables false in
/-- **C.** One Fourier mode of the tail (the statement of the targets file).  The hypothesis
`ht : 0 ≤ t` of the contract is kept for compatibility but is not needed (`tail_mode_bound'`). -/
theorem tail_mode_bound {σ t x : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (ht : 0 ≤ t) (hxt : t / π ≤ x)
    {ν : ℕ} (hν : 1 ≤ ν) :
    ‖∫ u in Ioi x, Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ)) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 8 / (π * ν) * x ^ (-σ - 2) := by
  have hxt' : t ≤ π * x := by
    have := (div_le_iff₀ Real.pi_pos).mp hxt
    linarith
  exact tail_mode_bound' hσ hx1 hxt' hν

/-- **C⁻.** The same for the mode e^{−2πiνu}, by complex conjugation. -/
theorem tail_mode_bound_neg {σ t x : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (hxt : -t ≤ π * x)
    {ν : ℕ} (hν : 1 ≤ ν) :
    ‖∫ u in Ioi x, Complex.exp (-(2 * π * I * (ν : ℂ) * (u : ℂ)))
        * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 8 / (π * ν) * x ^ (-σ - 2) := by
  have hxpos : 0 < x := by linarith
  have hpt : ∀ u ∈ Ioi x,
      Complex.exp (-(2 * π * I * (ν : ℂ) * (u : ℂ))) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
        = conj (Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ))
            * (u : ℂ) ^ (-(σ : ℂ) - ((-t : ℝ) : ℂ) * I - 2)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hxpos hu
    have harg : (u : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg hu0.le]; exact ne_of_lt Real.pi_pos
    have hc : ∀ n : ℂ, conj ((u : ℂ) ^ n) = (u : ℂ) ^ (conj n) := by
      intro n
      rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
    rw [map_mul, ← Complex.exp_conj, hc]
    congr 2
    · simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
      ring
    · simp only [map_mul, map_neg, map_sub, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_conj, Complex.norm_conj]
  exact tail_mode_bound' hσ hx1 hxt hν

/-! ## F. The sharpened tail -/

/-- the ν-th cosine mode of P + 1/12 (frequency ν + 1) -/
noncomputable def cmode (ν : ℕ) (u : ℝ) : ℝ :=
  Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2)

lemma cmode_hasSum (u : ℝ) : HasSum (fun ν => cmode ν u) (P u + 1 / 12) := P_fourier u

lemma continuous_cmode (ν : ℕ) : Continuous (cmode ν) := by
  unfold cmode; fun_prop

lemma cmode_abs_le (ν : ℕ) (u : ℝ) :
    |cmode ν u| ≤ 1 / (2 * π ^ 2) * (1 / ((ν : ℝ) + 1) ^ 2) := by
  unfold cmode
  have hD : (0 : ℝ) < 2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hD]
  calc |Real.cos (2 * π * ((ν : ℝ) + 1) * u)| / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2)
      ≤ 1 / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2) :=
        div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hD.le
    _ = 1 / (2 * π ^ 2) * (1 / ((ν : ℝ) + 1) ^ 2) := by
        field_simp

/-- cos as the average of the two exponentials, in the form used below -/
lemma cmode_eq (ν : ℕ) (u : ℝ) :
    (cmode ν u : ℂ) = ((1 / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2) / 2 : ℝ) : ℂ)
      * (Complex.exp (2 * π * I * ((ν : ℂ) + 1) * (u : ℂ))
        + Complex.exp (-(2 * π * I * ((ν : ℂ) + 1) * (u : ℂ)))) := by
  have e1 : Complex.exp (2 * π * I * ((ν : ℂ) + 1) * (u : ℂ))
      = Complex.exp (((2 * π * ((ν : ℝ) + 1) * u : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (-(2 * π * I * ((ν : ℂ) + 1) * (u : ℂ)))
      = Complex.exp (-((2 * π * ((ν : ℝ) + 1) * u : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [e1, e2]
  unfold cmode
  rw [Complex.ofReal_div, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

/-- the bound for one mode integral of (P + 1/12) u^{−s−2} on (N, ∞), N ≥ max(1, t) -/
lemma mode_integral_bound {σ t : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) (hxt : t ≤ π * N)
    (hxt' : -t ≤ π * N) (ν : ℕ) :
    ‖∫ u in Ioi (N : ℝ), (cmode ν u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 4 / π ^ 3 * (1 / ((ν : ℝ) + 1) ^ 3) * (N : ℝ) ^ (-σ - 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hπ : 0 < π := Real.pi_pos
  have hν1 : 1 ≤ ν + 1 := by omega
  have hp := tail_mode_bound' hσ hN1 hxt hν1
  have hm := tail_mode_bound_neg hσ hN1 hxt' hν1
  push_cast at hp hm
  have hpsiP : IntegrableOn (fun u : ℝ => Complex.exp (2 * π * I * ((ν : ℂ) + 1) * (u : ℂ))
      * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) (Ioi (N : ℝ)) :=
    integrableOn_exp_mul_cpow (re_phase' ν) hNpos (re_w_lt hσ t)
  have hpsiM : IntegrableOn (fun u : ℝ => Complex.exp (-(2 * π * I * ((ν : ℂ) + 1) * (u : ℂ)))
      * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) (Ioi (N : ℝ)) :=
    integrableOn_exp_neg_mul_cpow (re_phase' ν) hNpos (re_w_lt hσ t)
  set κ : ℝ := 1 / (2 * π ^ 2 * ((ν : ℝ) + 1) ^ 2) / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hint_eq : ∫ u in Ioi (N : ℝ), (cmode ν u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
      = (κ : ℂ) * ((∫ u in Ioi (N : ℝ), Complex.exp (2 * π * I * ((ν : ℂ) + 1) * (u : ℂ))
            * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2))
          + ∫ u in Ioi (N : ℝ), Complex.exp (-(2 * π * I * ((ν : ℂ) + 1) * (u : ℂ)))
            * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) := by
    rw [← MeasureTheory.integral_add hpsiP hpsiM, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [cmode_eq]
    ring
  rw [hint_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
  have hB : 0 ≤ (N : ℝ) ^ (-σ - 2) := Real.rpow_nonneg hNpos.le _
  calc κ * ‖(∫ u in Ioi (N : ℝ), Complex.exp (2 * π * I * ((ν : ℂ) + 1) * (u : ℂ))
            * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2))
          + ∫ u in Ioi (N : ℝ), Complex.exp (-(2 * π * I * ((ν : ℂ) + 1) * (u : ℂ)))
            * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ κ * (8 / (π * ((ν : ℝ) + 1)) * (N : ℝ) ^ (-σ - 2)
          + 8 / (π * ((ν : ℝ) + 1)) * (N : ℝ) ^ (-σ - 2)) := by
        apply mul_le_mul_of_nonneg_left _ hκpos.le
        exact (norm_add_le _ _).trans (add_le_add hp hm)
    _ = 4 / π ^ 3 * (1 / ((ν : ℝ) + 1) ^ 3) * (N : ℝ) ^ (-σ - 2) := by
        rw [hκ]
        field_simp
        ring

/-- dominated convergence: the integral of (P + 1/12) u^{−s−2} is the sum of the mode integrals -/
lemma hasSum_mode_integrals {σ t : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun ν : ℕ => ∫ u in Ioi (N : ℝ), (cmode ν u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2))
      (∫ u in Ioi (N : ℝ), ((P u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 := re_w_lt hσ t
  have hsum2 : Summable (fun ν : ℕ => 1 / ((ν : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact h.congr (fun n => by push_cast; ring)
  refine hasSum_integral_of_dominated_convergence
    (fun ν u => 1 / (2 * π ^ 2) * (1 / ((ν : ℝ) + 1) ^ 2) * u ^ (-σ - 2)) ?_ ?_ ?_ ?_ ?_
  · intro ν
    exact (integrableOn_bdd_mul_cpow (continuous_cmode ν).measurable (cmode_abs_le ν) hNpos
      hw1).aestronglyMeasurable
  · intro ν
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun u hu => ?_)
    have hu0 : 0 < u := lt_trans hNpos hu
    show ‖(cmode ν u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 1 / (2 * π ^ 2) * (1 / ((ν : ℝ) + 1) ^ 2) * u ^ (-σ - 2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      re_w]
    exact mul_le_mul_of_nonneg_right (cmode_abs_le ν u) (Real.rpow_nonneg hu0.le _)
  · refine ae_of_all _ (fun u => ?_)
    exact (hsum2.mul_left _).mul_right _
  · simp_rw [tsum_mul_right]
    exact ((integrableOn_Ioi_rpow_iff hNpos).mpr (by linarith)).const_mul _
  · refine ae_of_all _ (fun u => ?_)
    exact (Complex.hasSum_ofReal.mpr (cmode_hasSum u)).mul_right _

/-- splitting P = (P + 1/12) − 1/12 under the integral -/
lemma split_P {σ t : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in Ioi (N : ℝ), (P u : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
      = (∫ u in Ioi (N : ℝ), ((P u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2))
        - (1 / 12 : ℂ) * ∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-(σ : ℂ) - t * I - 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 := re_w_lt hσ t
  have hg : Measurable (fun u : ℝ => P u + 1 / 12) := (continuous_P.add continuous_const).measurable
  have hintP : IntegrableOn (fun u : ℝ => ((P u + 1 / 12 : ℝ) : ℂ)
      * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) (Ioi (N : ℝ)) :=
    integrableOn_bdd_mul_cpow hg (c := 1) (fun u => by
      have h := abs_le.mp (P_abs_le u)
      rw [abs_le]; constructor <;> linarith [h.1, h.2]) hNpos hw1
  have hintJ : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_cpow_iff hNpos).mpr hw1
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hintP (hintJ.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  push_cast
  ring

/-- the exact value of ∫_N^∞ u^{−s−2} du -/
lemma integral_cpow_tail {σ t : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)
      = (N : ℂ) ^ (-(((σ : ℂ) + t * I) + 1)) / (((σ : ℂ) + t * I) + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [integral_Ioi_cpow_of_lt (re_w_lt hσ t) hNpos]
  have e1 : -(σ : ℂ) - t * I - 2 + 1 = -(((σ : ℂ) + t * I) + 1) := by ring
  rw [e1, neg_div_neg_eq, Complex.ofReal_natCast]

/-- **F.** The sharpened tail: |s ∫_N^∞ ψ(u) u^{−s−1} du| ≤ C N^{−σ} for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N. -/
theorem tail_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      ‖((σ : ℂ) + t * I) * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)‖
        ≤ C * (N : ℝ) ^ (-σ) := by
  have hsum3 : Summable (fun ν : ℕ => 1 / ((ν : ℝ) + 1) ^ 3) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
    exact h.congr (fun n => by push_cast; ring)
  have hπ : 0 < π := Real.pi_pos
  refine ⟨12 * (4 / π ^ 3 * ∑' ν : ℕ, 1 / ((ν : ℝ) + 1) ^ 3) + 1 / 4, ?_⟩
  intro σ t hσ₀σ hσ2 ht N hN htN
  have hσ : 0 < σ := lt_of_lt_of_le hσ₀ hσ₀σ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxt : t ≤ π * N := by nlinarith [Real.pi_gt_three]
  have hxt' : -t ≤ π * N := by nlinarith [Real.pi_gt_three]
  have hs : (0 : ℝ) < ((σ : ℂ) + t * I).re := by simp; exact hσ
  have hs1 : ((σ : ℂ) + t * I) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  -- E, then the decomposition of the P-integral
  have hE := tail_by_parts hs hN
  have hw' : -((σ : ℂ) + t * I) - 2 = -(σ : ℂ) - t * I - 2 := by ring
  rw [hw'] at hE
  have hT_eq := (hasSum_mode_integrals (t := t) hσ hN).tsum_eq
  have hkey : ((σ : ℂ) + t * I) *
      ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)
      = ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) + 1)
          * (∫ u in Ioi (N : ℝ), ((P u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2))
        - ((1 / 12 : ℝ) : ℂ) * (((σ : ℂ) + t * I) * (N : ℂ) ^ (-(((σ : ℂ) + t * I) + 1))) := by
    rw [hE, split_P hσ hN, integral_cpow_tail hσ hN, div_eq_mul_inv]
    have hinv : ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 1)⁻¹ = 1 := mul_inv_cancel₀ hs1
    push_cast
    linear_combination
      (-(1 / 12 : ℂ) * ((σ : ℂ) + t * I) * (N : ℂ) ^ (-(((σ : ℂ) + t * I) + 1))) * hinv
  rw [hkey]
  -- the pieces
  have hT_bound : ‖∫ u in Ioi (N : ℝ), ((P u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 4 / π ^ 3 * (∑' ν : ℕ, 1 / ((ν : ℝ) + 1) ^ 3) * (N : ℝ) ^ (-σ - 2) := by
    rw [← hT_eq]
    exact tsum_of_norm_bounded ((hsum3.hasSum.mul_left (4 / π ^ 3)).mul_right _)
      (mode_integral_bound hσ hN hxt hxt')
  have hs_norm : ‖(σ : ℂ) + t * I‖ ≤ 3 * N := by
    calc ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = σ + t := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hσ, abs_of_nonneg ht]
      _ ≤ 3 * N := by linarith
  have hs1_norm : ‖((σ : ℂ) + t * I) + 1‖ ≤ 4 * N := by
    calc ‖((σ : ℂ) + t * I) + 1‖ ≤ ‖(σ : ℂ) + t * I‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * N + 1 := by rw [norm_one]; linarith
      _ ≤ 4 * N := by linarith
  have hX_norm : ‖(N : ℂ) ^ (-(((σ : ℂ) + t * I) + 1))‖ = (N : ℝ) ^ (-σ - 1) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
    ring
  have hN2 : (N : ℝ) ^ (-σ - 2) = (N : ℝ) ^ (-σ) / (N : ℝ) ^ 2 := by
    rw [show -σ - 2 = -σ - ((2 : ℕ) : ℝ) by norm_num, Real.rpow_sub hNpos, Real.rpow_natCast]
  have hN1' : (N : ℝ) ^ (-σ - 1) = (N : ℝ) ^ (-σ) / N := by
    rw [Real.rpow_sub_one hNpos.ne']
  have hA : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hNpos.le _
  have hK : 0 ≤ ∑' ν : ℕ, 1 / ((ν : ℝ) + 1) ^ 3 := tsum_nonneg (fun ν => by positivity)
  set T := ∫ u in Ioi (N : ℝ), ((P u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2) with hT
  set X := (N : ℂ) ^ (-(((σ : ℂ) + t * I) + 1)) with hX
  set K := ∑' ν : ℕ, 1 / ((ν : ℝ) + 1) ^ 3 with hK_def
  calc ‖((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) + 1) * T
          - ((1 / 12 : ℝ) : ℂ) * (((σ : ℂ) + t * I) * X)‖
      ≤ ‖((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) + 1) * T‖
          + ‖((1 / 12 : ℝ) : ℂ) * (((σ : ℂ) + t * I) * X)‖ := norm_sub_le _ _
    _ = ‖(σ : ℂ) + t * I‖ * ‖((σ : ℂ) + t * I) + 1‖ * ‖T‖
          + 1 / 12 * (‖(σ : ℂ) + t * I‖ * ‖X‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
    _ ≤ (3 * N) * (4 * N) * (4 / π ^ 3 * K * (N : ℝ) ^ (-σ - 2))
          + 1 / 12 * ((3 * N) * (N : ℝ) ^ (-σ - 1)) := by
        rw [hX_norm]
        have hnn1 : 0 ≤ ‖T‖ := norm_nonneg _
        have hnn2 : 0 ≤ (N : ℝ) ^ (-σ - 1) := Real.rpow_nonneg hNpos.le _
        have h12 : ‖(σ : ℂ) + t * I‖ * ‖((σ : ℂ) + t * I) + 1‖ ≤ (3 * N) * (4 * N) :=
          mul_le_mul hs_norm hs1_norm (norm_nonneg _) (by positivity)
        have h3 : ‖(σ : ℂ) + t * I‖ * ‖((σ : ℂ) + t * I) + 1‖ * ‖T‖
            ≤ (3 * N) * (4 * N) * (4 / π ^ 3 * K * (N : ℝ) ^ (-σ - 2)) :=
          mul_le_mul h12 hT_bound hnn1 (by positivity)
        have h4 : ‖(σ : ℂ) + t * I‖ * (N : ℝ) ^ (-σ - 1) ≤ (3 * N) * (N : ℝ) ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right hs_norm hnn2
        linarith
    _ = (12 * (4 / π ^ 3 * K) + 1 / 4) * (N : ℝ) ^ (-σ) := by
        rw [hN2, hN1']
        field_simp
        ring

end NodeCF

section NodeD

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


end NodeD

section NodeG

/-! ## G. The approximate formula with the sharp error  (Titchmarsh Theorem 4.11, x = N ≥ t) -/

/-- ‖N^{−s}/2‖ = N^{−σ}/2 for s = σ + it and N ≥ 1. -/
lemma norm_natCast_cpow_neg_div_two {σ t : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    ‖(N : ℂ) ^ (-((σ : ℂ) + t * I)) / 2‖ = (N : ℝ) ^ (-σ) / 2 := by
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), RCLike.norm_two]
  have hre : (-((σ : ℂ) + t * I)).re = -σ := by simp
  rw [hre]

/-- **G.** The approximate formula with the sharp error term:
ζ(s) = S_N(s) + N^{1−s}/(s−1) + O(N^{−σ}) uniformly for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N, N ≥ 1, s ≠ 1. -/
theorem zeta_approx_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C * (N : ℝ) ^ (-σ) := by
  obtain ⟨C₀, hC₀⟩ := tail_sharp hσ₀
  refine ⟨C₀ + 1 / 2, ?_⟩
  intro σ t hσ₀σ hσ2 ht N hN htN hs1
  have hσ : 0 < σ := lt_of_lt_of_le hσ₀ hσ₀σ
  have hs : (0 : ℝ) < ((σ : ℂ) + t * I).re := by simp; exact hσ
  have hD := zeta_eq_euler_maclaurin hs hs1 hN
  have hF := hC₀ σ t hσ₀σ hσ2 ht N hN htN
  have hhalf := norm_natCast_cpow_neg_div_two (σ := σ) (t := t) hN
  have heq : riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)
      = -((N : ℂ) ^ (-((σ : ℂ) + t * I)) / 2)
        - ((σ : ℂ) + t * I)
          * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1) := by
    rw [hD]; ring
  rw [heq]
  calc ‖-((N : ℂ) ^ (-((σ : ℂ) + t * I)) / 2)
          - ((σ : ℂ) + t * I)
            * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)‖
      ≤ ‖-((N : ℂ) ^ (-((σ : ℂ) + t * I)) / 2)‖
          + ‖((σ : ℂ) + t * I)
            * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)‖ :=
        norm_sub_le _ _
    _ ≤ (N : ℝ) ^ (-σ) / 2 + C₀ * (N : ℝ) ^ (-σ) := by
        rw [norm_neg, hhalf]; exact add_le_add le_rfl hF
    _ = (C₀ + 1 / 2) * (N : ℝ) ^ (-σ) := by ring

/-! ### The segment specialisation: t ∈ [1, T], N = ⌈T⌉₊ -/

/-- For σ₁ > 1/2, T ≥ 2 and N := ⌈T⌉₊, every t ∈ [1, T] satisfies t ≤ N and s = σ + it ≠ 1, so
G holds uniformly on the segment σ₁ ≤ σ ≤ 2, t ∈ [1, T], with one constant C = C(σ₁). -/
theorem zeta_approx_sharp_segment {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∀ t ∈ Icc (1 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + t * I) - S ⌈T⌉₊ ((σ : ℂ) + t * I)
          - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C * (⌈T⌉₊ : ℝ) ^ (-σ) := by
  obtain ⟨C, hC⟩ := zeta_approx_sharp (σ₀ := σ₁) (by linarith)
  refine ⟨C, ?_⟩
  intro σ hσ₁ hσ2 T hT t ht
  have hN : 1 ≤ ⌈T⌉₊ := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < T by linarith)
    omega
  have htN : t ≤ ⌈T⌉₊ := ht.2.trans (Nat.le_ceil T)
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  exact hC σ t hσ₁ hσ2 (by linarith [ht.1]) ⌈T⌉₊ hN htN hs1

/-- The same with the error bounded by the constant alone (N^{−σ} ≤ 1 since N ≥ 1, σ ≥ 0),
as node I uses it: ζ = S_N + N^{1−s}/(s−1) + E with ‖E‖ ≤ C on the whole segment. -/
theorem zeta_approx_sharp_segment' {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∀ t ∈ Icc (1 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + t * I) - S ⌈T⌉₊ ((σ : ℂ) + t * I)
          - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C := by
  obtain ⟨C, hC⟩ := zeta_approx_sharp_segment h1
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro σ hσ₁ hσ2 T hT t ht
  have hN : 1 ≤ ⌈T⌉₊ := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < T by linarith)
    omega
  have hN1 : (1 : ℝ) ≤ ⌈T⌉₊ := by exact_mod_cast hN
  have hpow : (⌈T⌉₊ : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hpow0 : 0 ≤ (⌈T⌉₊ : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
  calc ‖riemannZeta ((σ : ℂ) + t * I) - S ⌈T⌉₊ ((σ : ℂ) + t * I)
          - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
      ≤ C * (⌈T⌉₊ : ℝ) ^ (-σ) := hC σ hσ₁ hσ2 T hT t ht
    _ ≤ max C 0 * (⌈T⌉₊ : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0
    _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max C 0 := mul_one _


end NodeG

section NodeI

/-! ## I. The goal: the uniform mean square for every σ₁ > 1/2 -/

/-- `S N (σ + it)` is the tree's `Dpoly σ N t` (coefficients `n^{−σ}`, twist `n^{−it}`). -/
lemma S_eq_Dpoly (σ : ℝ) (N : ℕ) (t : ℝ) :
    S N ((σ : ℂ) + t * I) = Zeta23.BL.M3.Dpoly σ N t := by
  unfold S Zeta23.BL.M3.Dpoly
  refine Finset.sum_congr rfl fun n hn => ?_
  exact M1.cpow_neg_add_eq n (Finset.mem_Icc.mp hn).1 σ t

/-- `‖N^{1−s}/(s−1)‖ ≤ N^{1−σ₁}/t` for `σ ≥ σ₁`, `t > 0`, `N ≥ 1` (the tree's `M2.norm_P_le`). -/
lemma norm_main_term_le {σ₁ σ t : ℝ} (hσ : σ₁ ≤ σ) (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) :
    ‖(N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
      ≤ (N : ℝ) ^ (1 - σ₁) / t := by
  have h := Zeta23.BL.M2.norm_P_le hσ ht hN
  rw [← neg_div_neg_eq, neg_sub]
  exact h

/-- The pointwise square bound from the sharp approximate formula: if
`‖ζ(s) − S_N(s) − N^{1−s}/(s−1)‖ ≤ C` then
`‖ζ(s)‖² ≤ 4‖Dpoly σ N t‖² + 4 N^{2−2σ₁}/t² + 4C²` (for `σ ≥ σ₁`, `t ≥ 1`, `N ≥ 1`). -/
lemma norm_zeta_sq_le_sharp {σ₁ σ t C : ℝ} (hσ : σ₁ ≤ σ) (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N)
    (hE : ‖riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖ ≤ C) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤
      4 * ‖Zeta23.BL.M3.Dpoly σ N t‖ ^ 2
        + 4 * (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + 4 * C ^ 2 := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  set Pm : ℂ := (N : ℂ) ^ (1 - s) / (s - 1) with hPm
  set E : ℂ := riemannZeta s - S N s - Pm with hEdef
  have hζ : riemannZeta s = S N s + Pm + E := by rw [hEdef]; ring
  have hP : ‖Pm‖ ≤ (N : ℝ) ^ (1 - σ₁) / t := norm_main_term_le hσ (by linarith) hN
  have hP2 : ‖Pm‖ ^ 2 ≤ (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ := by
    calc ‖Pm‖ ^ 2 ≤ ((N : ℝ) ^ (1 - σ₁) / t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
      _ = (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ := by
          rw [div_pow, Zeta23.BL.M2.rpow_sq_eq (Nat.cast_nonneg N) (a := 1 - σ₁)
            (b := 2 - 2 * σ₁) (by ring), div_eq_mul_inv]
  have hSD : S N s = Zeta23.BL.M3.Dpoly σ N t := S_eq_Dpoly σ N t
  have htri : ‖riemannZeta s‖ ≤ ‖S N s‖ + ‖Pm‖ + ‖E‖ := by
    rw [hζ]; exact norm_add₃_le
  have hsq : ‖riemannZeta s‖ ^ 2 ≤ (‖S N s‖ + ‖Pm‖ + ‖E‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hE2 : ‖E‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE 2
  have hA0 : 0 ≤ (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ := by positivity
  rw [hSD] at hsq
  nlinarith [sq_nonneg (‖Zeta23.BL.M3.Dpoly σ N t‖ - ‖Pm‖),
    sq_nonneg (‖Zeta23.BL.M3.Dpoly σ N t‖ - ‖E‖), sq_nonneg (‖Pm‖ - ‖E‖),
    sq_nonneg ‖Zeta23.BL.M3.Dpoly σ N t‖, sq_nonneg ‖Pm‖, sq_nonneg ‖E‖, sq_nonneg C]

/-- **The parametric mean square with the sharp error.** For `1/2 < σ₁ < 1` there is `C` such
that for all `σ₁ ≤ σ ≤ 2` and `T ≥ 2`, `∫₁ᵀ ‖ζ(σ+it)‖² ≤ C T`
(explicitly `C = 4(1 + 1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4 C_G²`, `C_G` the constant of G). -/
theorem meanSquare_sharp_param {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T := by
  obtain ⟨C, _hC0, hC⟩ := zeta_approx_sharp_segment' h1
  refine ⟨4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * C ^ 2, ?_⟩
  intro σ hσ hσ2 T hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  set N : ℕ := ⌈T⌉₊ with hNdef
  have hN : 1 ≤ N := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < T by linarith)
    omega
  have hNT : (N : ℝ) ≤ 2 * T := by
    have := Nat.ceil_lt_add_one hT0
    linarith
  have hA0 : 0 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hK0 : 0 ≤ 4 * C ^ 2 := by positivity
  have hpt : ∀ t ∈ Icc (1:ℝ) T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 4 * ‖Zeta23.BL.M3.Dpoly σ N t‖ ^ 2 + 4 * (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹
        + 4 * C ^ 2 :=
    fun t ht => norm_zeta_sq_le_sharp hσ ht.1 hN (hC σ hσ hσ2 T hT t ht)
  have hmain := Zeta23.BL.M3.integral_bound_abstract hT1 hA0 hK0 hpt
  have hs1 : ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) ≤ 1 + 1 / (2 * σ₁ - 1) := by
    refine le_trans ?_ (M1.sum_rpow_neg_le σ₁ h1 N)
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hs2 : ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (1 + (N:ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁)) := by
    refine le_trans ?_ (M1.sum_weight_le_logfree σ₁ h1 h2 N)
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (by linarith)
  have hNpow : (N:ℝ) ^ (2 - 2 * σ₁) ≤ 2 * T := by
    have he0 : 0 ≤ 2 - 2 * σ₁ := by linarith
    calc (N:ℝ) ^ (2 - 2 * σ₁) ≤ (2 * T) ^ (2 - 2 * σ₁) :=
          Real.rpow_le_rpow (Nat.cast_nonneg N) hNT he0
      _ = 2 ^ (2 - 2 * σ₁) * T ^ (2 - 2 * σ₁) := Real.mul_rpow (by norm_num) hT0
      _ ≤ 2 ^ (1:ℝ) * T ^ (1:ℝ) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          · exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
          · exact Real.rpow_nonneg hT0 _
          · exact Real.rpow_nonneg (by norm_num) _
      _ = 2 * T := by rw [Real.rpow_one, Real.rpow_one]
  have hTs1 := mul_le_mul_of_nonneg_left hs1 hT0
  have hdiv : (N:ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁) ≤ 2 * T / (2 - 2 * σ₁) :=
    div_le_div_of_nonneg_right hNpow (by linarith)
  have hE : 2 * T / (2 - 2 * σ₁) = (2 / (2 - 2 * σ₁)) * T := by ring
  rw [hE] at hdiv
  have hfin : 4 * (T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
      + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ))
      + 4 * (N:ℝ) ^ (2 - 2 * σ₁) + 4 * C ^ 2 * T
      ≤ (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * C ^ 2) * T := by
    have e : (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * C ^ 2) * T
        = 4 * (T * (1 + 1 / (2 * σ₁ - 1))) + 112 * T + 208 * ((2 / (2 - 2 * σ₁)) * T)
          + 4 * C ^ 2 * T := by ring
    rw [e]
    linarith
  exact hmain.trans hfin

/-- The uniform mean square for all `σ ≥ σ₁`, when `1/2 < σ₁ < 1`: the segment `σ ≤ 2` from
`meanSquare_sharp_param`, the rest from the tree's trivial bound `meanSquare_hyp_extend`. -/
theorem meanSquareUnif_all_of_lt_one {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T := by
  obtain ⟨C, hC⟩ := meanSquare_sharp_param h1 h2
  exact ⟨_, Zeta23.BL.meanSquare_hyp_extend (σ₂ := 2) (by norm_num) hC⟩

/-- **I. The goal.** The uniform mean square for every `σ₁ > 1/2`
(Hardy–Littlewood, Titchmarsh Theorem 7.2(A)). -/
theorem meanSquareUnif_all {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T := by
  obtain ⟨C, hC⟩ := meanSquareUnif_all_of_lt_one (σ₁ := min σ₁ (3 / 4))
    (lt_min h1 (by norm_num)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  exact ⟨C, fun σ hσ T hT => hC σ (le_trans (min_le_left _ _) hσ) T hT⟩

/-- The same in the tree's shape `Zeta23.BL.M3.MeanSquareUnifFrom σ₁` (definitionally the
statement of `meanSquareUnif_all`). -/
theorem meanSquareUnifFrom_all {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) :
    Zeta23.BL.M3.MeanSquareUnifFrom σ₁ :=
  meanSquareUnif_all h1

/-- Bohr–Landau for the right half-strip, every `δ > 0`: from the tree's J8
`Zeta23.BL.rightHalf_of_meanSquareUnif` with `σ₁ := 1/2 + min δ (1/4) / 2`. -/
theorem rightHalfBound : Zeta23.BL.RightHalfBound := by
  intro δ hδ
  have hmin0 : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hmin1 : min δ (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hminδ : min δ (1 / 4) ≤ δ := min_le_left _ _
  have h1 : 1 / 2 < 1 / 2 + min δ (1 / 4) / 2 := by linarith
  have h2 : 1 / 2 + min δ (1 / 4) / 2 < 1 := by linarith
  have hδσ : 1 / 2 + min δ (1 / 4) / 2 - 1 / 2 < δ := by linarith
  exact Zeta23.BL.rightHalf_of_meanSquareUnif h1 h2 (meanSquareUnifFrom_all h1) δ hδσ

/-- **Bohr–Landau** (MNF's statement `MNF.RH.BohrLandau`): the zeros with `|Re ρ − 1/2| ≥ δ`,
`0 < Im ρ ≤ T`, counted with multiplicity, are `O(T)` for every `δ > 0`. -/
theorem bohrLandau_all : MNF.RH.BohrLandau :=
  Zeta23.BL.bohrLandau_of_right rightHalfBound

end NodeI

end BLClosure

/-! # CLOSE — the tree's statements from node I -/

section CLOSEpart

open Complex Real MeasureTheory intervalIntegral Set

namespace Zeta23.BL
open MNF.RH

/-- **Bohr–Landau for the right half-strip, every `δ > 0`.**  For `δ ≥ 1/2` the count is `0`
(`NRight_eq_zero_of_half_le`); for `0 < δ < 1/2` apply J8 (`rightHalf_of_meanSquareUnif`) with
`σ₁ := 1/2 + δ/2 ∈ (1/2, 3/4)` and node I's `MeanSquareUnifFrom σ₁`. -/
theorem rightHalf_all : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T := by
  intro δ hδ
  rcases le_or_gt (1 / 2) δ with hδ2 | hδ2
  · exact ⟨0, fun T _ => by rw [NRight_eq_zero_of_half_le hδ2]; simp⟩
  · have h1 : 1 / 2 < 1 / 2 + δ / 2 := by linarith
    have h2 : 1 / 2 + δ / 2 < 1 := by linarith
    have hδσ : 1 / 2 + δ / 2 - 1 / 2 < δ := by linarith
    exact rightHalf_of_meanSquareUnif h1 h2 (BLClosure.meanSquareUnifFrom_all h1) δ hδσ

/-- `RightHalfBound` (the definition of `Zeta23/BohrLandau.lean`), unconditionally. -/
theorem rightHalfBound : RightHalfBound := rightHalf_all

/-- **Bohr–Landau** (`MNF.RH.BohrLandau`), unconditionally, through the tree's sorry-free
reduction `bohrLandau_of_right`. -/
theorem bohrLandau_full : MNF.RH.BohrLandau := bohrLandau_of_right rightHalfBound

set_option linter.unusedVariables false in
/-- The shape of the sorried `Zeta23.BL.rightHalfBound_of_meanSquare` of `Zeta23/BohrLandau.lean`.
The hypothesis `h : ZetaMeanSquare` is NOT used: the conclusion is `rightHalfBound` above, which
goes through node I's `∫₁ᵀ` mean square and J8, not through the `∫₀ᵀ` statement `ZetaMeanSquare`. -/
theorem rightHalfBound_of_meanSquare' (h : ZetaMeanSquare) : RightHalfBound := rightHalfBound

/-- The verbatim shape of the sorried `Zeta23.BL.meanSquare_strip` of `Zeta23/BohrLandau.lean`:
`∫₀ᵀ ‖ζ(σ+it)‖² ≤ C T` for `T ≥ 2`, `1/2 < σ ≤ 1`.  For `σ < 1`: `∫₀ᵀ = ∫₀¹ + ∫₁ᵀ`, the first by
M45's patch `meanSquare_zero_one`, the second by node I's `meanSquareUnif_all` (with `σ₁ := σ`).
**Caveat at `σ = 1`** (repeated from M45's `meanSquare_one`): there the statement holds only
vacuously, because the integrand is not interval-integrable on `[0, T]`
(`M45.not_intervalIntegrable_zeta_one_sq`: ζ has its pole at `t = 0`), so Mathlib's Bochner
interval integral is `0` by the junk-value convention (`M45.integral_zeta_one_sq_eq_zero`) and the
inequality says nothing about ζ; the genuine `σ = 1` content is M45's `meanSquare_one_from_one`
on `[1, T]` (and node I's `meanSquareUnif_all` at any `σ₁ ≤ 1`). -/
theorem meanSquare_strip' {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact M45.meanSquare_one
  · obtain ⟨C, hC⟩ := BLClosure.meanSquareUnif_all h1
    refine ⟨(1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 + C, fun T hT => ?_⟩
    have hcont := M45.continuous_norm_zeta_sq (σ := σ) hlt.ne
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 1)
      (hcont.intervalIntegrable 1 T)]
    have hA := M45.meanSquare_zero_one (by linarith) hlt
    have hB := hC σ le_rfl T hT
    have hB0 : 0 ≤ (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 := sq_nonneg _
    have hBT : (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 ≤ (1 / 2 + 1 / (1 - σ) + 2 / σ) ^ 2 * T :=
      le_mul_of_one_le_right hB0 (by linarith)
    linarith

end Zeta23.BL

namespace MNF.RH

/-- **`ReservoirDensityOne`, unconditionally**: at every threshold `δ > 0`, all but a vanishing
proportion of the zeros lie within `δ` of the line (Bohr–Landau for every `δ > 0` plus the
superlinear growth of `N(0,T)`). -/
theorem reservoirDensityOne_unconditional : ReservoirDensityOne :=
  reservoirDensityOne_of_bohrLandau Zeta23.BL.bohrLandau_full

/-- **Density one on the line from a spectral gap alone**: a gap at any `Δ > 0` gives
`OnLineDensityOne`, with no other hypothesis (Bohr–Landau is now unconditional). -/
theorem onLineDensityOne_of_gap_only {Δ : ℝ} (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) :
    OnLineDensityOne :=
  onLineDensityOne_of_gap Zeta23.BL.bohrLandau_full hΔ hgap

end MNF.RH

end CLOSEpart

/-! # Contract statements NOT proved by any node — kept as `sorry`, CLEARLY MARKED.

Nothing above depends on these.  A and A′ are the contract's original forms (F' monotone, G
antitone); the nodes proved the smooth strengthenings `first_derivative_test_smooth` /
`first_derivative_test_amp_smooth` above, which is all the downstream chain uses.  H was not
assigned to any node (the contract: "proved in the author's tree; a proof is welcome but not
required"). -/

section ContractNotProved

open Complex Real MeasureTheory intervalIntegral Set

namespace BLClosure

/-- **A (contract form, UNPROVED — sorry).** -/
theorem first_derivative_test {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (F F' : ℝ → ℝ)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (hmono : MonotoneOn F' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, lam ≤ F' x) :
    ‖∫ x in a..b, Complex.exp (I * (F x : ℂ))‖ ≤ 4 / lam := by
  sorry -- UNPROVED: no node attacked the monotone form; see first_derivative_test_smooth

/-- **A′ (contract form, UNPROVED — sorry).** -/
theorem first_derivative_test_amp {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (F F' G : ℝ → ℝ)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (hmono : MonotoneOn F' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, lam ≤ F' x) (hG : AntitoneOn G (Icc a b))
    (hG0 : ∀ x ∈ Icc a b, 0 ≤ G x) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  sorry -- UNPROVED: no node attacked the antitone form; see first_derivative_test_amp_smooth

/-- **H (contract, UNPROVED — sorry; not assigned to any node).** -/
theorem dirichlet_mean_value (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log ((n : ℝ) / m)|)) := by
  sorry -- UNPROVED: not assigned to any node

/-- **H′ (contract, UNPROVED — sorry; not assigned to any node).** -/
theorem offdiag_pow_bound {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m = n then 0 else (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) * (2 / |Real.log ((n : ℝ) / m)|))
        ≤ C * (N : ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  sorry -- UNPROVED: not assigned to any node

end BLClosure

end ContractNotProved

/-! # Axiom audit: every theorem and lemma of this file -/

#print axioms BLClosure.hasSum_cos_div_sq_bernoulli
#print axioms BLClosure.cos_mode_fract
#print axioms BLClosure.B2per_fourier
#print axioms BLClosure.P_fourier
#print axioms BLClosure.P_nonpos
#print axioms BLClosure.P_intCast
#print axioms BLClosure.P_eq
#print axioms BLClosure.psi_abs_le
#print axioms BLClosure.P_abs_le
#print axioms BLClosure.P_natCast
#print axioms BLClosure.continuous_P
#print axioms BLClosure.measurable_psi
#print axioms BLClosure.hasDerivAt_P
#print axioms BLClosure.integrableOn_bdd_mul_cpow
#print axioms BLClosure.integrableOn_psi_mul
#print axioms BLClosure.integrableOn_P_mul
#print axioms BLClosure.tail_by_parts_interval
#print axioms BLClosure.tail_by_parts
#print axioms BLClosure.hasDerivAt_P'
#print axioms BLClosure.first_derivative_test_amp_smooth'
#print axioms BLClosure.first_derivative_test_amp_smooth
#print axioms BLClosure.first_derivative_test_smooth
#print axioms BLClosure.mode_integrand_eq
#print axioms BLClosure.mode_bound_interval
#print axioms BLClosure.integrableOn_bdd_mul_cpow'
#print axioms BLClosure.integrableOn_exp_mul_cpow
#print axioms BLClosure.integrableOn_exp_neg_mul_cpow
#print axioms BLClosure.re_w
#print axioms BLClosure.re_w_lt
#print axioms BLClosure.re_phase
#print axioms BLClosure.re_phase'
#print axioms BLClosure.tail_mode_bound'
#print axioms BLClosure.tail_mode_bound
#print axioms BLClosure.tail_mode_bound_neg
#print axioms BLClosure.cmode_hasSum
#print axioms BLClosure.continuous_cmode
#print axioms BLClosure.cmode_abs_le
#print axioms BLClosure.cmode_eq
#print axioms BLClosure.mode_integral_bound
#print axioms BLClosure.hasSum_mode_integrals
#print axioms BLClosure.split_P
#print axioms BLClosure.integral_cpow_tail
#print axioms BLClosure.tail_sharp
#print axioms BLClosure.zeta_eq_euler_maclaurin
#print axioms BLClosure.norm_natCast_cpow_neg_div_two
#print axioms BLClosure.zeta_approx_sharp
#print axioms BLClosure.zeta_approx_sharp_segment
#print axioms BLClosure.zeta_approx_sharp_segment'
#print axioms BLClosure.S_eq_Dpoly
#print axioms BLClosure.norm_main_term_le
#print axioms BLClosure.norm_zeta_sq_le_sharp
#print axioms BLClosure.meanSquare_sharp_param
#print axioms BLClosure.meanSquareUnif_all_of_lt_one
#print axioms BLClosure.meanSquareUnif_all
#print axioms BLClosure.meanSquareUnifFrom_all
#print axioms BLClosure.rightHalfBound
#print axioms BLClosure.bohrLandau_all
#print axioms Zeta23.BL.rightHalf_all
#print axioms Zeta23.BL.rightHalfBound
#print axioms Zeta23.BL.bohrLandau_full
#print axioms Zeta23.BL.rightHalfBound_of_meanSquare'
#print axioms Zeta23.BL.meanSquare_strip'
#print axioms MNF.RH.reservoirDensityOne_unconditional
#print axioms MNF.RH.onLineDensityOne_of_gap_only
#print axioms BLClosure.first_derivative_test
#print axioms BLClosure.first_derivative_test_amp
#print axioms BLClosure.dirichlet_mean_value
#print axioms BLClosure.offdiag_pow_bound
