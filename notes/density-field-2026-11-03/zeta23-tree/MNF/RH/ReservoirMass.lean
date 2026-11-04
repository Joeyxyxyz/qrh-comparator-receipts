/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE RESERVOIR MASS: Σ_ρ m(ρ)·|Re ρ − 1/2| OVER 0 < Im ρ ≤ T
(MNF/RH/ReservoirMass.lean, on the zeta23 tree)
[PROVED | this tree]
Register: everything below is proved on this tree from Mathlib and the tree's sorry-free
files (`Zeta23.BL.BohrLandauClosure`, `Zeta23.BL.BohrLandauPartial`, `Zeta23.BohrLandau`,
`Zeta23.Final` / `Zeta23.Superlinear`, `MNF.RH.GapDensity`); no new hypothesis, no sorry;
axioms audited from `MNF_AuditDensity.lean` at the tree root (propext, Classical.choice,
Quot.sound only).
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e).

THE OBJECT.  For T > 0 let

    reservoirMass T := Σ_{ρ ∈ zerosIn 0 T} m(ρ) · |Re ρ − 1/2|           (ℝ-valued, `∑ᶠ`),

the multiplicity-weighted total distance of the nontrivial zeros with 0 < Im ρ ≤ T from the
critical line (m = `zeta_order`, the window is finite by `zerosIn_finite`).  Vocabulary: MNF is
the name of the framework this library is written for, and "reservoir" is its word for the
zeros off the critical line (Re ρ ≠ 1/2); so the reservoir mass is just the total displacement
of the zeros from the line, and `NOff δ 0 T` below is the number (with multiplicity) of zeros at
distance ≥ δ from it.  Neither word is standard terminology.  The mass is 0 for all T if and
only if RH holds — a remark on the definition, not a theorem of this file, and nothing below
bears on it.

WHAT IS PROVED (all unconditional).
  * Layer cake (`reservoirMass_eq_integral`): reservoirMass T = ∫₀^{1/2} N_off(δ; 0, T) dδ,
    where N_off(δ; 0, T) = `NOff δ 0 T` counts, with multiplicity, the zeros at distance ≥ δ from the line
    (each distance is < 1/2 because 0 < Re ρ < 1).  δ ↦ N_off(δ) is antitone, hence interval
    integrable on every [a, b], so the integral splits at any δ₀ (`integral_NOff_split`) with
    head ≤ δ₀·N(0,T) and tail ≤ (1/2 − δ₀)·N_off(δ₀) (`reservoirMass_le_split`).  Trivially
    0 ≤ reservoirMass T ≤ (1/2)·N(0,T).
  * Symmetry (`signedReservoir_eq_zero`, `reservoirMass_eq_two_right`): the reflection
    ρ ↦ 1 − ρ̄ is a multiplicity-preserving involution of every window, so the SIGNED sum
    Σ m(ρ)(Re ρ − 1/2) is 0 and the mass is twice the right-half signed mass
    2·Σ_{Re ρ > 1/2} m(ρ)(Re ρ − 1/2).  (This is only the functional-equation symmetry — the
    sign-symmetry statement MNF calls its "sign gate" — in count form: it says nothing about
    whether the right-half mass is 0.)
  * Explicit mean square (`meanSquare_explicit_small_B`): with the approximate-formula constant
    taken once at σ₀ = 1/2 (`CG`, from the tree's existential `BLClosure.zeta_approx_sharp`;
    the one ingredient that is not a numeral) and meanSquareB := 951 + 4·CG²,
      ∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ (4/(2σ₁−1) + meanSquareB)·T   for 1/2 < σ₁ ≤ 3/4, σ ≥ σ₁, T ≥ 2,
    i.e. the diagonal 1/(2σ₁ − 1) is the only σ₁-dependence left.
  * Explicit Bohr–Landau (`bohrLandau_explicit`): with A₀ := 54 + (27/2)·meanSquareB + 12·log 3,
      N_off(δ; 0, T) ≤ (2A₀·δ^{−5/2} + N(0,4))·T   for 0 < δ ≤ 1/2, T ≥ 2,
    by running the tree's Jensen-window argument (`count_le_meanSquare'`) at σ₁ = 1/2 + δ/2,
    where hwin ≥ √δ/4 and log(Rout/rin) ≥ δ/6.
  * Riemann–von Mangoldt in the shape N(0,T) ≍ T log T (`Ncount_le_mul_log`,
    `mul_log_le_Ncount`): N(0,T) ≤ 4A₀'·T log T for T ≥ 3 and N(0,T) ≥ T log T/(16π) for
    T ≥ an explicit T₀, from the `local_count` and `main` fields of the tree's
    `riemannVonMangoldt_zeta`.  Here A₀' ≥ 1 is the unit-window constant of `local_count`: an
    existential constant of the tree, not a numeral, and not the A₀ of §2.
  * THE BOUND (`reservoirMass_le_rpow`, `reservoirMass_le_Ncount_mul`,
    `meanDisplacement_tendsto_zero`): splitting the layer cake at δ₀ = (log T)^{−2/5},
      reservoirMass T ≤ A · T · (log T)^{3/5}                       (T ≥ T₀),
      reservoirMass T ≤ A · (log T)^{−2/5} · N(0,T)                  (T ≥ T₀),
      reservoirMass T / N(0,T) → 0                                   (T → ∞):
    the multiplicity-weighted MEAN distance of the zeros from the critical line tends to 0, at
    rate (log T)^{−2/5}.  In the first bound A = C + (2/3)·2A₀ + N(0,4)/2 with C = 4A₀' from
    `Ncount_le_mul_log`, so A is explicit up to the two existential constants CG and A₀'; the
    constant of the second bound is 16π·|A|; the Lean statements only assert ∃ A.  N(0,4) is a
    fixed natural number (in fact 0, the lowest zero having Im ρ ≈ 14.13, but that is not proved
    here).

WHAT THIS IS NOT.  The bound T (log T)^{3/5} is far weaker than what is classically known for
the same sum: Littlewood (1924) proved Σ_{0<Im ρ≤T} |Re ρ − 1/2| = O(T log log T), and Selberg
(1946) proved it is O(T) — both from zero-density arguments (Littlewood's via Littlewood's lemma
and mean-value estimates for ζ near the line, Selberg's via his mollified mean value; cf.
Titchmarsh, Chapter IX) that are not on this tree.  What is new here is only that the statement
is FORMALISED, with a constant explicit up to `CG` and the unit-window constant A₀' of §3, from
the Bohr–Landau route available on the tree (whose δ^{−5/2} dependence is the reason for the
exponent 3/5: a bound N_off(δ) ≪ T/δ^{a} gives T (log T)^{(a−1)/a}; a bound of the classical shape
T/δ, up to logarithms in 1/δ, would give only T log T, no better than the trivial (1/2)N(0,T);
the gain over the trivial bound here is the factor (log T)^{−2/5}, nothing more).  Nothing here bears on the gap
hypothesis `SpectralGapHyp`: a vanishing mean distance is consistent with infinitely many zeros
off the line (indeed with zeros at any fixed distance, as long as they are rare), and no
statement below implies, or is implied by, a zero-free strip of any width.  Nothing here uses
the 7/8 theorem.  The conclusion `meanDisplacement_tendsto_zero` follows from RH (where the mass
is 0) and is not known to imply anything about it.

Layout.  §1 the explicit mean square (namespace `Zeta23.BL`); §2 the explicit Bohr–Landau
constant (`Zeta23.BL`); §3 the Riemann–von Mangoldt bounds (`Zeta23`, restated for
`MNF.RH.Ncount`, which is definitionally `Zeta23.Ncount`); §4 the reservoir mass and the layer
cake (`MNF.RH`); §5 the reflection symmetry (`MNF.RH`); §6 the bound (`MNF.RH`); then a note
on the axiom audit.
-/
import Mathlib
import Zeta23.BL.BohrLandauClosure
import Zeta23.BohrLandau
import Zeta23.Superlinear
import Zeta23.RvM.NcountWindow
import MNF.RH.GapDensity
import MNF.RH.Counting

set_option maxHeartbeats 400000

/-! # §1 The explicit mean square: the approximate-formula constant taken once at σ₀ = 1/2 -/

section MeanSquareExplicit

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real ComplexConjugate

namespace Zeta23.BL

/-! ## The approximate-formula constant, once and for all at σ₀ = 1/2 -/

lemma one_half_pos' : (0 : ℝ) < 1 / 2 := by norm_num

/-- The constant of `BLClosure.zeta_approx_sharp` at `σ₀ = 1/2`, made nonnegative. -/
noncomputable def CG : ℝ :=
  max (Classical.choose (BLClosure.zeta_approx_sharp (σ₀ := 1 / 2) one_half_pos')) 0

lemma CG_nonneg : 0 ≤ CG := le_max_right _ _

/-- `CG` bounds the error of the approximate formula on `1/2 ≤ σ ≤ 2`, `0 ≤ t ≤ N`, `N ≥ 1`:
‖ζ(s) − S_N(s) − N^{1−s}/(s−1)‖ ≤ CG · N^{−σ}. -/
lemma CG_spec : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ CG * (N : ℝ) ^ (-σ) := by
  intro σ t hσ hσ2 ht N hN htN hs1
  have h := Classical.choose_spec (BLClosure.zeta_approx_sharp (σ₀ := 1 / 2) one_half_pos')
    σ t hσ hσ2 ht N hN htN hs1
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _))

/-- The segment specialisation of `CG_spec` (the shape of
`BLClosure.zeta_approx_sharp_segment'`, with the uniform constant): on `1/2 ≤ σ ≤ 2`, `T ≥ 2`,
`t ∈ [1, T]`, `N = ⌈T⌉₊`, the error is at most `CG`. -/
theorem zeta_approx_segment_half : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T →
    ∀ t ∈ Icc (1 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S ⌈T⌉₊ ((σ : ℂ) + t * I)
          - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ CG := by
  intro σ hσ hσ2 T hT t ht
  have hN : 1 ≤ ⌈T⌉₊ := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < T by linarith)
    omega
  have htN : t ≤ ⌈T⌉₊ := ht.2.trans (Nat.le_ceil T)
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  have hC := CG_spec σ t hσ hσ2 (by linarith [ht.1]) ⌈T⌉₊ hN htN hs1
  have hN1 : (1 : ℝ) ≤ ⌈T⌉₊ := by exact_mod_cast hN
  have hpow : (⌈T⌉₊ : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  calc ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S ⌈T⌉₊ ((σ : ℂ) + t * I)
          - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
      ≤ CG * (⌈T⌉₊ : ℝ) ^ (-σ) := hC
    _ ≤ CG * 1 := mul_le_mul_of_nonneg_left hpow CG_nonneg
    _ = CG := mul_one _

/-! ## The parametric mean square with the uniform constant -/

/-- `BLClosure.meanSquare_sharp_param` with the uniform constant `CG`: for `1/2 < σ₁ < 1`,
`σ₁ ≤ σ ≤ 2`, `T ≥ 2`,
`∫₁ᵀ ‖ζ(σ+it)‖² ≤ (4(1 + 1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4 CG²) T`. -/
theorem meanSquare_sharp_param_half {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) :
    ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2
        ≤ (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * CG ^ 2) * T := by
  intro σ hσ hσ2 T hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hσhalf : 1 / 2 ≤ σ := le_trans h1.le hσ
  set N : ℕ := ⌈T⌉₊ with hNdef
  have hN : 1 ≤ N := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < T by linarith)
    omega
  have hNT : (N : ℝ) ≤ 2 * T := by
    have := Nat.ceil_lt_add_one hT0
    linarith
  have hA0 : 0 ≤ (N:ℝ) ^ (2 - 2 * σ₁) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hK0 : 0 ≤ 4 * CG ^ 2 := by positivity
  have hpt : ∀ t ∈ Icc (1:ℝ) T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2
      ≤ 4 * ‖Zeta23.BL.M3.Dpoly σ N t‖ ^ 2 + 4 * (N:ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹
        + 4 * CG ^ 2 :=
    fun t ht => BLClosure.norm_zeta_sq_le_sharp hσ ht.1 hN
      (zeta_approx_segment_half σ hσhalf hσ2 T hT t ht)
  have hmain := Zeta23.BL.M3.integral_bound_abstract hT1 hA0 hK0 hpt
  have hs1 : ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) ≤ 1 + 1 / (2 * σ₁ - 1) := by
    refine le_trans ?_ (_root_.M1.sum_rpow_neg_le σ₁ h1 N)
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hs2 : ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
      ≤ 2 * (1 + (N:ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁)) := by
    refine le_trans ?_ (_root_.M1.sum_weight_le_logfree σ₁ h1 h2 N)
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
      + 4 * (N:ℝ) ^ (2 - 2 * σ₁) + 4 * CG ^ 2 * T
      ≤ (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * CG ^ 2) * T := by
    have e : (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * CG ^ 2) * T
        = 4 * (T * (1 + 1 / (2 * σ₁ - 1))) + 112 * T + 208 * ((2 / (2 - 2 * σ₁)) * T)
          + 4 * CG ^ 2 * T := by ring
    rw [e]
    linarith
  exact hmain.trans hfin

/-! ## The trivial bound for σ > 2: ζ(2)² = (π²/6)² ≤ 3 -/

/-- `ζ(2)² = (π²/6)² ≤ 3` (in the shape of the constant of `Zeta23.BL.meanSquare_of_gt_one`
at `σ₂ = 2`). -/
lemma tsum_one_div_rpow_two_sq_le : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) ^ 2 ≤ 3 := by
  have hz : ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) = π ^ 2 / 6 := by
    have hfun : (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) = fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 := by
      funext n; rw [Real.rpow_two]
    rw [hfun]; exact hasSum_zeta_two.tsum_eq
  rw [hz]
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hπ' : π < 315 / 100 := by norm_num at hπ ⊢; linarith
  have hπ0 : 0 < π := Real.pi_pos
  have hπ2 : π ^ 2 < 10 := by nlinarith
  have h4 : (π ^ 2 / 6) ^ 2 = π ^ 2 * π ^ 2 / 36 := by ring
  rw [h4]
  have hsq : π ^ 2 * π ^ 2 < 10 * 10 := mul_self_lt_mul_self (sq_nonneg _) hπ2
  linarith

/-! ## The explicit constant and the main statements -/

/-- The σ₁-independent part of the mean-square constant: `B = 951 + 4 CG²`,
`951 = 4 + 112 + 832 + 3` (diagonal `4`, off-diagonal `112 + 416/(2−2σ₁) ≤ 112 + 832` for
`σ₁ ≤ 3/4`, and `ζ(2)² ≤ 3` for `σ > 2`). -/
noncomputable def meanSquareB : ℝ := 951 + 4 * CG ^ 2

lemma meanSquareB_nonneg : 0 ≤ meanSquareB := by
  unfold meanSquareB; positivity

/-- **The explicit mean square, with the named constant.** For `1/2 < σ₁ ≤ 3/4`, all `σ ≥ σ₁` and `T ≥ 2`,
`∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ (4/(2σ₁−1) + meanSquareB) T`. -/
theorem meanSquare_explicit_small_B : ∀ σ₁ : ℝ, 1 / 2 < σ₁ → σ₁ ≤ 3 / 4 →
    ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2
        ≤ (4 / (2 * σ₁ - 1) + meanSquareB) * T := by
  intro σ₁ h1 h34 σ hσ T hT
  have hT0 : 0 ≤ T := by linarith
  have hd : 0 < 2 * σ₁ - 1 := by linarith
  have hd4 : 0 ≤ 4 / (2 * σ₁ - 1) := by positivity
  have hCG2 : 0 ≤ 4 * CG ^ 2 := by positivity
  rcases le_or_gt σ 2 with hσ2 | hσ2
  · have h := meanSquare_sharp_param_half h1 (by linarith) σ hσ hσ2 T hT
    have h416 : 416 / (2 - 2 * σ₁) ≤ 832 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hconst : 4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * CG ^ 2
        ≤ 4 / (2 * σ₁ - 1) + meanSquareB := by
      unfold meanSquareB
      have e : 4 * (1 + 1 / (2 * σ₁ - 1)) = 4 + 4 / (2 * σ₁ - 1) := by ring
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hconst hT0)
  · have h := Zeta23.BL.meanSquare_of_gt_one (σ₂ := 2) (by norm_num) hσ2.le
      (by linarith : (1:ℝ) ≤ T)
    have hZ := tsum_one_div_rpow_two_sq_le
    have hconst : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) ^ 2 ≤ 4 / (2 * σ₁ - 1) + meanSquareB := by
      unfold meanSquareB; linarith
    exact h.trans (mul_le_mul_of_nonneg_right hconst hT0)

/-- **The explicit mean square.** Explicit mean-square constant for `σ₁` near `1/2`: there is `B ≥ 0` (namely
`meanSquareB = 951 + 4 CG²`, `CG` the approximate-formula constant at `σ₀ = 1/2`) with
`∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ (4/(2σ₁−1) + B) T` for all `1/2 < σ₁ ≤ 3/4`, `σ ≥ σ₁`, `T ≥ 2`. -/
theorem meanSquare_explicit_small : ∃ B : ℝ, 0 ≤ B ∧ ∀ σ₁ : ℝ, 1 / 2 < σ₁ → σ₁ ≤ 3 / 4 →
    ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * Complex.I)‖ ^ 2
        ≤ (4 / (2 * σ₁ - 1) + B) * T :=
  ⟨meanSquareB, meanSquareB_nonneg, meanSquare_explicit_small_B⟩

/-- **The explicit mean square, specialised** to `σ₁ = 1/2 + δ/2` (`2σ₁ − 1 = δ`), `0 < δ ≤ 1/2`, with the same
constant `meanSquareB`: `∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ (4/δ + meanSquareB) T` for all
`σ ≥ 1/2 + δ/2`, `T ≥ 2`. -/
theorem meanSquareUnifFrom_explicit (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ σ : ℝ, 1 / 2 + δ / 2 ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * Complex.I)‖ ^ 2
        ≤ (4 / δ + meanSquareB) * T := by
  intro σ hσ T hT
  have h := meanSquare_explicit_small_B (1 / 2 + δ / 2) (by linarith) (by linarith) σ hσ T hT
  have e : 2 * (1 / 2 + δ / 2) - 1 = δ := by ring
  rw [e] at h
  exact h

/-- The same in the tree's shape `Zeta23.BL.M3.MeanSquareUnifFrom (1/2 + δ/2)`, with the
explicit constant `4/δ + meanSquareB`. -/
theorem meanSquareUnifFrom_explicit' (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    Zeta23.BL.M3.MeanSquareUnifFrom (1 / 2 + δ / 2) :=
  ⟨4 / δ + meanSquareB, meanSquareUnifFrom_explicit δ hδ hδ'⟩

end Zeta23.BL

end MeanSquareExplicit

/-! # §2 The explicit Bohr–Landau constant: N_off(δ; 0, T) ≤ (2A₀ δ^{−5/2} + N(0,4)) T -/

section BohrLandauExplicit

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real ComplexConjugate

namespace Zeta23.BL

/-- `NRight δ T ≤ Ncount 0 T`: a finsum over a subset of the finite window (mirror of
`MNF.RH.NOff_le_Ncount`). -/
theorem NRight_le_Ncount (δ T : ℝ) : NRight δ T ≤ MNF.RH.Ncount 0 T := by
  have hfin := MNF.RH.zerosIn_finite 0 T
  have hfin' : (MNF.RH.zerosIn 0 T ∩ {ρ : ℂ | δ ≤ ρ.re - 1 / 2}).Finite :=
    hfin.subset inter_subset_left
  unfold NRight
  rw [MNF.RH.Ncount_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin']
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finite.toFinset_subset_toFinset.2 inter_subset_left) (fun _ _ _ => Nat.zero_le _)

/-! ### The geometry constants at `σ₁ = 1/2 + δ/2` -/

lemma Rout_half (δ : ℝ) : Rout (1 / 2 + δ / 2) = 3 / 2 - δ / 2 := by
  unfold Rout; ring

lemma rin_half (δ : ℝ) : rin (1 / 2 + δ / 2) δ = 3 / 2 - 3 * δ / 4 := by
  unfold rin Rout; ring

/-- `hwin ≥ √δ / 4`: `rin² − (3/2 − δ)² = (δ/4)(3 − 7δ/4) ≥ δ/4` for `δ ≤ 1/2`. -/
lemma hwin_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    Real.sqrt δ / 4 ≤ hwin (1 / 2 + δ / 2) δ := by
  unfold hwin
  rw [rin_half]
  have hX : δ / 4 ≤ (3 / 2 - 3 * δ / 4) ^ 2 - (3 / 2 - δ) ^ 2 := by nlinarith
  have hsq : (Real.sqrt δ / 2) ^ 2 = δ / 4 := by
    rw [div_pow, Real.sq_sqrt hδ.le]; norm_num
  have hs : Real.sqrt δ / 2 ≤ Real.sqrt ((3 / 2 - 3 * δ / 4) ^ 2 - (3 / 2 - δ) ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by linarith), hsq]
    exact hX
  linarith

/-- `log (Rout / rin) ≥ 1 − rin/Rout = (δ/4)/(3/2 − δ/2) ≥ δ/6`. -/
lemma log_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    δ / 6 ≤ Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ) := by
  rw [Rout_half, rin_half]
  have hd1 : 0 < 3 / 2 - δ / 2 := by linarith
  have hd2 : 0 < 3 / 2 - 3 * δ / 4 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hd1 hd2)
  rw [inv_div] at h
  have h' : (3 / 2 - 3 * δ / 4) / (3 / 2 - δ / 2) ≤ 1 - δ / 6 := by
    rw [div_le_iff₀ hd1]; nlinarith
  linarith

/-- The explicit lower bound for the constant `K = 2 hwin log(Rout/rin)` in front of the count in
`count_le_meanSquare'` (the Jensen-window argument: the per-`t` Jensen count integrated over
`t ∈ [3, T+3]`, then Fubini and the mean square): `K ≥ δ√δ/12`. -/
lemma K_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    δ * Real.sqrt δ / 12
      ≤ 2 * hwin (1 / 2 + δ / 2) δ * Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ) := by
  have h1 := hwin_half_ge hδ hδ'
  have h2 := log_half_ge hδ hδ'
  have hs : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hw : 0 ≤ 2 * hwin (1 / 2 + δ / 2) δ := by linarith
  calc δ * Real.sqrt δ / 12 = (2 * (Real.sqrt δ / 4)) * (δ / 6) := by ring
    _ ≤ (2 * hwin (1 / 2 + δ / 2) δ)
          * Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ) :=
        mul_le_mul (by linarith) h2 (by positivity) hw

/-- `δ^{-5/2} · (δ² √δ) = 1` for `δ > 0`. -/
lemma rpow_neg_five_half_mul {δ : ℝ} (hδ : 0 < δ) :
    δ ^ (-(5 / 2 : ℝ)) * (δ ^ 2 * Real.sqrt δ) = 1 := by
  have h1 : δ ^ 2 * Real.sqrt δ = δ ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add hδ]; norm_num
  rw [h1, Real.rpow_neg hδ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hδ _).ne']

/-! ### The explicit right-half bound -/

/-- The explicit right-half constant `A₀ = 54 + (27/2) meanSquareB + 12 log 3`
(`A₀/12 = 9/2 + (9/8) meanSquareB + log 3`). -/
noncomputable def A₀ : ℝ := 54 + 27 / 2 * meanSquareB + 12 * Real.log 3

lemma log_three_nonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)

lemma A₀_nonneg : 0 ≤ A₀ := by
  unfold A₀
  have := meanSquareB_nonneg
  have := log_three_nonneg
  linarith

/-- **The explicit Bohr–Landau bound, right half.** For `0 < δ ≤ 1/2` and `T ≥ 2`,
`NRight δ T ≤ (A₀ δ^{-5/2} + Ncount 0 4 / 2) T`. -/
theorem NRight_explicit {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ T : ℝ, 2 ≤ T →
      (NRight δ T : ℝ) ≤ (A₀ * δ ^ (-(5 / 2 : ℝ)) + (MNF.RH.Ncount 0 4 : ℝ) / 2) * T := by
  intro T hT
  have h1 : 1 / 2 < 1 / 2 + δ / 2 := by linarith
  have h2 : 1 / 2 + δ / 2 < 1 := by linarith
  have hδσ : 1 / 2 + δ / 2 - 1 / 2 < δ := by linarith
  have hMS := meanSquareUnifFrom_explicit δ hδ hδ'
  have hB := meanSquareB_nonneg
  have hC0 : 0 ≤ 4 / δ + meanSquareB := by positivity
  -- the geometry
  have hKlow := K_half_ge hδ hδ'
  set K : ℝ := 2 * hwin (1 / 2 + δ / 2) δ
    * Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ) with hK
  have hs : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hs' : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hKlow
  -- the power
  set E : ℝ := δ ^ (-(5 / 2 : ℝ)) with hE
  have hE0 : 0 < E := Real.rpow_pos_of_pos hδ _
  have hE1 : E * (δ ^ 2 * Real.sqrt δ) = 1 := rpow_neg_five_half_mul hδ
  have hQE : δ * Real.sqrt δ * E = 1 / δ := by
    rw [eq_div_iff hδ.ne']; linear_combination hE1
  have hu : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hN4 : (NRight δ 4 : ℝ) ≤ MNF.RH.Ncount 0 4 := by exact_mod_cast NRight_le_Ncount δ 4
  have hN40 : (0:ℝ) ≤ MNF.RH.Ncount 0 4 := Nat.cast_nonneg _
  have hA0 := A₀_nonneg
  have hl3 := log_three_nonneg
  rcases le_or_gt 4 T with hT4 | hT4
  · -- `T ≥ 4`: J6 + J7 with the explicit constants
    have h67 := count_le_meanSquare' h1 h2 hδσ hδ' hMS hT4
    rw [← hK] at h67
    have hstep1 : (1 / 2) * ((4 / δ + meanSquareB) * (T + 5)) + T * Real.log 3
        ≤ ((9 / 8) * (4 / δ + meanSquareB) + Real.log 3) * T := by
      nlinarith [mul_nonneg hC0 (by linarith : (0:ℝ) ≤ T - 4)]
    have hstep2 : (9 / 8) * (4 / δ + meanSquareB) + Real.log 3 ≤ A₀ / 12 * (1 / δ) := by
      unfold A₀
      have := mul_le_mul_of_nonneg_left hu
        (by linarith : (0:ℝ) ≤ 9 / 8 * meanSquareB + Real.log 3)
      have h4 : 4 / δ = 4 * (1 / δ) := by ring
      linarith
    have hstep3 : A₀ / 12 * (1 / δ) * T ≤ K * (A₀ * E * T) := by
      calc A₀ / 12 * (1 / δ) * T = δ * Real.sqrt δ / 12 * (A₀ * E * T) := by
            rw [← hQE]; ring
        _ ≤ K * (A₀ * E * T) := mul_le_mul_of_nonneg_right hKlow (by positivity)
    have hdiff : (NRight δ T : ℝ) - NRight δ 4 ≤ A₀ * E * T := by
      refine le_of_mul_le_mul_left ?_ hKpos
      calc K * ((NRight δ T : ℝ) - NRight δ 4) ≤ _ := h67
        _ ≤ ((9 / 8) * (4 / δ + meanSquareB) + Real.log 3) * T := hstep1
        _ ≤ A₀ / 12 * (1 / δ) * T := mul_le_mul_of_nonneg_right hstep2 (by linarith)
        _ ≤ K * (A₀ * E * T) := hstep3
    nlinarith [mul_nonneg hN40 (by linarith : (0:ℝ) ≤ T - 2)]
  · -- `2 ≤ T < 4`: monotonicity
    have hmono : (NRight δ T : ℝ) ≤ NRight δ 4 := by exact_mod_cast NRight_mono hT4.le
    nlinarith [mul_nonneg hN40 (by linarith : (0:ℝ) ≤ T - 2),
      mul_nonneg (mul_nonneg hA0 hE0.le) (by linarith : (0:ℝ) ≤ T)]

/-- **The explicit Bohr–Landau bound.** Explicit Bohr–Landau constant: there are `A, B ≥ 0` (namely `A = 2 A₀`,
`B = Ncount 0 4`) with `NOff δ 0 T ≤ (A δ^{-5/2} + B) T` for all `0 < δ ≤ 1/2`, `T ≥ 2`. -/
theorem bohrLandau_explicit : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
    ∀ T : ℝ, 2 ≤ T → (MNF.RH.NOff δ 0 T : ℝ) ≤ (A * δ ^ (-(5/2 : ℝ)) + B) * T := by
  refine ⟨2 * A₀, (MNF.RH.Ncount 0 4 : ℝ), by linarith [A₀_nonneg], Nat.cast_nonneg _, ?_⟩
  intro δ hδ hδ' T hT
  rw [NOff_eq_right_add_left hδ T, NLeft_eq_NRight]
  push_cast
  have h := NRight_explicit hδ hδ' T hT
  linarith

end Zeta23.BL

end BohrLandauExplicit

/-! # §3 Riemann–von Mangoldt in the shape N(0,T) ≍ T log T -/

section RiemannVonMangoldtShape

open Finset

noncomputable section

namespace Zeta23

/-- An empty ordinate window carries no zeros. -/
theorem Ncount_self (a : ℝ) : Ncount a a = 0 := by
  unfold Ncount
  have h : zerosIn a a = ∅ := by
    ext ρ
    simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, h1, h2⟩
    exact absurd h2 (not_le.2 h1)
  rw [h, finsum_mem_empty]

/-- N(0,n] = Σ_{m<n} N(m,m+1] for natural n. -/
theorem Ncount_zero_nat (n : ℕ) :
    Ncount 0 (n : ℝ) = ∑ m ∈ range n, Ncount (m : ℝ) ((m : ℝ) + 1) := by
  induction n with
  | zero => simp [Ncount_self]
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    have h := Ncount_add (a := (0 : ℝ)) (b := (n : ℝ)) (c := (n : ℝ) + 1)
      (by positivity) (by linarith)
    push_cast
    exact h

/-- Each unit window is bounded by A₀ log(T+3) once its left end is ≤ T (from `local_count`). -/
theorem Ncount_unit_le {A₀ : ℝ} (hA : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (m : ℕ) {T : ℝ} (hmT : (m : ℝ) ≤ T) :
    (Ncount (m : ℝ) ((m : ℝ) + 1) : ℝ) ≤ A₀ * Real.log (T + 3) := by
  have h := hloc (m : ℝ)
  rw [zetaZeroConfig_N] at h
  have hm : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (by positivity)
  rw [hm] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  exact Real.log_le_log (by positivity) (by linarith)

/-- **Upper bound** N(0,T) ≤ C·T·log T for T ≥ T₀ (with C = 4A₀ and T₀ = 3, where A₀ ≥ 1 is the
unit-window constant of `riemannVonMangoldt_zeta.local_count` — an existential constant, not
`Zeta23.BL.A₀`). -/
theorem Ncount_le_mul_log :
    ∃ C : ℝ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (Ncount 0 T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A₀, hA, hloc⟩ := riemannVonMangoldt_zeta.local_count
  refine ⟨4 * A₀, 3, by norm_num, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  set n : ℕ := ⌈T⌉₊ with hn
  -- step 1: N(0,T) ≤ N(0,n)
  have h1 : (Ncount 0 T : ℝ) ≤ Ncount 0 (n : ℝ) := by
    exact_mod_cast Ncount_mono le_rfl (Nat.le_ceil T)
  -- step 2: N(0,n) = Σ_{m<n} N(m,m+1) ≤ n · A₀ log(T+3)
  have h2 : (Ncount 0 (n : ℝ) : ℝ) ≤ (n : ℝ) * (A₀ * Real.log (T + 3)) := by
    rw [Ncount_zero_nat n]
    push_cast
    have := Finset.sum_le_card_nsmul (range n)
      (fun m : ℕ => (Ncount (m : ℝ) ((m : ℝ) + 1) : ℝ)) (A₀ * Real.log (T + 3))
      (fun m hm => by
        have hmn : m < n := Finset.mem_range.1 hm
        have hmT : (m : ℝ) ≤ T := le_of_lt (Nat.lt_ceil.1 hmn)
        exact Ncount_unit_le hA hloc m hmT)
    simpa [nsmul_eq_mul, Finset.card_range] using this
  -- step 3: n ≤ T + 1 ≤ 2T and log(T+3) ≤ 2 log T
  have hn_le : (n : ℝ) ≤ T + 1 := le_of_lt (Nat.ceil_lt_add_one hT0)
  have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
    have : Real.log (T + 3) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rwa [Real.log_pow] at this
    -- `Real.log_pow` gives `(2:ℕ) * log T`; the cast is handled by `rwa` up to `Nat.cast_ofNat`
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog3 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A₀ := by linarith
  calc (Ncount 0 T : ℝ) ≤ Ncount 0 (n : ℝ) := h1
    _ ≤ (n : ℝ) * (A₀ * Real.log (T + 3)) := h2
    _ ≤ (T + 1) * (A₀ * Real.log (T + 3)) :=
        mul_le_mul_of_nonneg_right hn_le (by positivity)
    _ ≤ (2 * T) * (A₀ * (2 * Real.log T)) := by
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hlog hA0) (by positivity)
          (by positivity)
    _ = 4 * A₀ * T * Real.log T := by ring

/-- ℓ₁(T/2) = log T − log π − 1. -/
theorem ell1_half (T : ℝ) (hT : 0 < T) :
    ell1 (T / 2) = Real.log T - Real.log Real.pi - 1 := by
  unfold ell1 l
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4 : T / 2 / (2 * Real.pi) = T / (4 * Real.pi) := by field_simp; ring
  rw [h4, Real.log_div hT.ne' (by positivity), Real.log_mul (by norm_num) hpi.ne']
  have : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [this]; ring

/-- **Lower bound** c·T·log T ≤ N(0,T) for T ≥ T₀ (with c = 1/(16π) and
T₀ = 2 + 2|T₁| + e⁸ + 16π(|C| + 1), where C, T₁ are the constants of
`riemannVonMangoldt_zeta.main`). -/
theorem mul_log_le_Ncount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → c * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  obtain ⟨C, T₁, hR⟩ := riemannVonMangoldt_zeta.main
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨1 / (16 * Real.pi), by positivity,
    2 + 2 * |T₁| + Real.exp 8 + 16 * Real.pi * (|C| + 1), ?_, fun T hT => ?_⟩
  · have := Real.exp_pos 8
    have : 0 ≤ 16 * Real.pi * (|C| + 1) := by positivity
    linarith [abs_nonneg T₁]
  have hexp : 0 < Real.exp 8 := Real.exp_pos 8
  have hC16 : 0 ≤ 16 * Real.pi * (|C| + 1) := by positivity
  have hT1 : T₁ ≤ T / 2 := by linarith [le_abs_self T₁]
  have hT2 : 2 ≤ T := by linarith [abs_nonneg T₁]
  have hTpos : 0 < T := by linarith
  have hTexp : Real.exp 8 ≤ T := by linarith [abs_nonneg T₁]
  have hTC : 16 * Real.pi * |C| ≤ T := by nlinarith [abs_nonneg T₁]
  -- the window (T/2, T]
  have hb := hR (T / 2) hT1
  rw [zetaZeroConfig_N, show 2 * (T / 2) = T by ring] at hb
  have hlow := (abs_le.1 hb).1
  -- log T ≥ 8
  have hL : 8 ≤ Real.log T := by
    have := Real.log_le_log hexp hTexp
    rwa [Real.log_exp] at this
  have hLpos : 0 ≤ Real.log T := by linarith
  -- ell1 (T/2) ≥ (1/2) log T
  have hE : Real.log T / 2 ≤ ell1 (T / 2) := by
    rw [ell1_half T hTpos]
    have : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos hpi
    have := Real.pi_le_four
    linarith
  -- C log(T/2) ≤ |C| log T
  have hlog_half : 0 ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  have hlog_half_le : Real.log (T / 2) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith)
  have hCl : C * Real.log (T / 2) ≤ |C| * Real.log T := by
    calc C * Real.log (T / 2) ≤ |C| * Real.log (T / 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hlog_half
      _ ≤ |C| * Real.log T := mul_le_mul_of_nonneg_left hlog_half_le (abs_nonneg C)
  -- main term ≥ T log T / (8π)
  have hmain : T * Real.log T / (8 * Real.pi) ≤ T / 2 / (2 * Real.pi) * ell1 (T / 2) := by
    have h1 : T / 2 / (2 * Real.pi) * ell1 (T / 2) = T * ell1 (T / 2) / (4 * Real.pi) := by
      field_simp; ring
    have h2 : T * Real.log T / (8 * Real.pi) = T * (Real.log T / 2) / (4 * Real.pi) := by ring
    rw [h1, h2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hTpos.le) (by positivity)
  -- |C| log T ≤ T log T / (16π)
  have herr : |C| * Real.log T ≤ T * Real.log T / (16 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hTC hLpos
    nlinarith
  -- assemble: N(T/2,T) ≥ T log T/(16π), and N(0,T) ≥ N(T/2,T)
  have hwin : T * Real.log T / (16 * Real.pi) ≤ (Ncount (T / 2) T : ℝ) := by
    have : T * Real.log T / (8 * Real.pi) - T * Real.log T / (16 * Real.pi)
        = T * Real.log T / (16 * Real.pi) := by ring
    linarith
  have hmono : (Ncount (T / 2) T : ℝ) ≤ Ncount 0 T := by
    exact_mod_cast Ncount_mono (by linarith : (0 : ℝ) ≤ T / 2) le_rfl
  calc 1 / (16 * Real.pi) * T * Real.log T = T * Real.log T / (16 * Real.pi) := by ring
    _ ≤ Ncount (T / 2) T := hwin
    _ ≤ Ncount 0 T := hmono

/-! ## MNF.RH restatements (definitional) -/

theorem MNF_Ncount_eq (T₁ T₂ : ℝ) : MNF.RH.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := rfl

theorem MNF_Ncount_le_mul_log :
    ∃ C : ℝ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (MNF.RH.Ncount 0 T : ℝ) ≤ C * T * Real.log T :=
  Ncount_le_mul_log

theorem MNF_mul_log_le_Ncount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      c * T * Real.log T ≤ (MNF.RH.Ncount 0 T : ℝ) :=
  mul_log_le_Ncount

end Zeta23

end

end RiemannVonMangoldtShape

/-! # §4 The reservoir mass and the layer-cake identity -/

section LayerCake

namespace MNF.RH

open Set MeasureTheory intervalIntegral
open scoped BigOperators

/-- **The reservoir mass** of the window (0, T]: the sum over the nontrivial zeros ρ with
0 < Im ρ ≤ T of m(ρ)·|Re ρ − 1/2| (m = `zeta_order`), i.e. the total distance from the critical
line, counted with multiplicity (the header explains the name).  `∑ᶠ` is Mathlib's finite sum;
the window is finite (`zerosIn_finite`). -/
noncomputable def reservoirMass (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * |ρ.re - 1 / 2|

/-! ### §4.1 The shift of a nontrivial zero is < 1/2 -/

theorem abs_re_sub_half_lt_half {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    |ρ.re - 1 / 2| < 1 / 2 := by
  rw [abs_sub_lt_iff]
  constructor <;> linarith [h.2.1, h.2.2]

theorem abs_re_sub_half_le_half {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    |ρ.re - 1 / 2| ≤ 1 / 2 :=
  (abs_re_sub_half_lt_half h).le

/-! ### §4.2 `NOff` as a Finset sum of indicators over the finite window -/

/-- `NOff δ T₁ T₂` as a sum over the finite window, each zero contributing its multiplicity
when `δ ≤ |Re ρ − 1/2|` and `0` otherwise. -/
theorem NOff_eq_sum_ite (δ T₁ T₂ : ℝ) :
    NOff δ T₁ T₂ = ∑ ρ ∈ (zerosIn_finite T₁ T₂).toFinset,
      if δ ≤ |ρ.re - 1 / 2| then zeta_order ρ else 0 := by
  have hfin' : (zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}).Finite :=
    (zerosIn_finite T₁ T₂).subset inter_subset_left
  unfold NOff
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← Finset.sum_filter]
  congr 1
  ext ρ
  simp only [Finset.mem_filter, Finite.mem_toFinset, mem_inter_iff, mem_ofPred_eq]

/-- The real-valued `NOff δ T₁ T₂` as a sum of `m(ρ) · 1[δ ≤ |Re ρ − 1/2|]`; the indicator set is
spelled `{x | x ≤ a}` so that Mathlib's `intervalIntegral.integral_indicator` applies. -/
theorem NOff_real_eq_sum_indicator (δ T₁ T₂ : ℝ) :
    (NOff δ T₁ T₂ : ℝ) = ∑ ρ ∈ (zerosIn_finite T₁ T₂).toFinset,
      (zeta_order ρ : ℝ) * indicator {x : ℝ | x ≤ |ρ.re - 1 / 2|} (fun _ => (1 : ℝ)) δ := by
  rw [NOff_eq_sum_ite]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [indicator_apply, mem_ofPred_eq]
  split_ifs <;> simp

/-! ### §4.3 `δ ↦ NOff δ T₁ T₂` is antitone, hence interval integrable -/

/-- Raising the threshold removes zeros: `NOff` is antitone in `δ` (as natural numbers). -/
theorem NOff_anti {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) (T₁ T₂ : ℝ) :
    NOff δ₂ T₁ T₂ ≤ NOff δ₁ T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have hfin₁ : (zerosIn T₁ T₂ ∩ {ρ | δ₁ ≤ |ρ.re - 1 / 2|}).Finite :=
    hfin.subset inter_subset_left
  have hfin₂ : (zerosIn T₁ T₂ ∩ {ρ | δ₂ ≤ |ρ.re - 1 / 2|}).Finite :=
    hfin.subset inter_subset_left
  unfold NOff
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin₁, finsum_mem_eq_finite_toFinset_sum _ hfin₂]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finite.toFinset_subset_toFinset.2 ?_) (fun _ _ _ => Nat.zero_le _)
  exact inter_subset_inter subset_rfl fun ρ (hρ : δ₂ ≤ |ρ.re - 1 / 2|) => le_trans h hρ

/-- `δ ↦ (NOff δ T₁ T₂ : ℝ)` is antitone. -/
theorem NOff_antitone (T₁ T₂ : ℝ) : Antitone (fun δ => (NOff δ T₁ T₂ : ℝ)) := by
  intro δ₁ δ₂ h
  show (NOff δ₂ T₁ T₂ : ℝ) ≤ NOff δ₁ T₁ T₂
  exact_mod_cast NOff_anti h T₁ T₂

/-- `δ ↦ (NOff δ T₁ T₂ : ℝ)` is interval integrable on every `[a, b]` (an antitone function
is interval integrable, `Antitone.intervalIntegrable`). -/
theorem NOff_intervalIntegrable (T₁ T₂ a b : ℝ) :
    IntervalIntegrable (fun δ => (NOff δ T₁ T₂ : ℝ)) volume a b :=
  (NOff_antitone T₁ T₂).intervalIntegrable

/-- The indicator `δ ↦ 1[δ ≤ a]` is antitone. -/
theorem indicator_le_antitone (a : ℝ) :
    Antitone (fun δ : ℝ => indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ) := by
  intro x y hxy
  simp only [indicator_apply, mem_ofPred_eq]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hxy.trans h1) h2
  · norm_num
  · exact le_rfl

/-- Each summand `δ ↦ m(ρ) · 1[δ ≤ a]` is interval integrable on every `[x, y]`. -/
theorem term_intervalIntegrable (c a x y : ℝ) :
    IntervalIntegrable (fun δ : ℝ => c * indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ)
      volume x y :=
  (indicator_le_antitone a).intervalIntegrable.const_mul c

/-! ### §4.4 The per-zero integral: ∫₀^{1/2} 1[δ ≤ a] dδ = a for 0 ≤ a ≤ 1/2 -/

theorem integral_indicator_le_eq {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1 / 2) :
    ∫ δ in (0 : ℝ)..(1 / 2), indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ = a := by
  rw [intervalIntegral.integral_indicator ⟨h0, h1⟩, intervalIntegral.integral_const]
  simp

/-! ### §4.5 The layer-cake identity -/

/-- **Layer cake**: `reservoirMass T = ∫₀^{1/2} NOff δ 0 T dδ`.  Write `NOff δ 0 T` as the
finite sum `Σ_ρ m(ρ)·1[δ ≤ |Re ρ − 1/2|]` (§4.2), interchange the Finset sum and the interval
integral (`intervalIntegral.integral_finsetSum`, each term integrable by §4.3), and evaluate each
`∫₀^{1/2} 1[δ ≤ |Re ρ − 1/2|] dδ = |Re ρ − 1/2|` (§4.4, using `|Re ρ − 1/2| ≤ 1/2` from §4.1). -/
theorem reservoirMass_eq_integral (T : ℝ) :
    reservoirMass T = ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ) := by
  have hfin := zerosIn_finite 0 T
  simp only [NOff_real_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum (fun ρ _ => term_intervalIntegrable _ _ _ _)]
  unfold reservoirMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hρ' : is_nontrivial_zero ρ := (hfin.mem_toFinset.1 hρ).1
  rw [intervalIntegral.integral_const_mul,
    integral_indicator_le_eq (abs_nonneg _) (abs_re_sub_half_le_half hρ')]

/-- The reservoir mass is nonnegative. -/
theorem reservoirMass_nonneg (T : ℝ) : 0 ≤ reservoirMass T := by
  unfold reservoirMass
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)]
  exact Finset.sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

/-- Every zero is at distance ≤ 1/2 from the line, so the mass is at most `(1/2)·N(0,T)`. -/
theorem reservoirMass_le_half_Ncount (T : ℝ) :
    reservoirMass T ≤ (1 / 2) * Ncount 0 T := by
  have hfin := zerosIn_finite 0 T
  unfold reservoirMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Ncount_eq_sum hfin]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' : is_nontrivial_zero ρ := (hfin.mem_toFinset.1 hρ).1
  rw [mul_comm (1 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (abs_re_sub_half_le_half hρ') (Nat.cast_nonneg _)

/-! ### §4.6 The two-piece split -/

/-- `∫₀^{1/2} NOff = ∫₀^{δ₀} NOff + ∫_{δ₀}^{1/2} NOff` (for every `δ₀`, by interval
integrability on each piece). -/
theorem integral_NOff_split (T δ₀ : ℝ) :
    ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ) =
      (∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ)) + ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ) :=
  (intervalIntegral.integral_add_adjacent_intervals (NOff_intervalIntegrable 0 T 0 δ₀)
    (NOff_intervalIntegrable 0 T δ₀ (1 / 2))).symm

/-- `∫₀^{δ₀} NOff ≤ δ₀ · N(0,T)` for `0 ≤ δ₀`, from `NOff ≤ Ncount` pointwise. -/
theorem integral_NOff_le_mul_Ncount (T : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) :
    ∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ) ≤ δ₀ * Ncount 0 T := by
  have h : ∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ) ≤ ∫ _ in (0 : ℝ)..δ₀, (Ncount 0 T : ℝ) :=
    intervalIntegral.integral_mono_on h0 (NOff_intervalIntegrable 0 T 0 δ₀)
      intervalIntegrable_const (fun δ _ => by exact_mod_cast NOff_le_Ncount δ 0 T)
  rw [intervalIntegral.integral_const] at h
  simpa only [sub_zero, smul_eq_mul] using h

/-- `∫_{δ₀}^{1/2} NOff ≤ (1/2 − δ₀) · NOff δ₀ 0 T` for `δ₀ ≤ 1/2`, since `NOff` is
antitone. -/
theorem integral_NOff_tail_le (T : ℝ) {δ₀ : ℝ} (h1 : δ₀ ≤ 1 / 2) :
    ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ) ≤ (1 / 2 - δ₀) * NOff δ₀ 0 T := by
  have h : ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ) ≤ ∫ _ in δ₀..(1 / 2), (NOff δ₀ 0 T : ℝ) :=
    intervalIntegral.integral_mono_on h1 (NOff_intervalIntegrable 0 T δ₀ (1 / 2))
      intervalIntegrable_const (fun δ hδ => NOff_antitone 0 T hδ.1)
  rw [intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul] using h

/-! ### §4.7 Consequences -/

/-- The mass is at most `δ₀ · N(0,T) + (1/2 − δ₀) · N_off(δ₀; 0,T)` for every `0 ≤ δ₀ ≤ 1/2`:
layer cake, the split at `δ₀`, and the two bounds of §4.6. -/
theorem reservoirMass_le_split (T : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 1 / 2) :
    reservoirMass T ≤ δ₀ * Ncount 0 T + (1 / 2 - δ₀) * NOff δ₀ 0 T := by
  rw [reservoirMass_eq_integral, integral_NOff_split T δ₀]
  exact add_le_add (integral_NOff_le_mul_Ncount T h0) (integral_NOff_tail_le T h1)

/-- **The mean distance from the line tends to zero**: for every `ε > 0`, eventually
`Σ_ρ m(ρ)·|Re ρ − 1/2| ≤ ε · N(0,T)`.  Take `δ₀ = min (ε/2) (1/2)` in `reservoirMass_le_split`
and bound `N_off(δ₀; 0,T) ≤ ε · N(0,T)` by the tree's unconditional `ReservoirDensityOne`
(`reservoirDensityOne_unconditional`, from Bohr–Landau at every `δ > 0` and the superlinear
growth of `N`). -/
theorem reservoirMass_le_eps_Ncount :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, reservoirMass T ≤ ε * Ncount 0 T := by
  intro ε hε
  set δ₀ : ℝ := min (ε / 2) (1 / 2) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  have hδ₀le : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hδ₀ε : δ₀ ≤ ε / 2 := min_le_left _ _
  obtain ⟨T₀, hT₀⟩ := reservoirDensityOne_unconditional δ₀ hδ₀pos ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := reservoirMass_le_split T hδ₀pos.le hδ₀le
  have h2 : (NOff δ₀ 0 T : ℝ) ≤ ε * Ncount 0 T := hT₀ T hT
  have hN : (0 : ℝ) ≤ Ncount 0 T := Nat.cast_nonneg _
  have hNOff : (0 : ℝ) ≤ NOff δ₀ 0 T := Nat.cast_nonneg _
  have hA : δ₀ * (Ncount 0 T : ℝ) ≤ (ε / 2) * Ncount 0 T :=
    mul_le_mul_of_nonneg_right hδ₀ε hN
  have hB : (1 / 2 - δ₀) * (NOff δ₀ 0 T : ℝ) ≤ (1 / 2) * NOff δ₀ 0 T :=
    mul_le_mul_of_nonneg_right (by linarith) hNOff
  have hC : (1 / 2) * (NOff δ₀ 0 T : ℝ) ≤ (1 / 2) * (ε * Ncount 0 T) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  linarith

end MNF.RH

end LayerCake

/-! # §5 The reflection symmetry: the signed reservoir vanishes -/

section ReflectionSymmetry

open Set Complex

namespace MNF.RH

/-! ### The reflection ρ ↦ 1 − ρ̄ on a window -/

lemma reflect_re (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]

lemma reflect_im (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im := by simp [Zeta23.reflect]

lemma reflect_reflect (ρ : ℂ) : Zeta23.reflect (Zeta23.reflect ρ) = ρ := by
  simp [Zeta23.reflect]

lemma reflect_injective : Function.Injective Zeta23.reflect :=
  Function.LeftInverse.injective reflect_reflect

/-- The reflection maps every ordinate window of nontrivial zeros into itself. -/
lemma reflect_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) :
    Zeta23.reflect ρ ∈ zerosIn T₁ T₂ := by
  obtain ⟨hz, h1, h2⟩ := h
  exact ⟨Zeta23.zetaZeroConfig.reflect_mem ρ hz, by simpa [reflect_im] using h1,
    by simpa [reflect_im] using h2⟩

/-- The reflection preserves multiplicity (delegated to the tree's `zetaZeroConfig.mult_reflect`,
which comes from the functional equation and Schwarz reflection). -/
lemma zeta_order_reflectZ {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    zeta_order (Zeta23.reflect ρ) = zeta_order ρ :=
  Zeta23.zetaZeroConfig.mult_reflect ρ hz

/-- An involution that maps `A` into `B` and `B` into `A` is a bijection `A → B`. -/
lemma reflect_bijOn (A B : Set ℂ) (hAB : MapsTo Zeta23.reflect A B)
    (hBA : MapsTo Zeta23.reflect B A) : BijOn Zeta23.reflect A B :=
  ⟨hAB, reflect_injective.injOn, fun σ hσ => ⟨Zeta23.reflect σ, hBA hσ, reflect_reflect σ⟩⟩

lemma reflect_bijOn_zerosIn (T : ℝ) : BijOn Zeta23.reflect (zerosIn 0 T) (zerosIn 0 T) :=
  reflect_bijOn _ _ (fun _ h => reflect_mem_zerosIn h) (fun _ h => reflect_mem_zerosIn h)

/-! ### The signed reservoir vanishes -/

/-- **The signed reservoir vanishes**: Σ_{ρ ∈ zerosIn 0 T} m_ρ (Re ρ − 1/2) = 0, because the
reflection ρ ↦ 1 − ρ̄ is a multiplicity-preserving involution of the window that negates each
term.  (This is the sign-symmetry statement MNF calls its "sign gate", in count form; it is the
functional-equation symmetry and nothing more.) -/
theorem signedReservoir_eq_zero (T : ℝ) :
    ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) = 0 := by
  have hneg : ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) =
      ∑ᶠ ρ ∈ zerosIn 0 T, -((zeta_order ρ : ℝ) * (ρ.re - 1 / 2)) := by
    refine finsum_mem_eq_of_bijOn Zeta23.reflect (reflect_bijOn_zerosIn T) ?_
    intro ρ hρ
    rw [zeta_order_reflectZ hρ.1, reflect_re]; ring
  rw [finsum_mem_neg_distrib _ (zerosIn_finite 0 T)] at hneg
  linarith

/-- The right-half signed mass equals the left-half signed mass. -/
theorem sum_right_eq_sum_left (T : ℝ) :
    ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | 1 / 2 < ρ.re}, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) =
    ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | ρ.re < 1 / 2}, (zeta_order ρ : ℝ) * (1 / 2 - ρ.re) := by
  refine finsum_mem_eq_of_bijOn Zeta23.reflect (reflect_bijOn _ _ ?_ ?_) ?_
  · rintro ρ ⟨h, hp⟩
    refine ⟨reflect_mem_zerosIn h, ?_⟩
    simp only [mem_ofPred_eq, reflect_re] at hp ⊢; linarith
  · rintro ρ ⟨h, hp⟩
    refine ⟨reflect_mem_zerosIn h, ?_⟩
    simp only [mem_ofPred_eq, reflect_re] at hp ⊢; linarith
  · rintro ρ ⟨hρ, _⟩
    rw [zeta_order_reflectZ hρ.1, reflect_re]; ring

/-- The reservoir mass is twice the right-half signed mass. -/
theorem reservoirMass_eq_two_right (T : ℝ) :
    reservoirMass T =
      2 * ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | 1 / 2 < ρ.re}, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) := by
  unfold reservoirMass
  have hf := zerosIn_finite 0 T
  set g : ℂ → ℝ := fun ρ => (zeta_order ρ : ℝ) * |ρ.re - 1 / 2| with hg
  set A := zerosIn 0 T ∩ {ρ | 1 / 2 < ρ.re} with hA
  set B := zerosIn 0 T ∩ {ρ | ρ.re < 1 / 2} with hB
  have hsplit : ∑ᶠ ρ ∈ zerosIn 0 T, g ρ = ∑ᶠ ρ ∈ A ∪ B, g ρ := by
    apply finsum_mem_inter_support_eq'
    intro ρ hρ
    simp only [hA, hB, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      have hne : ρ.re ≠ 1 / 2 := by
        intro heq; exact hρ (by simp [hg, heq])
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inr ⟨h, h'⟩
      · exact Or.inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd : Disjoint A B := disjoint_left.2 fun x h1 h2 => by
    have a : 1 / 2 < x.re := h1.2; have b : x.re < 1 / 2 := h2.2; linarith
  have hAeq : ∑ᶠ ρ ∈ A, g ρ = ∑ᶠ ρ ∈ A, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) :=
    finsum_mem_congr rfl fun ρ hρ => by
      have : 1 / 2 < ρ.re := hρ.2
      simp only [hg]; rw [abs_of_pos (by linarith)]
  have hBeq : ∑ᶠ ρ ∈ B, g ρ = ∑ᶠ ρ ∈ B, (zeta_order ρ : ℝ) * (1 / 2 - ρ.re) :=
    finsum_mem_congr rfl fun ρ hρ => by
      have : ρ.re < 1 / 2 := hρ.2
      simp only [hg]; rw [abs_of_neg (by linarith)]; ring
  rw [hsplit, finsum_mem_union hd (hf.subset inter_subset_left) (hf.subset inter_subset_left),
    hAeq, hBeq, ← sum_right_eq_sum_left]
  ring

end MNF.RH

end ReflectionSymmetry

/-! # §6 The bound: reservoirMass T ≤ A · T · (log T)^{3/5}, and the mean distance → 0 -/

section ReservoirBound

namespace MNF.RH

open MeasureTheory intervalIntegral

/-- `δ ↦ (A δ^{-5/2} + B) T` is interval integrable on `[δ₀, 1/2]` for `δ₀ > 0`
(continuous away from `0`). -/
theorem rpow_tail_intervalIntegrable (A B T : ℝ) {δ₀ : ℝ} (h0 : 0 < δ₀) (h1 : δ₀ ≤ 1 / 2) :
    IntervalIntegrable (fun δ : ℝ => (A * δ ^ (-(5 / 2 : ℝ)) + B) * T) volume δ₀ (1 / 2) := by
  have hz : (0 : ℝ) ∉ Set.uIcc δ₀ (1 / 2) := by
    rw [Set.uIcc_of_le h1]
    intro h
    exact absurd h.1 (not_le.2 h0)
  have hr : IntervalIntegrable (fun δ : ℝ => δ ^ (-(5 / 2 : ℝ))) volume δ₀ (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  exact ((hr.const_mul A).add intervalIntegrable_const).mul_const T

/-- The tail integral of the explicit Bohr–Landau majorant:
`∫_{δ₀}^{1/2} (A δ^{-5/2} + B) T dδ ≤ ((2/3) A δ₀^{-3/2} + B/2) T` for `A, B, T ≥ 0`,
`0 < δ₀ ≤ 1/2` (`∫ δ^{-5/2} dδ = −(2/3) δ^{-3/2}`, `integral_rpow`). -/
theorem integral_rpow_tail_le (A B T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) {δ₀ : ℝ}
    (h0 : 0 < δ₀) (h1 : δ₀ ≤ 1 / 2) :
    ∫ δ in δ₀..(1 / 2), (A * δ ^ (-(5 / 2 : ℝ)) + B) * T
      ≤ (2 / 3 * A * δ₀ ^ (-(3 / 2 : ℝ)) + B / 2) * T := by
  have hz : (0 : ℝ) ∉ Set.uIcc δ₀ (1 / 2) := by
    rw [Set.uIcc_of_le h1]
    intro h
    exact absurd h.1 (not_le.2 h0)
  have hr : IntervalIntegrable (fun δ : ℝ => δ ^ (-(5 / 2 : ℝ))) volume δ₀ (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hI : ∫ δ in δ₀..(1 / 2), δ ^ (-(5 / 2 : ℝ))
      = ((1 / 2 : ℝ) ^ (-(5 / 2 : ℝ) + 1) - δ₀ ^ (-(5 / 2 : ℝ) + 1)) / (-(5 / 2 : ℝ) + 1) :=
    integral_rpow (Or.inr ⟨by norm_num, hz⟩)
  have he : (-(5 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) := by norm_num
  rw [he] at hI
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hr.const_mul A) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hI, intervalIntegral.integral_const, smul_eq_mul]
  have hhalf : 0 ≤ (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  refine mul_le_mul_of_nonneg_right ?_ hT
  have e : A * (((1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) - δ₀ ^ (-(3 / 2 : ℝ))) / -(3 / 2 : ℝ))
      = 2 / 3 * A * δ₀ ^ (-(3 / 2 : ℝ)) - 2 / 3 * A * (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
  rw [e]
  have hAp : 0 ≤ 2 / 3 * A * (1 / 2 : ℝ) ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hA) hhalf
  have hBd : 0 ≤ δ₀ * B := mul_nonneg h0.le hB
  linarith

/-- **The reservoir-mass bound.** `reservoirMass T ≤ A · T · (log T)^{3/5}` for all large `T`
(`A = C + (2/3) A₂ + B₂/2` with `C` from `Ncount_le_mul_log` and `A₂, B₂` from `bohrLandau_explicit`;
`T₀ = max T₁ (exp 8)`).  Split the layer cake at `δ₀ = (log T)^{-2/5}` (`≤ 1/2` since
`log T ≥ 8`): the head `∫₀^{δ₀} NOff ≤ δ₀ · N(0,T) ≤ C · T · (log T)^{3/5}`, the tail
`∫_{δ₀}^{1/2} NOff ≤ ((2/3) A₂ δ₀^{-3/2} + B₂/2) · T = ((2/3) A₂ (log T)^{3/5} + B₂/2) · T`, and
`(log T)^{3/5} ≥ 1` absorbs `B₂/2`.  The exponent `3/5` is where the two pieces balance for a
majorant `δ^{-5/2}`. -/
theorem reservoirMass_le_rpow :
    ∃ A : ℝ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      reservoirMass T ≤ A * T * (Real.log T) ^ ((3:ℝ)/5) := by
  obtain ⟨A₂, B₂, hA₂, hB₂, hBL⟩ := Zeta23.BL.bohrLandau_explicit
  obtain ⟨C, T₁, hT₁, hUp⟩ := Zeta23.MNF_Ncount_le_mul_log
  refine ⟨C + 2 / 3 * A₂ + B₂ / 2, max T₁ (Real.exp 8), fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTexp : Real.exp 8 ≤ T := le_trans (le_max_right _ _) hT
  have hT2 : 2 ≤ T := le_trans hT₁ hTT₁
  have hTpos : 0 < T := by linarith
  have hT0 : 0 ≤ T := hTpos.le
  -- log T ≥ 8
  have hL8 : 8 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 8) hTexp
    rwa [Real.log_exp] at this
  have hLpos : 0 < Real.log T := by linarith
  have hL1 : 1 ≤ Real.log T := by linarith
  -- δ₀ = (log T)^{-2/5}
  set δ₀ : ℝ := Real.log T ^ (-(2:ℝ)/5) with hδ₀
  have hδ₀pos : 0 < δ₀ := Real.rpow_pos_of_pos hLpos _
  -- δ₀ ≤ 1/2, since (log T)^{2/5} ≥ 8^{2/5} = 2^{6/5} ≥ 2
  have hδ₀le : δ₀ ≤ 1 / 2 := by
    have h8 : (8:ℝ) = (2:ℝ) ^ (3:ℝ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have h2 : (2:ℝ) ≤ Real.log T ^ ((2:ℝ)/5) := by
      calc (2:ℝ) = (2:ℝ) ^ (1:ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2:ℝ) ^ ((3:ℝ) * ((2:ℝ)/5)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = ((2:ℝ) ^ (3:ℝ)) ^ ((2:ℝ)/5) := Real.rpow_mul (by norm_num) _ _
        _ = (8:ℝ) ^ ((2:ℝ)/5) := by rw [h8]
        _ ≤ Real.log T ^ ((2:ℝ)/5) := Real.rpow_le_rpow (by norm_num) hL8 (by norm_num)
    have hneg : δ₀ = (Real.log T ^ ((2:ℝ)/5))⁻¹ := by
      rw [hδ₀, show (-(2:ℝ)/5) = -((2:ℝ)/5) by norm_num, Real.rpow_neg hLpos.le]
    rw [hneg, show (1 / 2 : ℝ) = (2:ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) h2
  -- the two exponent identities: δ₀ · log T = (log T)^{3/5} and δ₀^{-3/2} = (log T)^{3/5}
  have hδ₀L : δ₀ * Real.log T = Real.log T ^ ((3:ℝ)/5) := by
    calc δ₀ * Real.log T = Real.log T ^ (-(2:ℝ)/5) * Real.log T ^ (1:ℝ) := by
          rw [hδ₀, Real.rpow_one]
      _ = Real.log T ^ (-(2:ℝ)/5 + 1) := (Real.rpow_add hLpos _ _).symm
      _ = Real.log T ^ ((3:ℝ)/5) := by norm_num
  have hδ₀pow : δ₀ ^ (-(3 / 2 : ℝ)) = Real.log T ^ ((3:ℝ)/5) := by
    rw [hδ₀, ← Real.rpow_mul hLpos.le]; norm_num
  -- head piece: ∫₀^{δ₀} N_off ≤ δ₀ N(0,T) ≤ C T (log T)^{3/5}
  have hhead : ∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ) ≤ δ₀ * Ncount 0 T :=
    integral_NOff_le_mul_Ncount T hδ₀pos.le
  have hN : (Ncount 0 T : ℝ) ≤ C * T * Real.log T := hUp T hTT₁
  have hhead' : δ₀ * (Ncount 0 T : ℝ) ≤ C * T * Real.log T ^ ((3:ℝ)/5) := by
    calc δ₀ * (Ncount 0 T : ℝ) ≤ δ₀ * (C * T * Real.log T) :=
          mul_le_mul_of_nonneg_left hN hδ₀pos.le
      _ = C * T * (δ₀ * Real.log T) := by ring
      _ = C * T * Real.log T ^ ((3:ℝ)/5) := by rw [hδ₀L]
  -- tail piece: ∫_{δ₀}^{1/2} N_off ≤ ∫_{δ₀}^{1/2} (A₂ δ^{-5/2} + B₂) T ≤ ((2/3) A₂ (log T)^{3/5} + B₂/2) T
  have htail : ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ)
      ≤ ∫ δ in δ₀..(1 / 2), (A₂ * δ ^ (-(5 / 2 : ℝ)) + B₂) * T := by
    refine intervalIntegral.integral_mono_on hδ₀le (NOff_intervalIntegrable 0 T δ₀ (1 / 2))
      (rpow_tail_intervalIntegrable A₂ B₂ T hδ₀pos hδ₀le) (fun δ hδ => ?_)
    exact hBL δ (lt_of_lt_of_le hδ₀pos hδ.1) hδ.2 T hT2
  have htail' := integral_rpow_tail_le A₂ B₂ T hA₂ hB₂ hT0 hδ₀pos hδ₀le
  rw [hδ₀pow] at htail'
  -- (log T)^{3/5} ≥ 1 absorbs the constant term
  have hone : 1 ≤ Real.log T ^ ((3:ℝ)/5) := Real.one_le_rpow hL1 (by norm_num)
  have hB₂T : B₂ / 2 * T ≤ B₂ / 2 * T * Real.log T ^ ((3:ℝ)/5) := by
    have h := mul_le_mul_of_nonneg_left hone (by positivity : (0:ℝ) ≤ B₂ / 2 * T)
    linarith
  -- assemble
  rw [reservoirMass_eq_integral, integral_NOff_split T δ₀]
  calc (∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ)) + ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ)
      ≤ δ₀ * Ncount 0 T + (2 / 3 * A₂ * Real.log T ^ ((3:ℝ)/5) + B₂ / 2) * T :=
        add_le_add hhead (htail.trans htail')
    _ ≤ C * T * Real.log T ^ ((3:ℝ)/5)
          + (2 / 3 * A₂ * Real.log T ^ ((3:ℝ)/5) + B₂ / 2) * T := by linarith
    _ ≤ (C + 2 / 3 * A₂ + B₂ / 2) * T * Real.log T ^ ((3:ℝ)/5) := by linarith

/-- **The reservoir-mass bound, relative to N(0,T).** `reservoirMass T ≤ A · (log T)^{-2/5} · N(0,T)` for all large `T`: from
`reservoirMass_le_rpow` and the lower bound `c T log T ≤ N(0,T)` of `mul_log_le_Ncount`
(`A = |A₁| / c`). -/
theorem reservoirMass_le_Ncount_mul :
    ∃ A : ℝ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      reservoirMass T ≤ A * (Real.log T) ^ (-(2:ℝ)/5) * Ncount 0 T := by
  obtain ⟨A₁, T₁, h₁⟩ := reservoirMass_le_rpow
  obtain ⟨c, hc, T₂, hT₂, hLow⟩ := Zeta23.MNF_mul_log_le_Ncount
  refine ⟨|A₁| / c, max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_max_right _ _) hT
  have hT2 : 2 ≤ T := le_trans hT₂ hTT₂
  have hTpos : 0 < T := by linarith
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have h1 := h₁ T hTT₁
  have h2 := hLow T hTT₂
  have hP : 0 ≤ Real.log T ^ (-(2:ℝ)/5) := Real.rpow_nonneg hLpos.le _
  have hE : Real.log T ^ (-(2:ℝ)/5) * Real.log T = Real.log T ^ ((3:ℝ)/5) := by
    calc Real.log T ^ (-(2:ℝ)/5) * Real.log T
        = Real.log T ^ (-(2:ℝ)/5) * Real.log T ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = Real.log T ^ (-(2:ℝ)/5 + 1) := (Real.rpow_add hLpos _ _).symm
      _ = Real.log T ^ ((3:ℝ)/5) := by norm_num
  have hTL : T * Real.log T ≤ (Ncount 0 T : ℝ) / c := by
    rw [le_div_iff₀ hc]
    linarith [h2]
  have hpos : 0 ≤ Real.log T ^ ((3:ℝ)/5) := Real.rpow_nonneg hLpos.le _
  calc reservoirMass T ≤ A₁ * T * Real.log T ^ ((3:ℝ)/5) := h1
    _ ≤ |A₁| * T * Real.log T ^ ((3:ℝ)/5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A₁) hTpos.le) hpos
    _ = |A₁| * Real.log T ^ (-(2:ℝ)/5) * (T * Real.log T) := by rw [← hE]; ring
    _ ≤ |A₁| * Real.log T ^ (-(2:ℝ)/5) * ((Ncount 0 T : ℝ) / c) :=
        mul_le_mul_of_nonneg_left hTL (mul_nonneg (abs_nonneg _) hP)
    _ = |A₁| / c * Real.log T ^ (-(2:ℝ)/5) * Ncount 0 T := by ring

/-- **The mean distance from the line tends to zero.** The multiplicity-weighted mean distance of the zeros from the critical line
tends to zero: `reservoirMass T / N(0,T) → 0` as `T → ∞`.  Squeeze between `0` and
`A (log T)^{-2/5} → 0` (`Real.tendsto_log_atTop`, `tendsto_rpow_neg_atTop`), using
`reservoirMass_le_Ncount_mul` and `N(0,T) > 0` for large `T` (from `mul_log_le_Ncount`). -/
theorem meanDisplacement_tendsto_zero :
    Filter.Tendsto (fun T : ℝ => reservoirMass T / (Ncount 0 T : ℝ)) Filter.atTop (nhds 0) := by
  obtain ⟨A, T₁, hA⟩ := reservoirMass_le_Ncount_mul
  obtain ⟨c, hc, T₂, hT₂, hLow⟩ := Zeta23.MNF_mul_log_le_Ncount
  have hup : Filter.Tendsto (fun T : ℝ => A * Real.log T ^ (-(2:ℝ)/5)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-(2:ℝ)/5)) Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop (y := (2:ℝ)/5) (by norm_num)
      have e : (fun x : ℝ => x ^ (-(2:ℝ)/5)) = fun x : ℝ => x ^ (-((2:ℝ)/5)) := by
        funext x; rw [neg_div]
      rw [e]; exact h
    have h2 : Filter.Tendsto (fun T : ℝ => Real.log T ^ (-(2:ℝ)/5)) Filter.atTop (nhds 0) :=
      h1.comp Real.tendsto_log_atTop
    have h3 := h2.const_mul A
    rw [mul_zero] at h3
    exact h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact Filter.Eventually.of_forall
      (fun T => div_nonneg (reservoirMass_nonneg T) (Nat.cast_nonneg _))
  · rw [Filter.eventually_atTop]
    refine ⟨max T₁ T₂, fun T hT => ?_⟩
    have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
    have hTT₂ : T₂ ≤ T := le_trans (le_max_right _ _) hT
    have hT2 : 2 ≤ T := le_trans hT₂ hTT₂
    have hTpos : 0 < T := by linarith
    have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hN : 0 < (Ncount 0 T : ℝ) :=
      lt_of_lt_of_le (mul_pos (mul_pos hc hTpos) hLpos) (hLow T hTT₂)
    rw [div_le_iff₀ hN]
    exact hA T hTT₁

end MNF.RH

end ReservoirBound

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════

-- No `#print axioms` is run in this file.  The audit of every theorem and lemma above, §1–§6,
-- is run by name from `MNF_AuditDensity.lean` at the tree root (the four `noncomputable def`s
-- CG, meanSquareB, A₀, reservoirMass carry no proof term to audit).
