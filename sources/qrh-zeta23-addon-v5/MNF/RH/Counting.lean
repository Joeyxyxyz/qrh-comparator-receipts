/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — COUNTING VOCABULARY  (MNF/RH/Counting.lean)
[BOOKKEEPING] zeta23's window-counting functions, restated over MNF's names.
═══════════════════════════════════════════════════════════════════════
This file carries the counting vocabulary of the zeta23 comparator challenge
(ChallengeDeps.lean §1: zerosIn, Ncount, Ndist, N0star, N0simple, cMT) over
MNF's own definitions `is_nontrivial_zero` (for IsNontrivialZero) and
`zeta_order` (for zeroMult).  The bodies are spelled exactly as zeta23 spells
them, so that a later delegation file can restate zeta23's theorems over these
names and have each delegation typecheck by definitional unfolding.  This file
imports nothing from Zeta23/, Challenge, ChallengeDeps or Solution.

Everything proved here is Mathlib-only bookkeeping about these counts:

  §1  definitions   zerosIn, Ncount, Ndist, N0star, N0simple, cMT
  §2  finiteness    zerosIn_finite  (Mathlib: zeros of ζ in a compact box are finite);
                    every count below is an `ncard`/`∑ᶠ` over `zerosIn`, which would be
                    vacuously 0 on an infinite set, so every statement about counts
                    threads this lemma.
  §3  inequalities  Ndist_le_Ncount, N0star_le_Ndist, N0simple_le_N0star
  §4  restatements  riemannHypothesis_iff_window_counts
                      (RH ⟺ the two multiplicity-free counts N₀*, N_d agree on every window),
                    allZerosSimple_iff_window_counts
                      (AllZerosSimple ⟺ total and distinct counts agree on every window),
                    N0simple_eq_deriv_form  (simple ⟺ ζ' ≠ 0, via order_one_iff_deriv).

The two equivalences of §4 are restatements of the definitions, not density
results: they say nothing about proportions of zeros, and nothing here advances
RH or the simple-zeros conjecture.

Register: [PROVED] for every theorem below (kernel-checked; see the
`#print axioms` block at the end: only propext, Classical.choice, Quot.sound).
-/
import MNF.RH.Hypotheses
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Complex.Basic

namespace MNF.RH

open Complex Set
open scoped BigOperators

/-! ### §1 Definitions (zeta23's ChallengeDeps.lean §1, over MNF's names) -/

/-- The nontrivial zeros with ordinate in the window (T₁, T₂]: {ρ | ζ(ρ) = 0, 0 < Re ρ < 1,
T₁ < Im ρ ≤ T₂}.  Positive-ordinate window, not |Im ρ| (a zero and its conjugate lie in different
windows); `T₁ T₂` range over all of ℝ, so windows below the real axis are allowed.  zeta23's
`zerosIn` with `IsNontrivialZero` replaced by `is_nontrivial_zero`. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): the nontrivial zeros with T₁ < Im ρ ≤ T₂, counted WITH multiplicity
(`∑ᶠ` is Mathlib's finite sum; finiteness of the window is `zerosIn_finite` below).
zeta23's `Ncount` with `zeroMult` replaced by `zeta_order`. -/
noncomputable def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ

/-- N_d(T₁,T₂): the nontrivial zeros with T₁ < Im ρ ≤ T₂, each distinct zero counted once. -/
noncomputable def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀*(T₁,T₂): the DISTINCT zeros ON the critical line Re ρ = 1/2 with T₁ < Im ρ ≤ T₂. -/
noncomputable def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂): the SIMPLE zeros (multiplicity exactly 1) ON the critical line with
T₁ < Im ρ ≤ T₂. -/
noncomputable def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeta_order ρ = 1}).ncard

/-- zeta23's Montgomery–Taylor constant c₁* = √2·tan ϑ / (1 + ϑ·tan ϑ) at ϑ = 1/√2, copied
character-for-character from ChallengeDeps.lean §3 (numerically 0.7532960…). -/
noncomputable def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

/-! ### §2 Finiteness of a window -/

theorem mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ zerosIn T₁ T₂ ↔ is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂ :=
  Iff.rfl

theorem zerosIn_subset_zetaZeros (T₁ T₂ : ℝ) : zerosIn T₁ T₂ ⊆ ZetaZeros :=
  fun _ h => h.1

theorem zerosIn_mono {T₁ T₁' T₂ T₂' : ℝ} (h₁ : T₁' ≤ T₁) (h₂ : T₂ ≤ T₂') :
    zerosIn T₁ T₂ ⊆ zerosIn T₁' T₂' :=
  fun _ ⟨hρ, hlo, hhi⟩ => ⟨hρ, lt_of_le_of_lt h₁ hlo, le_trans hhi h₂⟩

/-- A window lies in the compact box `Re ∈ [0,1]`, `Im ∈ [T₁,T₂]` intersected with the zero set
of `ζ` (Mathlib's `riemannZetaZeros`). -/
theorem zerosIn_subset_box (T₁ T₂ : ℝ) :
    zerosIn T₁ T₂ ⊆ (Icc (0 : ℝ) 1 ×ℂ Icc T₁ T₂) ∩ riemannZetaZeros := by
  rintro ρ ⟨hρ, h1, h2⟩
  exact ⟨mem_reProdIm.2 ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨h1.le, h2⟩⟩, hρ.1⟩

/-- Every window contains finitely many nontrivial zeros (Mathlib's
`IsCompact.inter_riemannZetaZeros_finite` on the compact box). -/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite :=
  ((isCompact_Icc.reProdIm isCompact_Icc).inter_riemannZetaZeros_finite).subset
    (zerosIn_subset_box T₁ T₂)

/-- The count with multiplicity as a `Finset` sum, given any proof that the window is finite
(`zerosIn_finite` supplies one; the proof is a hypothesis here so that no theorem appears inside
a statement). -/
theorem Ncount_eq_sum {T₁ T₂ : ℝ} (hfin : (zerosIn T₁ T₂).Finite) :
    Ncount T₁ T₂ = ∑ ρ ∈ hfin.toFinset, zeta_order ρ :=
  finsum_mem_eq_finite_toFinset_sum _ _

/-- The distinct count as a `Finset` sum of ones, given any proof that the window is finite. -/
theorem Ndist_eq_sum_ones {T₁ T₂ : ℝ} (hfin : (zerosIn T₁ T₂).Finite) :
    Ndist T₁ T₂ = ∑ _ρ ∈ hfin.toFinset, 1 := by
  unfold Ndist
  rw [ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones]

/-! ### §3 Inequalities between the counts -/

/-- Each zero has multiplicity at least one (`zeta_order_ge_one`), so the distinct count is at
most the count with multiplicity. -/
theorem Ndist_le_Ncount (T₁ T₂ : ℝ) : Ndist T₁ T₂ ≤ Ncount T₁ T₂ := by
  rw [Ncount_eq_sum (zerosIn_finite T₁ T₂), Ndist_eq_sum_ones (zerosIn_finite T₁ T₂)]
  exact Finset.sum_le_sum fun ρ hρ =>
    zeta_order_ge_one ((zerosIn_finite T₁ T₂).mem_toFinset.1 hρ).1

theorem N0star_le_Ndist (T₁ T₂ : ℝ) : N0star T₁ T₂ ≤ Ndist T₁ T₂ :=
  ncard_le_ncard inter_subset_left (zerosIn_finite T₁ T₂)

theorem N0simple_le_N0star (T₁ T₂ : ℝ) : N0simple T₁ T₂ ≤ N0star T₁ T₂ :=
  ncard_le_ncard inter_subset_left ((zerosIn_finite T₁ T₂).subset inter_subset_left)

/-! ### §4 Restatements -/

/-- **Mathlib's `RiemannHypothesis` ⟺ on every window (T₁, T₂], T₁ T₂ ∈ ℝ, the number of distinct
zeros on the line equals the number of distinct zeros.**  A restatement of
`riemannHypothesis_iff_strip`, not a density result: both sides are `ncard`s (no multiplicity
anywhere in this statement), and it says only that the on-line subset of a window is the whole
window.  (⇐ uses finiteness: a zero off the line lies in the window (Im ρ − 1, Im ρ], where the
on-line subset is then a proper subset of a finite set, hence of smaller `ncard`; windows of
negative ordinate are included, so every zero is reached.) -/
theorem riemannHypothesis_iff_window_counts :
    RiemannHypothesis ↔ ∀ T₁ T₂ : ℝ, N0star T₁ T₂ = Ndist T₁ T₂ := by
  rw [riemannHypothesis_iff_strip]
  constructor
  · intro h T₁ T₂
    unfold N0star Ndist
    congr 1
    exact inter_eq_left.2 fun ρ hρ => h ρ hρ.1
  · intro h ρ hρ
    by_contra hne
    have hmem : ρ ∈ zerosIn (ρ.im - 1) ρ.im := ⟨hρ, by linarith, le_rfl⟩
    have hssub : zerosIn (ρ.im - 1) ρ.im ∩ {ρ | ρ.re = 1 / 2} ⊂ zerosIn (ρ.im - 1) ρ.im :=
      ⟨inter_subset_left, fun hsub => hne (hsub hmem).2⟩
    have hlt := ncard_lt_ncard hssub (zerosIn_finite (ρ.im - 1) ρ.im)
    have h' := h (ρ.im - 1) ρ.im
    unfold N0star Ndist at h'
    exact hlt.ne h'

/-- **AllZerosSimple ⟺ on every window, the count with multiplicity equals the distinct count.**
A restatement of the definition of `AllZerosSimple`, not a density result.  (⇐ uses finiteness:
a zero of multiplicity ≥ 2 makes the sum of multiplicities over its window strictly larger
than the number of terms.) -/
theorem allZerosSimple_iff_window_counts :
    AllZerosSimple ↔ ∀ T₁ T₂ : ℝ, Ncount T₁ T₂ = Ndist T₁ T₂ := by
  constructor
  · intro h T₁ T₂
    rw [Ncount_eq_sum (zerosIn_finite T₁ T₂), Ndist_eq_sum_ones (zerosIn_finite T₁ T₂)]
    exact Finset.sum_congr rfl fun ρ hρ =>
      h ρ ((zerosIn_finite T₁ T₂).mem_toFinset.1 hρ).1
  · intro h ρ hρ
    by_contra hne
    have h2 : 2 ≤ zeta_order ρ := by
      have := zeta_order_ge_one hρ
      omega
    have hmem : ρ ∈ (zerosIn_finite (ρ.im - 1) ρ.im).toFinset :=
      (zerosIn_finite (ρ.im - 1) ρ.im).mem_toFinset.2 ⟨hρ, by linarith, le_rfl⟩
    have hlt : ∑ _σ ∈ (zerosIn_finite (ρ.im - 1) ρ.im).toFinset, 1 <
        ∑ σ ∈ (zerosIn_finite (ρ.im - 1) ρ.im).toFinset, zeta_order σ :=
      Finset.sum_lt_sum
        (fun σ hσ => zeta_order_ge_one ((zerosIn_finite (ρ.im - 1) ρ.im).mem_toFinset.1 hσ).1)
        ⟨ρ, hmem, by omega⟩
    have h' := h (ρ.im - 1) ρ.im
    rw [Ncount_eq_sum (zerosIn_finite (ρ.im - 1) ρ.im),
      Ndist_eq_sum_ones (zerosIn_finite (ρ.im - 1) ρ.im)] at h'
    exact hlt.ne' h'

/-- On a window, "simple and on the line" may be spelled with `ζ' ≠ 0` in place of
`zeta_order = 1` (`order_one_iff_deriv`, available because membership in `zerosIn` gives
`is_nontrivial_zero`). -/
theorem N0simple_eq_deriv_form (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ =
      (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | deriv riemannZeta ρ ≠ 0}).ncard := by
  unfold N0simple
  congr 1
  ext ρ
  simp only [mem_inter_iff, mem_ofPred_eq, mem_zerosIn]
  exact and_congr_right fun h => order_one_iff_deriv h.1.1

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.mem_zerosIn
#print axioms MNF.RH.zerosIn_subset_zetaZeros
#print axioms MNF.RH.zerosIn_mono
#print axioms MNF.RH.zerosIn_subset_box
#print axioms MNF.RH.zerosIn_finite
#print axioms MNF.RH.Ncount_eq_sum
#print axioms MNF.RH.Ndist_eq_sum_ones
#print axioms MNF.RH.Ndist_le_Ncount
#print axioms MNF.RH.N0star_le_Ndist
#print axioms MNF.RH.N0simple_le_N0star
#print axioms MNF.RH.riemannHypothesis_iff_window_counts
#print axioms MNF.RH.allZerosSimple_iff_window_counts
#print axioms MNF.RH.N0simple_eq_deriv_form
