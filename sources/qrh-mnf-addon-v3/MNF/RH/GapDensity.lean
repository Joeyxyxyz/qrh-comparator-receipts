/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — GAP ⟹ DENSITY ONE ON THE LINE  (MNF/RH/GapDensity.lean)
[CONDITIONAL] the one place the MNF gap hypothesis does work that is not a
restatement: with a zero-density input of Bohr–Landau type, a gap at any Δ > 0
forces density one of the zeros onto the critical line.
═══════════════════════════════════════════════════════════════════════
Everything here is Mathlib-only bookkeeping on top of `MNF.RH.Counting`, with
every assumption about ζ carried as an explicit named `Prop` argument.  Nothing
is asserted about ζ beyond Mathlib; the file adds no axiom (see the
`#print axioms` block at the end: only propext, Classical.choice, Quot.sound).

Register of the two [LITERATURE] Props, which no Lean library supplies as of
2026-10-28 (Palomar holds one-sided zero-density estimates at Lean v4.35.0-rc2
only; nothing of this kind is in Mathlib at the pin used here):

  BohrLandau          [LITERATURE]  Bohr–Landau 1914: for every fixed δ > 0 the zeros with
                                    |Re ρ − 1/2| ≥ δ and 0 < Im ρ ≤ T number O(T), i.e.
                                    o(T log T).  Stated here with multiplicity.
  NcountSuperlinear   [LITERATURE]  N(T) grows faster than every linear function; a
                                    consequence of Riemann–von Mangoldt, N(T) ~ (T/2π) log T.

What is proved [PROVED], with those Props as hypotheses:

  §1  definitions   N0 (on-line count WITH multiplicity, so that the split
                    Ncount = N0 + NOff is exact; `N0star` of Counting.lean is the
                    distinct count), NOff (zeros at distance ≥ δ from the line, with
                    multiplicity), BohrLandau, NcountSuperlinear
  §2  inequalities  N0_le_Ncount, NOff_le_Ncount  (finsum over a subset of a finite set)
  §3  the split     gap_forces_NOff_eq: under SpectralGapHyp Δ with Δ > 0, every window
                    is the disjoint union of its on-line zeros and its zeros at distance
                    ≥ Δ, so Ncount = N0 + NOff Δ exactly.  The binder 0 < Δ is mandatory:
                    for Δ ≤ 0 the two pieces overlap and the equation is false.
  §4  density       on_line_density_one_of_gap: BohrLandau + NcountSuperlinear +
                    SpectralGapHyp Δ (Δ > 0) ⟹ for every ε > 0, eventually
                    (1 − ε)·N(0,T) ≤ N₀(0,T).

How to read the conclusion.  "Density one on the line" is strictly weaker than RH: it
allows infinitely many zeros off the line as long as they are o(N(T)).  For Δ ≥ 1/2 the
hypothesis SpectralGapHyp Δ is RH itself, unconditionally (`riemannHypothesis_iff_gap_half`
in Gap.lean).  Given the additional hypothesis `ZeroFreeRightOf (7/8)` — a zero-free
half-plane Re s > 7/8, which is NOT proved in this tree or in Mathlib and appears only as
an explicit binder (`rh_of_gap_of_zeroFree`, `riemannHypothesis_iff_gap_of_zeroFree`) —
the threshold drops to Δ > 3/8.  So the unconditional content of this file is for
0 < Δ < 1/2, and for Δ ≤ 3/8 under that extra hypothesis.  By
`spectralGapHyp_iff_zeroFree_strip` the hypothesis for such Δ is a zero-free strip
1/2 < Re s < 1/2 + Δ next to the line, and "zero-free strip next to the line plus
Bohr–Landau gives density one" is a folklore implication, not new mathematics: the gap
removes exactly the zeros Bohr–Landau does not bound, and the remaining off-line count is
O(T) = o(N(T)).  Nothing here advances RH or the simple-zeros conjecture.
-/
import MNF.RH.Counting

namespace MNF.RH

open Complex Set
open scoped BigOperators

/-- N₀(T₁,T₂): the nontrivial zeros ON the critical line Re ρ = 1/2 with T₁ < Im ρ ≤ T₂,
counted WITH multiplicity (`N0star` of Counting.lean is the distinct count; this one is needed
so that `Ncount = N0 + NOff` is exact under a gap). -/
noncomputable def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeta_order ρ

/-- N_off(δ; T₁,T₂): the nontrivial zeros with T₁ < Im ρ ≤ T₂ at distance at least δ from the
critical line, |Re ρ − 1/2| ≥ δ, counted WITH multiplicity. -/
noncomputable def NOff (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}, zeta_order ρ

/-- [LITERATURE] Bohr–Landau (1914): for every fixed δ > 0, the zeros at distance ≥ δ from the
line with 0 < Im ρ ≤ T number O(T).  Not in Mathlib or any Lean library as of 2026-10-28; a
named `Prop`, never asserted. -/
def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T

/-- [LITERATURE] N(T) dominates every linear function eventually; a consequence of the
Riemann–von Mangoldt formula N(T) ~ (T/2π) log T.  Not in Mathlib as of 2026-10-28; a named
`Prop`, never asserted. -/
def NcountSuperlinear : Prop := ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ T ≥ T₀, c * T ≤ (Ncount 0 T : ℝ)

/-- The on-line count with multiplicity is at most the full count: a `∑ᶠ` over a subset of a
finite set of nonnegative terms. -/
theorem N0_le_Ncount (T₁ T₂ : ℝ) : N0 T₁ T₂ ≤ Ncount T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have hfin' : (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).Finite := hfin.subset inter_subset_left
  unfold N0
  rw [Ncount_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin']
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finite.toFinset_subset_toFinset.2 inter_subset_left) (fun _ _ _ => Nat.zero_le _)

/-- The off-line count with multiplicity is at most the full count. -/
theorem NOff_le_Ncount (δ T₁ T₂ : ℝ) : NOff δ T₁ T₂ ≤ Ncount T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have hfin' : (zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}).Finite :=
    hfin.subset inter_subset_left
  unfold NOff
  rw [Ncount_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin']
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finite.toFinset_subset_toFinset.2 inter_subset_left) (fun _ _ _ => Nat.zero_le _)

/-- **Under a gap at Δ > 0, every window splits exactly.**  `SpectralGapHyp Δ` says each
nontrivial zero has Re ρ = 1/2 or |Re ρ − 1/2| ≥ Δ, so the window is the disjoint union of its
on-line zeros and its zeros at distance ≥ Δ (disjoint because Δ > 0), and the sums of
multiplicities add (`finsum_mem_union`, with finiteness from `zerosIn_finite`).  The binder
`0 < Δ` is mandatory: for Δ ≤ 0 every on-line zero also lies in the second piece and the
equation fails. -/
theorem gap_forces_NOff_eq {Δ : ℝ} (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) (T₁ T₂ : ℝ) :
    Ncount T₁ T₂ = N0 T₁ T₂ + NOff Δ T₁ T₂ := by
  have hfin := zerosIn_finite T₁ T₂
  have hunion : zerosIn T₁ T₂ =
      (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}) ∪ (zerosIn T₁ T₂ ∩ {ρ | Δ ≤ |ρ.re - 1 / 2|}) := by
    ext ρ
    constructor
    · intro hρ
      rcases hgap (ρ.re - 1 / 2) ⟨ρ, hρ.1, rfl⟩ with h0 | hge
      · left
        exact ⟨hρ, show ρ.re = 1 / 2 by linarith⟩
      · right
        exact ⟨hρ, hge⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2})
      (zerosIn T₁ T₂ ∩ {ρ | Δ ≤ |ρ.re - 1 / 2|}) := by
    rw [disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    have h1' : ρ.re = 1 / 2 := h1
    have h2' : Δ ≤ |ρ.re - 1 / 2| := h2
    rw [h1'] at h2'
    norm_num at h2'
    linarith
  have hsum := finsum_mem_union hdisj (hfin.subset inter_subset_left)
    (hfin.subset inter_subset_left) (f := zeta_order)
  rw [← hunion] at hsum
  exact hsum

/-- **Gap + Bohr–Landau + superlinear growth of N ⟹ density one on the line.**  For every
ε > 0 and all large T, (1 − ε)·N(0,T) ≤ N₀(0,T).  Proof: by `gap_forces_NOff_eq` the off-line
part of the window is exactly `NOff Δ 0 T`, Bohr–Landau bounds it by C·T, and
`NcountSuperlinear` makes C·T ≤ ε·N(0,T) eventually.  The conclusion is strictly weaker than RH
(it allows o(N(T)) zeros off the line); for Δ ≥ 1/2 the hypothesis is RH itself unconditionally
(`riemannHypothesis_iff_gap_half`), and for Δ > 3/8 it is RH under the unproved extra hypothesis
`ZeroFreeRightOf (7/8)` (see the file header).  So the content is for 0 < Δ < 1/2 (for Δ ≤ 3/8
under that extra hypothesis), where it is the folklore "zero-free strip next to the line plus
Bohr–Landau gives density one". -/
theorem on_line_density_one_of_gap (hBL : BohrLandau) (hN : NcountSuperlinear) {Δ : ℝ}
    (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T := by
  intro ε hε
  obtain ⟨C, hC⟩ := hBL Δ hΔ
  have hCpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨T₀, hT₀⟩ := hN (max C 1 / ε) (by positivity)
  refine ⟨max T₀ 2, fun T hT => ?_⟩
  have h1 := hT₀ T (le_trans (le_max_left _ _) hT)
  have h2 := hC T (le_trans (le_max_right _ _) hT)
  have hT2 : (0 : ℝ) ≤ T := by linarith [le_trans (le_max_right _ _) hT]
  have h3 : (NOff Δ 0 T : ℝ) ≤ max C 1 * T :=
    le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hT2)
  have h4 : ε * (max C 1 / ε * T) ≤ ε * Ncount 0 T := mul_le_mul_of_nonneg_left h1 hε.le
  have h4' : ε * (max C 1 / ε * T) = max C 1 * T := by field_simp
  have hsplit := gap_forces_NOff_eq hΔ hgap 0 T
  have hcast : (Ncount 0 T : ℝ) = N0 0 T + NOff Δ 0 T := by exact_mod_cast hsplit
  have h6 : (1 - ε) * (Ncount 0 T : ℝ) = Ncount 0 T - ε * Ncount 0 T := by ring
  linarith

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.N0_le_Ncount
#print axioms MNF.RH.NOff_le_Ncount
#print axioms MNF.RH.gap_forces_NOff_eq
#print axioms MNF.RH.on_line_density_one_of_gap
