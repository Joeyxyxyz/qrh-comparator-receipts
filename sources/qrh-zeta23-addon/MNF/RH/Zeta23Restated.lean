/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — ZETA23 THEOREMS A–D, RESTATED OVER MNF'S NAMES  (MNF/RH/Zeta23Restated.lean)
[RESTATEMENT | zeta23] zeta23's Theorems A–D stated over MNF's own definitions.
═══════════════════════════════════════════════════════════════════════
This file restates the eleven ζ-theorems of the zeta23 comparator challenge
(Challenge.lean: Theorems A, B, C, D, in dyadic (T, 2T] and cumulative (0, T]
forms; NOT the six Dirichlet-character statements of Theorem E, for which MNF
has no vocabulary) over MNF's counting vocabulary (MNF/RH/Counting.lean:
`zerosIn`, `Ncount`, `Ndist`, `N0star`, `N0simple`, `cMT`, built on
`is_nontrivial_zero` and `zeta_order`).
Every theorem of §1–§4 is proved by DELEGATION to the corresponding
root-namespace theorem of zeta23's Solution.lean.  MNF's counting definitions
are spelled character-for-character as zeta23's (ChallengeDeps.lean §1, §3)
with `IsNontrivialZero` replaced by `is_nontrivial_zero` and `zeroMult` by
`zeta_order`, whose bodies are in turn identical; so each delegation
typechecks by definitional unfolding in the kernel.  §5 rewrites two of these
through Counting.lean's bookkeeping lemmas.  No new mathematics is proved in
this file.

Reliability.  Each theorem of §1–§4 is zeta23's theorem under a change of
names that the kernel verifies by unfolding, so it carries zeta23's status and
nothing more: a reader must trust (i) the Comparator receipt for zeta23, if
one has been issued for this checkout (statement equality against
Challenge.lean, axiom audit, kernel replay of the Zeta23 library), (ii) that
this checkout is the receipted one, and (iii) this file's own build, which is
where the kernel checks that MNF's definitions unfold to zeta23's.  A reader
who does not trust (i) should regard every theorem here as having whatever
status the Zeta23 library has.

What they do NOT do.  A proportion of zeros, however large, is not a statement
about every zero.  Nothing in this file discharges, weakens, or bears on
`SpectralGapHyp`, `AllZerosSimple`, `MultiplicityBoundOne`, or
`DerivativeNonvanishing` (MNF/RH/Core.lean, Hypotheses.lean), all of which
quantify over EVERY nontrivial zero.  Nothing here advances RH or the
simple-zeros conjecture.  These theorems do not use the 7/8 theorem, and must
not be combined with it in one sentence: they are statements about proportions
of zeros on windows (T, 2T] and (0, T], and the 7/8 theorem is a statement
about a different quantity.

Contents
  §1  Theorem A  twoThirdsOnLine, twoThirdsOnLine_cumulative
  §2  Theorem B  twoThirdsSimpleOnLine, twoThirdsSimpleOnLine_cumulative
  §3  Theorem C  fiveSixthsDistinct, fiveSixthsDistinct_cumulative
  §4  Theorem D  montgomeryTaylorOnLine, montgomeryTaylorSimpleOnLine,
                 montgomeryTaylorSimpleOnLine_cumulative, montgomeryTaylorDistinct,
                 montgomeryTaylorDistinct_cumulative
  §5  two corollaries in MNF vocabulary (restatements, via Counting.lean's
      bookkeeping only): twoThirdsOnLineDerivNeZero (Theorem B with `ζ' ≠ 0` in
      place of `zeta_order = 1`), fiveSixthsDistinct_sandwich (Theorem C together
      with the trivial `Ndist ≤ Ncount`).

Register: [RESTATEMENT | zeta23] for every theorem in this file, §5 included:
§1–§4 are delegated, §5 are two of them rewritten through Counting.lean's
[BOOKKEEPING] lemmas and inherit exactly the §1–§4 status (see the
`#print axioms` block at the end: only propext, Classical.choice, Quot.sound,
inherited from the Zeta23 library through Solution).
-/
import MNF.RH.Counting
import Solution

namespace MNF.RH

open Complex Set

/-! ### §1 Theorem A — at least 2/3 of the zeros are on the critical line -/

/-- **zeta23 Theorem A (dyadic windows), over MNF's names.**  For every ε > 0 and all
sufficiently large T, (2/3 − ε)·N(T,2T) ≤ N₀*(T,2T): the zeros with T < Im ρ ≤ 2T, counted
with multiplicity on the left and as distinct points of the critical line on the right.
Delegated to `two_thirds_on_critical_line` (Solution.lean); typechecks by unfolding. -/
theorem twoThirdsOnLine :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  _root_.two_thirds_on_critical_line

/-- **zeta23 Theorem A (cumulative windows (0,T]), over MNF's names.**
Delegated to `two_thirds_on_critical_line_cumulative`. -/
theorem twoThirdsOnLine_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  _root_.two_thirds_on_critical_line_cumulative

/-! ### §2 Theorem B — at least 2/3 of the zeros are simple and on the critical line -/

/-- **zeta23 Theorem B (dyadic windows), over MNF's names.**  (2/3 − ε)·N(T,2T) ≤ N₀ˢ(T,2T)
for all large T, where N₀ˢ counts the zeros on the line with `zeta_order = 1`.
Delegated to `two_thirds_simple_on_critical_line`. -/
theorem twoThirdsSimpleOnLine :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  _root_.two_thirds_simple_on_critical_line

/-- **zeta23 Theorem B (cumulative windows), over MNF's names.**
Delegated to `two_thirds_simple_on_critical_line_cumulative`. -/
theorem twoThirdsSimpleOnLine_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  _root_.two_thirds_simple_on_critical_line_cumulative

/-! ### §3 Theorem C — at least 5/6 of the zeros are distinct -/

/-- **zeta23 Theorem C (dyadic windows), over MNF's names.**  (5/6 − ε)·N(T,2T) ≤ N_d(T,2T)
for all large T.  Delegated to `five_sixths_distinct`. -/
theorem fiveSixthsDistinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  _root_.five_sixths_distinct

/-- **zeta23 Theorem C (cumulative windows), over MNF's names.**
Delegated to `five_sixths_distinct_cumulative`. -/
theorem fiveSixthsDistinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  _root_.five_sixths_distinct_cumulative

/-! ### §4 Theorem D — the Montgomery–Taylor window (constant `cMT`) -/

/-- **zeta23 Theorem D (on-line, dyadic windows), over MNF's names.**
(2 − 1/c₁* − ε)·N(T,2T) ≤ N₀*(T,2T) for all large T, with c₁* = `cMT` (numerically
2 − 1/c₁* = 0.67250…; the decimal is not part of the statement).  MNF's `cMT` and zeta23's are
spelled identically, so the delegation to `montgomery_taylor_on_critical_line` unfolds. -/
theorem montgomeryTaylorOnLine :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  _root_.montgomery_taylor_on_critical_line

/-- **zeta23 Theorem D (simple on-line, dyadic windows), over MNF's names.**
Delegated to `montgomery_taylor_simple_on_critical_line_mult`. -/
theorem montgomeryTaylorSimpleOnLine :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  _root_.montgomery_taylor_simple_on_critical_line_mult

/-- **zeta23 Theorem D (simple on-line, cumulative windows), over MNF's names.**
Delegated to `montgomery_taylor_simple_on_critical_line_mult_cumulative`. -/
theorem montgomeryTaylorSimpleOnLine_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  _root_.montgomery_taylor_simple_on_critical_line_mult_cumulative

/-- **zeta23 Theorem D (distinct, dyadic windows), over MNF's names.**
(3/2 − c₁*⁻¹/2 − ε)·N(T,2T) ≤ N_d(T,2T) for all large T.
Delegated to `montgomery_taylor_distinct_mult`. -/
theorem montgomeryTaylorDistinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  _root_.montgomery_taylor_distinct_mult

/-- **zeta23 Theorem D (distinct, cumulative windows), over MNF's names.**
Delegated to `montgomery_taylor_distinct_mult_cumulative`. -/
theorem montgomeryTaylorDistinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  _root_.montgomery_taylor_distinct_mult_cumulative

/-! ### §5 Corollaries in MNF vocabulary (restatements only) -/

/-- [RESTATEMENT | zeta23] **Theorem B with `ζ' ≠ 0` in place of `zeta_order = 1`: 2/3 of the
zeros are on the line with `ζ' ≠ 0`.**  A restatement of `twoThirdsSimpleOnLine` through
`N0simple_eq_deriv_form` (Counting.lean, itself a restatement via `order_one_iff_deriv`): the
simple on-line zeros of a window are exactly the on-line zeros of the window at which ζ' ≠ 0.
It says nothing about `DerivativeNonvanishing`, which quantifies over every zero. -/
theorem twoThirdsOnLineDerivNeZero :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤
      ((zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | deriv riemannZeta ρ ≠ 0}).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := twoThirdsSimpleOnLine ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [← N0simple_eq_deriv_form]
  exact h T hT

/-- [RESTATEMENT | zeta23] **Theorem C sandwiched by the trivial bound.**  A restatement of
`fiveSixthsDistinct` together with `Ndist_le_Ncount` (Counting.lean): on dyadic windows, for all
large T, (5/6 − ε)·N(T,2T) ≤ N_d(T,2T) ≤ N(T,2T).  The upper bound is bookkeeping (each zero has
multiplicity ≥ 1); nothing here says anything about `AllZerosSimple` or `MultiplicityBoundOne`. -/
theorem fiveSixthsDistinct_sandwich :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) ∧
        (Ndist T (2 * T) : ℝ) ≤ Ncount T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := fiveSixthsDistinct ε hε
  exact ⟨T₀, fun T hT => ⟨h T hT, Nat.cast_le.2 (Ndist_le_Ncount T (2 * T))⟩⟩

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.twoThirdsOnLine
#print axioms MNF.RH.twoThirdsOnLine_cumulative
#print axioms MNF.RH.twoThirdsSimpleOnLine
#print axioms MNF.RH.twoThirdsSimpleOnLine_cumulative
#print axioms MNF.RH.fiveSixthsDistinct
#print axioms MNF.RH.fiveSixthsDistinct_cumulative
#print axioms MNF.RH.montgomeryTaylorOnLine
#print axioms MNF.RH.montgomeryTaylorSimpleOnLine
#print axioms MNF.RH.montgomeryTaylorSimpleOnLine_cumulative
#print axioms MNF.RH.montgomeryTaylorDistinct
#print axioms MNF.RH.montgomeryTaylorDistinct_cumulative
#print axioms MNF.RH.twoThirdsOnLineDerivNeZero
#print axioms MNF.RH.fiveSixthsDistinct_sandwich
