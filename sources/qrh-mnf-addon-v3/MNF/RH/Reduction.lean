/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE REDUCTIONS  (MNF/RH/Reduction.lean)
What is left, stated so that any proposed mechanism is a Lean goal.
═══════════════════════════════════════════════════════════════════════
Everything here is [PROVED] from Mathlib and MNF/RH/Core, Gap, Hypotheses.
No axiom, no `sorry`.  Each theorem rewrites one of the corpus's "attack"
hypotheses into its exact mathematical content:

  §1  the gap at Δ IS a zero-free band next to the line (one side suffices)
  §2  MultipleZeroKillsGap and FischerForward ARE "RH ⟹ all zeros simple"
  §3  a real spectrum containing (ρ − 1/2)/i IS RH (the Hilbert–Pólya step),
      and a multiplicity dictionary on top of it IS simplicity
  §4  what a gap mechanism must deliver (`GapMechanism`), and that nothing
      weaker than a zero-free band can deliver it
-/
import MNF.RH.Hypotheses

namespace MNF.RH

open Complex

/-! ### §1 The gap is a zero-free band -/

/-- No nontrivial zero in the open band `1/2 < Re ρ < 1/2 + Δ`. -/
def ZeroFreeBand (Δ : ℝ) : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re ≤ 1/2 ∨ 1/2 + Δ ≤ ρ.re

/-- The MNF gap at `Δ` is exactly a zero-free band of width `Δ` to the right of the line.
The left side comes for free from `ρ ↦ 1 − ρ`. -/
theorem gap_iff_zeroFreeBand (Δ : ℝ) : SpectralGapHyp Δ ↔ ZeroFreeBand Δ := by
  constructor
  · intro h ρ hρ
    rcases h (ρ.re - 1/2) ⟨ρ, hρ, rfl⟩ with h0 | hΔ
    · left; linarith
    · rcases le_or_gt 0 (ρ.re - 1/2) with hx | hx
      · right; rw [abs_of_nonneg hx] at hΔ; linarith
      · left; linarith
  · intro h x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rcases lt_trichotomy ρ.re (1/2) with hlt | heq | hgt
    · -- reflect to the right side
      have hr := nontrivial_zero_reflect hρ
      rcases h (1 - ρ) hr with h1 | h1
      · rw [re_one_sub] at h1; linarith
      · rw [re_one_sub] at h1; right
        rw [abs_of_neg (by linarith)]; linarith
    · left; linarith
    · rcases h ρ hρ with h1 | h1
      · linarith
      · right; rw [abs_of_pos (by linarith)]; linarith

/-- "Every other zero": it is enough to kill the zeros with `Re ρ > 1/2`. -/
theorem gap_of_right_side {Δ : ℝ}
    (h : ∀ ρ : ℂ, is_nontrivial_zero ρ → 1/2 < ρ.re → 1/2 + Δ ≤ ρ.re) : SpectralGapHyp Δ := by
  rw [gap_iff_zeroFreeBand]
  intro ρ hρ
  rcases le_or_gt ρ.re (1/2) with h1 | h1
  · left; exact h1
  · right; exact h ρ hρ h1

/-- With the 7/8 region, the band to kill is `1/2 < Re ρ ≤ 7/8` and nothing else. -/
theorem rh_of_band_of_zeroFree {θ : ℝ} (hθ : ZeroFreeRightOf θ)
    (h : ∀ ρ : ℂ, is_nontrivial_zero ρ → 1/2 < ρ.re → θ < ρ.re) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_strip]
  intro ρ hρ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hr := nontrivial_zero_reflect hρ
    have := h (1 - ρ) hr (by rw [re_one_sub]; linarith)
    exact hθ (1 - ρ) this hr.1
  · exact hθ ρ (h ρ hρ hgt) hρ.1

/-! ### §2 "A multiple zero kills the gap" is the simple-zeros conjecture under RH -/

/-- The corpus hypothesis `MultipleZeroKillsGap`. -/
def MultipleZeroKillsGap : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ¬ SpectralGapHyp (1/2)

/-- The corpus hypothesis `FischerForward`: gap(1/2) ⟹ ζ' ≠ 0 at every nontrivial zero. -/
def FischerForward : Prop := SpectralGapHyp (1/2) → DerivativeNonvanishing

theorem multipleZeroKillsGap_iff : MultipleZeroKillsGap ↔ (RiemannHypothesis → AllZerosSimple) := by
  constructor
  · intro h hRH ρ hρ
    have hgap : SpectralGapHyp (1/2) := gap_of_rh hRH _
    have h1 := zeta_order_ge_one hρ
    by_contra hne
    exact h ρ hρ (by omega) hgap
  · intro h ρ hρ h2 hgap
    have hRH : RiemannHypothesis := rh_of_gap le_rfl hgap
    have := h hRH ρ hρ
    omega

theorem fischerForward_iff : FischerForward ↔ (RiemannHypothesis → AllZerosSimple) := by
  unfold FischerForward
  rw [← allZerosSimple_iff_derivativeNonvanishing]
  constructor
  · intro h hRH; exact h (gap_of_rh hRH _)
  · intro h hgap; exact h (rh_of_gap le_rfl hgap)

/-! ### §3 Hilbert–Pólya: a real spectrum is RH; a multiplicity dictionary is simplicity -/

/-- A set of real numbers that contains `(ρ − 1/2)/i` for every nontrivial zero. -/
def RealSpectrumRealization (Λ : Set ℝ) : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → ∃ l ∈ Λ, (l : ℂ) = (ρ - 1/2) / Complex.I

theorem re_eq_half_of_real_eigenvalue {ρ : ℂ} {l : ℝ} (h : (l : ℂ) = (ρ - 1/2) / Complex.I) :
    ρ.re = 1/2 := by
  have him := congrArg Complex.im h
  rw [Complex.ofReal_im, Complex.div_I] at him
  simp at him
  linarith

/-- The Hilbert–Pólya step with no operator at all: any real spectrum realizing the zeros is RH. -/
theorem rh_of_realSpectrumRealization {Λ : Set ℝ} (h : RealSpectrumRealization Λ) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_strip]
  intro ρ hρ
  obtain ⟨l, _, hl⟩ := h ρ hρ
  exact re_eq_half_of_real_eigenvalue hl

/-- A multiplicity dictionary: each zero's eigenvalue carries multiplicity `zeta_order ρ`.
If every spectral multiplicity is 1, every zero is simple.  (The dictionary is the whole
content; nothing about ζ is used.) -/
theorem allZerosSimple_of_multiplicity_dictionary {Λ : Set ℝ} (mult : ℝ → ℕ)
    (hdict : ∀ ρ : ℂ, is_nontrivial_zero ρ → ∃ l ∈ Λ, mult l = zeta_order ρ)
    (hsimple : ∀ l ∈ Λ, mult l = 1) : AllZerosSimple := by
  intro ρ hρ
  obtain ⟨l, hl, hm⟩ := hdict ρ hρ
  rw [← hm]; exact hsimple l hl

/-! ### §4 What a gap mechanism must deliver -/

/-- A gap mechanism at `Δ`: some predicate on points that every band zero satisfies and that
no point satisfies.  Stated as a `Prop` (an `∃` over the predicate) so that the challenge
generator can mirror it verbatim; having one is the same as having the band. -/
def GapMechanism (Δ : ℝ) : Prop :=
  ∃ P : ℂ → Prop,
    (∀ ρ : ℂ, is_nontrivial_zero ρ → 1/2 < ρ.re → ρ.re < 1/2 + Δ → P ρ) ∧ ∀ s : ℂ, ¬ P s

theorem gap_of_mechanism {Δ : ℝ} (M : GapMechanism Δ) : SpectralGapHyp Δ := by
  obtain ⟨P, hband, hrefuted⟩ := M
  apply gap_of_right_side
  intro ρ hρ h1
  by_contra hlt
  exact hrefuted ρ (hband ρ hρ h1 (not_le.1 hlt))

/-- Conversely a band gives a mechanism (`P s := False` on the band), so the two notions
coincide: a mechanism is not a weaker thing to look for than the band itself. -/
theorem mechanism_of_gap {Δ : ℝ} (h : SpectralGapHyp Δ) : GapMechanism Δ := by
  rw [gap_iff_zeroFreeBand] at h
  refine ⟨fun _ => False, ?_, fun _ hs => hs⟩
  intro ρ hρ h1 h2
  rcases h ρ hρ with h3 | h3 <;> linarith

/-- The two notions are the same proposition. -/
theorem gapMechanism_iff (Δ : ℝ) : GapMechanism Δ ↔ SpectralGapHyp Δ :=
  ⟨gap_of_mechanism, mechanism_of_gap⟩

/-- The probe identities of output86 are definitional: `N(ρ) + S(ρ) = 0` for every `ρ`,
and `N(1 − ρ) = S(ρ)`.  They constrain nothing. -/
noncomputable def NorthProbe (ρ : ℂ) : ℝ := ρ.re - 1/2

noncomputable def SouthProbe (ρ : ℂ) : ℝ := -(ρ.re - 1/2)

theorem probe_balance (ρ : ℂ) : NorthProbe ρ + SouthProbe ρ = 0 := by
  simp [NorthProbe, SouthProbe]

theorem probe_reflect (ρ : ℂ) : NorthProbe (1 - ρ) = SouthProbe ρ := by
  simp [NorthProbe, SouthProbe]; ring

/-- "Both probes read 0" is `Re ρ = 1/2`, nothing more. -/
theorem probes_zero_iff (ρ : ℂ) : (NorthProbe ρ = 0 ∧ SouthProbe ρ = 0) ↔ ρ.re = 1/2 := by
  unfold NorthProbe SouthProbe
  constructor
  · rintro ⟨h, _⟩; linarith
  · intro h; constructor <;> linarith

end MNF.RH

#print axioms MNF.RH.gap_iff_zeroFreeBand
#print axioms MNF.RH.gap_of_right_side
#print axioms MNF.RH.rh_of_band_of_zeroFree
#print axioms MNF.RH.multipleZeroKillsGap_iff
#print axioms MNF.RH.fischerForward_iff
#print axioms MNF.RH.rh_of_realSpectrumRealization
#print axioms MNF.RH.allZerosSimple_of_multiplicity_dictionary
#print axioms MNF.RH.gap_of_mechanism
#print axioms MNF.RH.mechanism_of_gap
#print axioms MNF.RH.gapMechanism_iff
#print axioms MNF.RH.probes_zero_iff
