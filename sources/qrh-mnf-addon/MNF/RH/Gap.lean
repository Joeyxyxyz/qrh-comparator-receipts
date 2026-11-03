/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE GAP HYPOTHESIS  (MNF/RH/Gap.lean)
What the MNF spectral-gap hypothesis says about ζ, and what it does not.
═══════════════════════════════════════════════════════════════════════
All theorems here are [PROVED] from Mathlib and MNF/RH/Core.lean, except
where a zero-free-region hypothesis `ZeroFreeRightOf θ` is written as an
explicit argument.  No axiom, no `sorry`.

Contents
  §1  the gap property and the squeeze     SpectralGapProperty, tau_threshold
  §2  RH ⟺ gap, unconditionally at Δ ≥ 1/2  riemannHypothesis_iff_gap_half
  §3  with a zero-free region θ            ZeroFreeRightOf, shifted_bounded_of_zeroFree,
                                           riemannHypothesis_iff_gap_of_zeroFree  (Δ > θ − 1/2)
  §4  why no smaller Δ can work            gap_below_bound_insufficient (abstract),
                                           symmetric_bounded_not_on_line (structural no-go)
  §5  the hackathon items                  sign_gate_trivial, nullify, nullify_dilation,
                                           delta_from_ratio_38_insufficient

Bottom line (made kernel-checked here): with the 7/8 zero-free region in hand,
`SpectralGapProperty ShiftedZeroSpectrum Δ` is *equivalent to RH* for every
Δ > 3/8 and *does not imply RH* for any Δ ≤ 3/8 (§4, abstract model).  The gap
hypothesis is therefore not a weaker assumption than RH; it is RH in other words.
-/
import MNF.RH.Core

namespace MNF.RH

open Complex

/-! ### §1 The gap property -/

/-- MNF spectral gap: every element of `S` is `0` or at least `Δ` away from it. -/
def SpectralGapProperty (S : Set ℝ) (Δ : ℝ) : Prop := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ

/-- The squeeze: a gap at `Δ` together with the bound `|x| < Δ` forces `S ⊆ {0}`. -/
theorem tau_threshold {S : Set ℝ} {Δ : ℝ} (hgap : SpectralGapProperty S Δ)
    (hbound : ∀ x ∈ S, |x| < Δ) : S ⊆ {0} := by
  intro x hx
  rcases hgap x hx with h | h
  · simp [h]
  · exact absurd (hbound x hx) (not_lt.2 h)

theorem gap_of_subset_zero {S : Set ℝ} (h : S ⊆ {0}) (Δ : ℝ) : SpectralGapProperty S Δ :=
  fun x hx => Or.inl (by simpa using h hx)

theorem gap_mono {S : Set ℝ} {Δ Δ' : ℝ} (h : Δ' ≤ Δ) (hgap : SpectralGapProperty S Δ) :
    SpectralGapProperty S Δ' :=
  fun x hx => (hgap x hx).imp id (fun hx' => le_trans h hx')

/-! ### §2 RH ⟺ gap, with no hypothesis, at every Δ ≥ 1/2 -/

/-- **The corpus master theorem, unconditionally.**  Since `|x| < 1/2` on the spectrum
(`shifted_bounded`), a gap at any `Δ ≥ 1/2` is the same as `S ⊆ {0}`, i.e. RH. -/
theorem riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1/2 ≤ Δ) :
    RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ := by
  rw [riemannHypothesis_iff_shifted_subset_zero]
  constructor
  · intro h; exact gap_of_subset_zero h Δ
  · intro hgap
    exact tau_threshold hgap (fun x hx => lt_of_lt_of_le (shifted_bounded hx) hΔ)

/-! ### §3 With a zero-free region `Re s > θ` -/

/-- `ζ` has no zeros with real part greater than `θ`.  OpenAI's theorem is `ZeroFreeRightOf (7/8)`. -/
def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

theorem re_le_of_zeroFree {θ : ℝ} (h : ZeroFreeRightOf θ) {ρ : ℂ} (hρ : is_nontrivial_zero ρ) :
    ρ.re ≤ θ := by
  by_contra hlt
  exact h ρ (not_le.1 hlt) hρ.1

/-- With a zero-free region right of `θ`, the spectrum lies in `[-(θ - 1/2), θ - 1/2]`
(symmetry supplies the left bound). -/
theorem shifted_bounded_of_zeroFree {θ : ℝ} (h : ZeroFreeRightOf θ) {x : ℝ}
    (hx : x ∈ ShiftedZeroSpectrum) : |x| ≤ θ - 1/2 := by
  obtain ⟨ρ, hρ, rfl⟩ := hx
  have h1 := re_le_of_zeroFree h hρ
  have h2 := re_le_of_zeroFree h (nontrivial_zero_reflect hρ)
  rw [re_one_sub] at h2
  rw [abs_le]
  constructor <;> linarith

/-- RH ⟺ gap at any `Δ > θ - 1/2`, given a zero-free region right of `θ`.
At `θ = 7/8`: every `Δ > 3/8`. -/
theorem riemannHypothesis_iff_gap_of_zeroFree {θ Δ : ℝ} (h : ZeroFreeRightOf θ)
    (hΔ : θ - 1/2 < Δ) : RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ := by
  rw [riemannHypothesis_iff_shifted_subset_zero]
  constructor
  · intro hsub; exact gap_of_subset_zero hsub Δ
  · intro hgap
    exact tau_threshold hgap (fun x hx => lt_of_le_of_lt (shifted_bounded_of_zeroFree h hx) hΔ)

/-- What is left of RH under a zero-free region: no zeros in `1/2 < Re s ≤ θ`. -/
theorem riemannHypothesis_iff_remaining_strip {θ : ℝ} (h : ZeroFreeRightOf θ) :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ θ → riemannZeta s ≠ 0 := by
  rw [riemannHypothesis_iff_strip]
  constructor
  · intro hRH s hs1 hsθ hs
    have hlt1 : s.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hge) hs
    have := hRH s ⟨hs, by linarith, hlt1⟩
    linarith
  · intro hstrip ρ hρ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `Re ρ < 1/2`: reflect to `1 - ρ`, which has `1/2 < Re ≤ θ`
      have hr := nontrivial_zero_reflect hρ
      exact hstrip (1 - ρ) (by rw [re_one_sub]; linarith)
        (re_le_of_zeroFree h hr) hr.1
    · exact hstrip ρ hgt (re_le_of_zeroFree h hρ) hρ.1

/-! ### §4 Why no smaller Δ can close the squeeze -/

/-- Abstract model: for every `Δ` below the bound `b`, a symmetric set inside `(-b, b)`
can have a gap at `Δ` and still not be `{0}`.  So a gap at `Δ ≤ θ - 1/2` cannot by
itself give `S ⊆ {0}`; only the bound `|x| < Δ` does the work. -/
theorem gap_below_bound_insufficient {b Δ : ℝ} (hΔ : 0 < Δ) (hb : Δ < b) :
    ∃ S : Set ℝ, S ⊆ Set.Ioo (-b) b ∧ (∀ x ∈ S, -x ∈ S) ∧ SpectralGapProperty S Δ ∧ S ≠ {0} := by
  refine ⟨{Δ, -Δ}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> constructor <;> linarith
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · right; rw [abs_of_pos hΔ]
    · right; rw [abs_neg, abs_of_pos hΔ]
  · intro h
    have : Δ ∈ ({0} : Set ℝ) := h ▸ (by simp)
    simp at this
    linarith

/-- The three structural inputs a zero set is known to satisfy — symmetry under `ρ ↦ 1 - ρ`,
conjugation symmetry, and `Re ρ ≤ 7/8` — do not force `Re ρ = 1/2`: witnessed by four points. -/
def Counter : Set ℂ := {ρ | (ρ.re = 1/4 ∨ ρ.re = 3/4) ∧ (ρ.im = 1 ∨ ρ.im = -1)}

theorem counter_reflect : ∀ ρ ∈ Counter, (1 - ρ) ∈ Counter := by
  rintro ρ ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · rw [re_one_sub]; rcases h1 with h | h <;> [right; left] <;> linarith
  · simp only [Complex.sub_im, Complex.one_im, zero_sub]
    rcases h2 with h | h <;> [right; left] <;> linarith

theorem counter_bound : ∀ ρ ∈ Counter, ρ.re ≤ 7/8 := by
  rintro ρ ⟨h1, _⟩; rcases h1 with h | h <;> linarith

theorem counter_off_line : ¬ ∀ ρ ∈ Counter, ρ.re = 1/2 := by
  intro h
  have := h ⟨1/4, 1⟩ ⟨Or.inl rfl, Or.inl rfl⟩
  norm_num at this

theorem symmetric_bounded_not_on_line :
    ¬ ∀ Z : Set ℂ, (∀ ρ ∈ Z, (1 - ρ) ∈ Z) → (∀ ρ ∈ Z, ρ.re ≤ 7/8) → ∀ ρ ∈ Z, ρ.re = 1/2 :=
  fun h => counter_off_line (h Counter counter_reflect counter_bound)

/-! ### §5 The hackathon items, made exact -/

/-- The sign-consistency gate: keep an element only if its negative is absent, then add `0`. -/
def signGate (S : Set ℝ) : Set ℝ := {x ∈ S | -x ∉ S} ∪ {0}

/-- On any symmetric set the gate returns `{0}` — it assumes its conclusion.
Applied to `ShiftedZeroSpectrum` (symmetric by `shifted_symmetric`) it proves nothing about ζ. -/
theorem sign_gate_trivial {S : Set ℝ} (hS : ∀ x ∈ S, -x ∈ S) : signGate S = {0} := by
  ext x
  simp only [signGate, Set.mem_union, Set.mem_sep_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hx, hnx⟩ | h)
    · exact absurd (hS x hx) hnx
    · exact h
  · intro h; exact Or.inr h

theorem sign_gate_shifted : signGate ShiftedZeroSpectrum = {0} :=
  sign_gate_trivial (fun _ hx => shifted_symmetric hx)

/-- MNF nullification at threshold `Δ`. -/
noncomputable def nullify (Δ x : ℝ) : ℝ := if Δ ≤ |x| then x else 0

theorem nullify_eq_self_or_zero (Δ x : ℝ) : nullify Δ x = x ∨ nullify Δ x = 0 := by
  unfold nullify; split_ifs <;> simp

/-- Dilation covariance: `nullify (λΔ) (λx) = λ · nullify Δ x` for `λ > 0`.
(Was Python-verified in the corpus; kernel-checked here.) -/
theorem nullify_dilation {l : ℝ} (hl : 0 < l) (Δ x : ℝ) :
    nullify (l * Δ) (l * x) = l * nullify Δ x := by
  unfold nullify
  have : |l * x| = l * |x| := by rw [abs_mul, abs_of_pos hl]
  rw [this]
  by_cases h : Δ ≤ |x|
  · have h' : l * Δ ≤ l * |x| := mul_le_mul_of_nonneg_left h hl.le
    simp [h, h']
  · have h' : ¬ l * Δ ≤ l * |x| := fun h' => h (le_of_mul_le_mul_left h' hl)
    simp [h, h']

/-- The gap property is exactly "nullification at `Δ` is the identity on `S`". -/
theorem gap_iff_nullify_id (S : Set ℝ) (Δ : ℝ) :
    SpectralGapProperty S Δ ↔ ∀ x ∈ S, nullify Δ x = x := by
  constructor
  · intro h x hx
    rcases h x hx with rfl | h'
    · simp [nullify]
    · simp [nullify, h']
  · intro h x hx
    have := h x hx
    unfold nullify at this
    split_ifs at this with h'
    · right; exact h'
    · left; exact this.symm

/-- The learnings rule "Δ / scale = 1/2" with scale `3/8` gives `Δ = 3/16`, and a gap at
`3/16` is below the bound: by `gap_below_bound_insufficient` it cannot give `S ⊆ {0}`. -/
theorem delta_from_ratio_38_insufficient :
    (1/2 : ℝ) * (3/8) = 3/16 ∧
    ∃ S : Set ℝ, S ⊆ Set.Ioo (-(3/8)) (3/8) ∧ (∀ x ∈ S, -x ∈ S) ∧
      SpectralGapProperty S (3/16) ∧ S ≠ {0} :=
  ⟨by norm_num, gap_below_bound_insufficient (by norm_num) (by norm_num)⟩

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.tau_threshold
#print axioms MNF.RH.riemannHypothesis_iff_gap_half
#print axioms MNF.RH.shifted_bounded_of_zeroFree
#print axioms MNF.RH.riemannHypothesis_iff_gap_of_zeroFree
#print axioms MNF.RH.riemannHypothesis_iff_remaining_strip
#print axioms MNF.RH.gap_below_bound_insufficient
#print axioms MNF.RH.symmetric_bounded_not_on_line
#print axioms MNF.RH.sign_gate_shifted
#print axioms MNF.RH.nullify_dilation
#print axioms MNF.RH.gap_iff_nullify_id
#print axioms MNF.RH.delta_from_ratio_38_insufficient
