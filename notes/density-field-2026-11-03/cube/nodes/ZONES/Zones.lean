import MNF.RH.ReservoirMass

open Set

namespace MNF.RH

/-! ## DEFINITIONS (frozen): the zones of the strip and the pair measure ("the cube") -/

/-- The mirror ρ ↦ 1 − ρ̄ of the functional-equation symmetry: the same imaginary part, the real
part reflected in 1/2.  (The same body as zeta23's `reflect`.) -/
def mirror (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- The critical line, Re ρ = 1/2. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- The open band of half-width Δ around the line, the line itself removed:
0 < |Re ρ − 1/2| < Δ. -/
def InBand (Δ : ℝ) (ρ : ℂ) : Prop := 0 < |ρ.re - 1 / 2| ∧ |ρ.re - 1 / 2| < Δ

/-- The reservoir at threshold Δ: |Re ρ − 1/2| ≥ Δ. -/
def InReservoir (Δ : ℝ) (ρ : ℂ) : Prop := Δ ≤ |ρ.re - 1 / 2|

/-- The nontrivial zeros within distance < Δ of the line (the line included). -/
def bandZeros (Δ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ |ρ.re - 1 / 2| < Δ}

/-- A nontrivial zero is degenerate if it is a multiple zero or shares its ordinate with another
nontrivial zero. -/
def Degenerate (ρ : ℂ) : Prop :=
  2 ≤ zeta_order ρ ∨ ∃ ρ' : ℂ, is_nontrivial_zero ρ' ∧ ρ' ≠ ρ ∧ ρ'.im = ρ.im

/-- No two distinct points of `S` share an imaginary part. -/
def OrdinatesInjectiveOn (S : Set ℂ) : Prop := ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ.im = ρ'.im → ρ = ρ'

/-- The pair measure of the window (0, T] applied to a test function: the sum over ordered pairs
of nontrivial zeros `(ρ, ρ')` with `0 < Im ≤ T`, weighted by both multiplicities, of
`f (Re ρ − 1/2) (Re ρ' − 1/2) (Im ρ − Im ρ')`. -/
noncomputable def pairSum (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, ∑ᶠ ρ' ∈ zerosIn 0 T,
    (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im)

/-- The coincident mass: the pair measure of the pairs with equal ordinates (the atom at s = 0). -/
noncomputable def coincidentMass (T : ℝ) : ℝ := pairSum T (fun _ _ s => if s = 0 then 1 else 0)

/-- The diagonal mass Σ m(ρ)². -/
noncomputable def diagonalMass (T : ℝ) : ℝ := ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) ^ 2

/-- The off-diagonal coincident mass: ordered pairs of distinct zeros with equal ordinates. -/
noncomputable def offDiagonalCoincidentMass (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, ∑ᶠ ρ' ∈ zerosIn 0 T ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im},
    (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ)

/-- The band's coincident mass: ordered pairs of distinct zeros, both within distance < Δ of the
line, with equal ordinates. -/
noncomputable def bandCoincidentMass (Δ T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T ∩ bandZeros Δ,
    ∑ᶠ ρ' ∈ zerosIn 0 T ∩ bandZeros Δ ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im},
      (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ)

/-! ## END of the DEFINITIONS block -/

/-! ## Node ZONES: the mirror, the zones, degeneracy -/

/-! ### 1. The mirror ρ ↦ 1 − ρ̄ -/

lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re := by simp [mirror]

lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im := by simp [mirror]

lemma mirror_mirror (ρ : ℂ) : mirror (mirror ρ) = ρ := by simp [mirror]

lemma mirror_injective : Function.Injective mirror :=
  Function.LeftInverse.injective mirror_mirror

/-! ### 2. The mirror is zeta23's reflection (definitionally) -/

lemma aux_mirror_eq_reflect (ρ : ℂ) : mirror ρ = Zeta23.reflect ρ := rfl

/-! ### 3. The mirror preserves zeros, windows and multiplicities -/

lemma is_nontrivial_zero_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    is_nontrivial_zero (mirror ρ) :=
  Zeta23.zetaZeroConfig.reflect_mem ρ hz

lemma mirror_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) :
    mirror ρ ∈ zerosIn T₁ T₂ :=
  reflect_mem_zerosIn h

lemma zeta_order_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    zeta_order (mirror ρ) = zeta_order ρ :=
  zeta_order_reflectZ hz

/-! ### 4. Fixed points of the mirror are the points of the line -/

lemma mirror_eq_self_iff (ρ : ℂ) : mirror ρ = ρ ↔ OnLine ρ := by
  constructor
  · intro h
    have h' := congrArg Complex.re h
    rw [mirror_re] at h'
    unfold OnLine
    linarith
  · intro h
    unfold OnLine at h
    apply Complex.ext
    · rw [mirror_re]; linarith
    · rw [mirror_im]

/-! ### 5. Every nontrivial zero has multiplicity at least one -/

lemma one_le_zeta_order {ρ : ℂ} (hz : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ :=
  zeta_order_ge_one hz

/-! ### 6–9. Degeneracy -/

/-- The projection-degeneracy lemma: an off-line zero shares its ordinate with its mirror,
a distinct nontrivial zero. -/
theorem degenerate_of_not_onLine {ρ : ℂ} (hz : is_nontrivial_zero ρ) (h : ¬ OnLine ρ) :
    Degenerate ρ := by
  right
  refine ⟨mirror ρ, is_nontrivial_zero_mirror hz, ?_, mirror_im ρ⟩
  intro heq
  exact h ((mirror_eq_self_iff ρ).1 heq)

lemma onLine_and_simple_of_not_degenerate {ρ : ℂ} (hz : is_nontrivial_zero ρ)
    (h : ¬ Degenerate ρ) : OnLine ρ ∧ zeta_order ρ = 1 := by
  constructor
  · by_contra hon
    exact h (degenerate_of_not_onLine hz hon)
  · have h1 := one_le_zeta_order hz
    by_contra h2
    exact h (Or.inl (by omega))

lemma not_degenerate_of_onLine_simple (hall : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) {ρ : ℂ}
    (hz : is_nontrivial_zero ρ) (h1 : zeta_order ρ = 1) : ¬ Degenerate ρ := by
  rintro (h2 | ⟨ρ', hz', hne, him⟩)
  · omega
  · apply hne
    have hρ := hall ρ hz
    have hρ' := hall ρ' hz'
    unfold OnLine at hρ hρ'
    exact Complex.ext (by rw [hρ, hρ']) him

/-- No nontrivial zero is degenerate iff every nontrivial zero is on the line and simple. -/
theorem noDegenerate_iff :
    (∀ ρ, is_nontrivial_zero ρ → ¬ Degenerate ρ) ↔
      (∀ ρ, is_nontrivial_zero ρ → OnLine ρ) ∧ AllZerosSimple := by
  constructor
  · intro h
    exact ⟨fun ρ hz => (onLine_and_simple_of_not_degenerate hz (h ρ hz)).1,
      fun ρ hz => (onLine_and_simple_of_not_degenerate hz (h ρ hz)).2⟩
  · rintro ⟨hall, hsimple⟩ ρ hz
    exact not_degenerate_of_onLine_simple hall hz (hsimple ρ hz)

/-! ### 10. Zone bookkeeping -/

set_option linter.unusedVariables false in
/-- The three zones cover the strip (the hypothesis `0 < Δ` is the plan's shape; the trichotomy
itself holds for every `Δ`). -/
lemma inBand_or_inReservoir_or_onLine {Δ : ℝ} (hΔ : 0 < Δ) (ρ : ℂ) :
    OnLine ρ ∨ InBand Δ ρ ∨ InReservoir Δ ρ := by
  by_cases hon : OnLine ρ
  · exact Or.inl hon
  · right
    have hpos : 0 < |ρ.re - 1 / 2| := by
      rw [abs_pos]
      intro h0
      apply hon
      unfold OnLine
      linarith
    by_cases hlt : |ρ.re - 1 / 2| < Δ
    · exact Or.inl ⟨hpos, hlt⟩
    · exact Or.inr (not_lt.1 hlt)

lemma inBand_mirror_iff (Δ : ℝ) (ρ : ℂ) : InBand Δ (mirror ρ) ↔ InBand Δ ρ := by
  unfold InBand
  rw [mirror_re, show (1 - ρ.re - 1 / 2 : ℝ) = -(ρ.re - 1 / 2) by ring, abs_neg]

lemma mem_bandZeros_mirror {Δ : ℝ} {ρ : ℂ} (h : ρ ∈ bandZeros Δ) : mirror ρ ∈ bandZeros Δ := by
  obtain ⟨hz, hlt⟩ := h
  refine ⟨is_nontrivial_zero_mirror hz, ?_⟩
  rw [mirror_re, show (1 - ρ.re - 1 / 2 : ℝ) = -(ρ.re - 1 / 2) by ring, abs_neg]
  exact hlt

/-! ### Axiom audit -/

#print axioms MNF.RH.mirror_re
#print axioms MNF.RH.mirror_im
#print axioms MNF.RH.mirror_mirror
#print axioms MNF.RH.mirror_injective
#print axioms MNF.RH.aux_mirror_eq_reflect
#print axioms MNF.RH.is_nontrivial_zero_mirror
#print axioms MNF.RH.mirror_mem_zerosIn
#print axioms MNF.RH.zeta_order_mirror
#print axioms MNF.RH.mirror_eq_self_iff
#print axioms MNF.RH.one_le_zeta_order
#print axioms MNF.RH.degenerate_of_not_onLine
#print axioms MNF.RH.onLine_and_simple_of_not_degenerate
#print axioms MNF.RH.not_degenerate_of_onLine_simple
#print axioms MNF.RH.noDegenerate_iff
#print axioms MNF.RH.inBand_or_inReservoir_or_onLine
#print axioms MNF.RH.inBand_mirror_iff
#print axioms MNF.RH.mem_bandZeros_mirror

end MNF.RH
