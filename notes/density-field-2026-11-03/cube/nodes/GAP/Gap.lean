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

/-! ## Copied verbatim from Node ZONES (what this node needs) -/

lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re := by simp [mirror]

lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im := by simp [mirror]

lemma is_nontrivial_zero_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    is_nontrivial_zero (mirror ρ) :=
  Zeta23.zetaZeroConfig.reflect_mem ρ hz

lemma mirror_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) :
    mirror ρ ∈ zerosIn T₁ T₂ :=
  reflect_mem_zerosIn h

lemma zeta_order_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    zeta_order (mirror ρ) = zeta_order ρ :=
  zeta_order_reflectZ hz

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

lemma one_le_zeta_order {ρ : ℂ} (hz : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ :=
  zeta_order_ge_one hz

lemma mem_bandZeros_mirror {Δ : ℝ} {ρ : ℂ} (h : ρ ∈ bandZeros Δ) : mirror ρ ∈ bandZeros Δ := by
  obtain ⟨hz, hlt⟩ := h
  refine ⟨is_nontrivial_zero_mirror hz, ?_⟩
  rw [mirror_re, show (1 - ρ.re - 1 / 2 : ℝ) = -(ρ.re - 1 / 2) by ring, abs_neg]
  exact hlt

/-! ## Node GAP: the band and the gap -/

/-! ### 1. The gap hypothesis says exactly that no nontrivial zero lies in the open band -/

/-- `SpectralGapHyp Δ` (every shifted real part is `0` or has modulus `≥ Δ`) is the statement
that no nontrivial zero lies in the punctured band `0 < |Re ρ − 1/2| < Δ`.  Both directions
are read off the definition of the gap property. -/
theorem spectralGapHyp_iff_not_inBand (Δ : ℝ) :
    SpectralGapHyp Δ ↔ ∀ ρ, is_nontrivial_zero ρ → ¬ InBand Δ ρ := by
  constructor
  · intro hgap ρ hz hband
    have hx : ρ.re - 1 / 2 ∈ ShiftedZeroSpectrum := ⟨ρ, hz, rfl⟩
    rcases hgap _ hx with h0 | hge
    · exact (abs_pos.1 hband.1) h0
    · exact absurd hband.2 (not_lt.2 hge)
  · intro h x hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    by_cases h0 : ρ.re - 1 / 2 = 0
    · exact Or.inl h0
    · right
      by_contra hlt
      exact h ρ hρ ⟨abs_pos.2 h0, not_le.1 hlt⟩

/-! ### 2. The gap hypothesis as injectivity of the ordinate on the band -/

/-- The gap at `Δ` holds iff no two distinct zeros within distance `< Δ` of the line share an
ordinate.  (→: under the gap every band zero is on the line, and two on-line zeros with the same
ordinate coincide.  ←: an off-line band zero and its mirror are distinct band zeros with the same
ordinate.) -/
theorem spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros (Δ : ℝ) :
    SpectralGapHyp Δ ↔ OrdinatesInjectiveOn (bandZeros Δ) := by
  rw [spectralGapHyp_iff_not_inBand]
  constructor
  · intro h ρ hρ ρ' hρ' him
    have hre : ∀ σ ∈ bandZeros Δ, σ.re = 1 / 2 := by
      intro σ hσ
      obtain ⟨hz, hlt⟩ := hσ
      by_contra hne
      exact h σ hz ⟨abs_pos.2 (sub_ne_zero.2 hne), hlt⟩
    exact Complex.ext (by rw [hre ρ hρ, hre ρ' hρ']) him
  · intro h ρ hz hband
    have hρ : ρ ∈ bandZeros Δ := ⟨hz, hband.2⟩
    have hm : mirror ρ ∈ bandZeros Δ := mem_bandZeros_mirror hρ
    have heq : mirror ρ = ρ := h _ hm _ hρ (mirror_im ρ)
    have hon := (mirror_eq_self_iff ρ).1 heq
    unfold OnLine at hon
    have h0 : ρ.re - 1 / 2 = 0 := by linarith
    exact (abs_pos.1 hband.1) h0

/-! ### 3. Under the gap the band's coincident mass vanishes -/

/-- Under the gap, every inner set of `bandCoincidentMass` is empty (a band zero has no distinct
band partner with the same ordinate), so the whole double sum is `0`. -/
theorem bandCoincidentMass_eq_zero_of_spectralGapHyp {Δ : ℝ} (h : SpectralGapHyp Δ) (T : ℝ) :
    bandCoincidentMass Δ T = 0 := by
  have hinj := (spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros Δ).1 h
  unfold bandCoincidentMass
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro ρ hρ
  apply finsum_mem_eq_zero_of_forall_eq_zero
  rintro ρ' ⟨⟨_, hb'⟩, hne, him⟩
  exact absurd (hinj ρ' hb' ρ hρ.2 him) hne

/-! ### 4. A vanishing band coincident mass excludes band zeros of positive ordinate -/

/-- If the band's coincident mass vanishes in every window, no nontrivial zero of positive
ordinate lies in the open band: for such a `ρ` the ordered pair `(ρ, mirror ρ)` contributes
`(zeta_order ρ)² ≥ 1` to `bandCoincidentMass Δ (Im ρ)`, a sum of nonnegative terms. -/
theorem not_inBand_of_bandCoincidentMass_eq_zero {Δ : ℝ} (h : ∀ T, bandCoincidentMass Δ T = 0)
    {ρ : ℂ} (hz : is_nontrivial_zero ρ) (hpos : 0 < ρ.im) : ¬ InBand Δ ρ := by
  intro hband
  have hSfin : (zerosIn 0 ρ.im ∩ bandZeros Δ).Finite :=
    (zerosIn_finite 0 ρ.im).inter_of_left _
  have hρS : ρ ∈ zerosIn 0 ρ.im ∩ bandZeros Δ := ⟨⟨hz, hpos, le_refl _⟩, hz, hband.2⟩
  have hmS : mirror ρ ∈ zerosIn 0 ρ.im ∩ bandZeros Δ :=
    ⟨mirror_mem_zerosIn hρS.1, mem_bandZeros_mirror hρS.2⟩
  have hne : mirror ρ ≠ ρ := by
    intro heq
    have hon := (mirror_eq_self_iff ρ).1 heq
    unfold OnLine at hon
    have h0 : ρ.re - 1 / 2 = 0 := by linarith
    exact (abs_pos.1 hband.1) h0
  have hnn : ∀ σ : ℂ,
      0 ≤ ∑ᶠ σ' ∈ zerosIn 0 ρ.im ∩ bandZeros Δ ∩ {σ' | σ' ≠ σ ∧ σ'.im = σ.im},
        (zeta_order σ : ℝ) * (zeta_order σ' : ℝ) := by
    intro σ
    rw [finsum_mem_eq_finite_toFinset_sum _ (hSfin.inter_of_left {σ' | σ' ≠ σ ∧ σ'.im = σ.im})]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hfin' : (zerosIn 0 ρ.im ∩ bandZeros Δ ∩ {σ' | σ' ≠ ρ ∧ σ'.im = ρ.im}).Finite :=
    hSfin.inter_of_left _
  have hterm : (zeta_order ρ : ℝ) * (zeta_order (mirror ρ) : ℝ) ≤
      ∑ᶠ σ' ∈ zerosIn 0 ρ.im ∩ bandZeros Δ ∩ {σ' | σ' ≠ ρ ∧ σ'.im = ρ.im},
        (zeta_order ρ : ℝ) * (zeta_order σ' : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin']
    exact Finset.single_le_sum (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (hfin'.mem_toFinset.2 ⟨hmS, hne, mirror_im ρ⟩)
  have hsq : (1 : ℝ) ≤ (zeta_order ρ : ℝ) * (zeta_order (mirror ρ) : ℝ) := by
    rw [zeta_order_mirror hz]
    have h1 : (1 : ℝ) ≤ (zeta_order ρ : ℝ) := by exact_mod_cast one_le_zeta_order hz
    nlinarith
  have hpos0 : (0 : ℝ) < (zeta_order ρ : ℝ) * (zeta_order (mirror ρ) : ℝ) := by linarith
  have hpos' : 0 < bandCoincidentMass Δ ρ.im := by
    unfold bandCoincidentMass
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    exact lt_of_lt_of_le (lt_of_lt_of_le hpos0 hterm)
      (Finset.single_le_sum (fun σ _ => hnn σ) (hSfin.mem_toFinset.2 hρS))
  linarith [h ρ.im]

/-! ### 5. Conjugation, and the equivalence conditional on the absence of real zeros -/

/-- Conjugation symmetry of the nontrivial zeros (Mathlib's `riemannZeta_conj`). -/
lemma is_nontrivial_zero_conj {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    is_nontrivial_zero ((starRingEnd ℂ) ρ) := by
  obtain ⟨h0, h1, h2⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h0, map_zero]
  · rw [Complex.conj_re]; exact h1
  · rw [Complex.conj_re]; exact h2

/-- The equivalence "gap ↔ the band's coincident mass vanishes in every window", under the
explicit hypothesis that no nontrivial zero is real (a real zero has ordinate `0` and lies in no
window `(0, T]`, so the pair measure cannot see it).  Negative ordinates are handled by
conjugation, positive ones by `not_inBand_of_bandCoincidentMass_eq_zero`. -/
theorem spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero
    (hreal : ∀ ρ, is_nontrivial_zero ρ → ρ.im ≠ 0) (Δ : ℝ) :
    SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0 := by
  constructor
  · intro h T
    exact bandCoincidentMass_eq_zero_of_spectralGapHyp h T
  · intro h
    rw [spectralGapHyp_iff_not_inBand]
    intro ρ hz hband
    rcases lt_or_gt_of_ne (hreal ρ hz) with hneg | hpos
    · have hz' := is_nontrivial_zero_conj hz
      have hpos' : 0 < ((starRingEnd ℂ) ρ).im := by rw [Complex.conj_im]; linarith
      apply not_inBand_of_bandCoincidentMass_eq_zero h hz' hpos'
      unfold InBand at hband ⊢
      rw [Complex.conj_re]
      exact hband
    · exact not_inBand_of_bandCoincidentMass_eq_zero h hz hpos hband

/-! ### 6. Nonnegativity and comparison with the off-diagonal coincident mass -/

theorem bandCoincidentMass_nonneg (Δ T : ℝ) : 0 ≤ bandCoincidentMass Δ T :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => finsum_nonneg fun _ => finsum_nonneg fun _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The band's coincident mass is part of the off-diagonal coincident mass: the outer and inner
index sets shrink and every term is nonnegative. -/
theorem bandCoincidentMass_le_offDiagonalCoincidentMass (Δ T : ℝ) :
    bandCoincidentMass Δ T ≤ offDiagonalCoincidentMass T := by
  have hfin : (zerosIn 0 T).Finite := zerosIn_finite 0 T
  have hSfin : (zerosIn 0 T ∩ bandZeros Δ).Finite := hfin.inter_of_left _
  have hinner : ∀ σ : ℂ,
      (∑ᶠ σ' ∈ zerosIn 0 T ∩ bandZeros Δ ∩ {σ' | σ' ≠ σ ∧ σ'.im = σ.im},
        (zeta_order σ : ℝ) * (zeta_order σ' : ℝ)) ≤
      ∑ᶠ σ' ∈ zerosIn 0 T ∩ {σ' | σ' ≠ σ ∧ σ'.im = σ.im},
        (zeta_order σ : ℝ) * (zeta_order σ' : ℝ) := by
    intro σ
    rw [finsum_mem_eq_finite_toFinset_sum _ (hSfin.inter_of_left {σ' | σ' ≠ σ ∧ σ'.im = σ.im}),
      finsum_mem_eq_finite_toFinset_sum _ (hfin.inter_of_left {σ' | σ' ≠ σ ∧ σ'.im = σ.im})]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro σ' hσ'
      rw [Set.Finite.mem_toFinset] at hσ' ⊢
      exact ⟨hσ'.1.1, hσ'.2⟩
    · intro _ _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold bandCoincidentMass offDiagonalCoincidentMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine le_trans (Finset.sum_le_sum fun σ _ => hinner σ)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro σ hσ
    rw [Set.Finite.mem_toFinset] at hσ ⊢
    exact hσ.1
  · intro σ _ _
    exact finsum_nonneg fun _ => finsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### Axiom audit -/

#print axioms MNF.RH.spectralGapHyp_iff_not_inBand
#print axioms MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros
#print axioms MNF.RH.bandCoincidentMass_eq_zero_of_spectralGapHyp
#print axioms MNF.RH.not_inBand_of_bandCoincidentMass_eq_zero
#print axioms MNF.RH.is_nontrivial_zero_conj
#print axioms MNF.RH.spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero
#print axioms MNF.RH.bandCoincidentMass_nonneg
#print axioms MNF.RH.bandCoincidentMass_le_offDiagonalCoincidentMass

end MNF.RH
