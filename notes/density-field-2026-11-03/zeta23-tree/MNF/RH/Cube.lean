/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE STRIP CUBE: ZONES, DEGENERACY, AND THE PAIR MEASURE
(MNF/RH/Cube.lean)
[BOOKKEEPING] + [PROVED | this tree]
Register: every declaration below is proved from Mathlib and the tree's sorry-free files with
standard axioms only, nothing admitted; every theorem is audited by name from `MNF_AuditDensity.lean` at the tree root.
═══════════════════════════════════════════════════════════════════════
Written 2026-11-04 on the zeta23 tree, on top of MNF/RH/ReservoirMass.lean.

What this file defines.  The "cube" is the strip seen through three coordinates of an ordered
pair of nontrivial zeros `(ρ, ρ')` with `0 < Im ≤ T`: the two shifted real parts `Re ρ − 1/2`,
`Re ρ' − 1/2`, and the ordinate difference `Im ρ − Im ρ'`.  The pair measure `pairSum T f` is the
sum over all such ordered pairs, weighted by both multiplicities, of a test function of these
three coordinates.  The strip itself is cut into three zones at a threshold `Δ`: the line
(`OnLine`), the punctured band `0 < |Re ρ − 1/2| < Δ` (`InBand Δ`), and the reservoir
`|Re ρ − 1/2| ≥ Δ` (`InReservoir Δ`).  The mirror `ρ ↦ 1 − ρ̄` (the functional-equation symmetry,
the same body as the tree's reflection) fixes the line pointwise and swaps the two sides of the
band.  A zero is `Degenerate` if it is multiple or shares its ordinate with another zero.
Vocabulary: MNF is the name of the framework this library is written for; "cube", "reservoir"
(its word for the zeros off the line, here at distance ≥ Δ) and "degenerate" are its words,
with exactly the meanings of the definitions above, and none of them is standard terminology.

What is proved.  Apart from the real-zero theorem of §3 and the two eventual bounds at the end
of §5 (which call the tree's `offLine_le_one_third`), everything is bookkeeping over finite sums
of zeros: each window `(0, T]` contains finitely many zeros, `zerosIn_finite`, and every other
identity or inequality below is a rearrangement, a termwise comparison, or a single-term lower
bound of such a finite sum.
  * the mirror preserves zeros, windows, multiplicities and the band, and its fixed points are
    exactly the points of the line; the three zones cover the strip;
  * **projection degeneracy**: an off-line zero is degenerate, its partner being its mirror
    (`degenerate_of_not_onLine`); hence "no nontrivial zero is degenerate" is exactly "every
    nontrivial zero is on the line and simple" (`noDegenerate_iff`);
  * **the gap as ordinate injectivity**: `SpectralGapHyp Δ` says that no zero lies in the
    punctured band (`spectralGapHyp_iff_not_inBand`), equivalently that no two distinct zeros
    within distance `< Δ` of the line share an ordinate
    (`spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`); under the gap the band's coincident
    mass vanishes in every window (`bandCoincidentMass_eq_zero_of_spectralGapHyp`), and
    conversely a band coincident mass vanishing in every window excludes band zeros of positive
    ordinate (`not_inBand_of_bandCoincidentMass_eq_zero`); with conjugation and the absence of
    real zeros the two sides meet: the gap at `Δ` holds iff the band's coincident mass vanishes
    in every window (`spectralGapHyp_iff_bandCoincidentMass`); the band's coincident mass is at
    most the off-diagonal coincident mass (`bandCoincidentMass_le_offDiagonalCoincidentMass`);
  * **no real zero**: `ζ(σ) ≠ 0` for real `0 < σ < 1` (`riemannZeta_ofReal_ne_zero_of_mem_Ioo`),
    so every nontrivial zero has a nonzero ordinate (`nontrivial_zero_im_ne_zero`), from the
    tree's Euler–Maclaurin representation of ζ with one term, `ζ(σ) = σ/(σ − 1) − 1/2 + σ·J(σ)`
    with `‖J(σ)‖ ≤ 1/(2σ)`: a zero would need `σ·J(σ) = 1/(1 − σ) − 1/2 > 1/2`;
  * **the marginals of the pair measure**: total mass `N(0,T)²`; a test function of one real
    part integrates to `N(0,T)` times the one-zero sum, so the reservoir indicator gives
    `N(0,T) · NOff δ 0 T` and the distance `|a|` gives `N(0,T) · reservoirMass T`, i.e. the double
    layer cake `N(0,T) · ∫₀^{1/2} NOff δ 0 T dδ` (`pairSum_fst_abs_eq_integral`); swap symmetry,
    positivity, monotonicity; the diagonal mass `Σ m(ρ)²` lies between `N(0,T)` and `N(0,T)²`;
  * **the atom at `s = 0`**: the coincident mass (pairs with equal ordinates) is the diagonal
    mass plus the off-diagonal coincident mass (`coincidentMass_eq`); every off-line zero
    contributes `m(ρ)²` to the latter through its mirror
    (`offLine_sq_le_offDiagonalCoincidentMass`); the off-diagonal coincident mass is at most
    `NOffLine · N + N0 · NOffLine ≤ 2 · NOffLine · N` (`offDiagonalCoincidentMass_le`,
    `offDiagonalCoincidentMass_le_two_mul`); it vanishes in every window if every nontrivial
    zero is on the line (`offDiagonalCoincidentMass_eq_zero_of_onLine`), and conversely its
    vanishing in every window forces every zero of POSITIVE ordinate onto the line
    (`onLine_of_offDiagonalCoincidentMass_eq_zero`; the two-sided form, which would need
    conjugation and `nontrivial_zero_im_ne_zero`, is not assembled here); and, with
    `N = N0 + NOffLine` (`Ncount_eq_N0_add_NOffLine`) and the tree's `offLine_le_one_third`
    (`NOffLine ≤ (1/3 + ε) N` eventually), it is eventually at most `(5/9 + ε) N(0,T)²`
    (`offDiagonalCoincidentMass_le_five_ninths`: the bound `NOffLine · (N + N0)` is at most
    `(1/3)·1 + (2/3)·(1/3) = 5/9` of `N²`); `2/3 + ε` is the cruder form from
    `2 · NOffLine · N` (`offDiagonalCoincidentMass_le_two_thirds`).

What this is and is not.  The equivalences RELOCATE the gap and RH; they do not prove them.
`SpectralGapHyp Δ ↔ OrdinatesInjectiveOn (bandZeros Δ)` restates a zero-free strip as a
statement about ordinates, and `noDegenerate_iff` restates "RH and all zeros simple" as the
absence of degenerate zeros: each side is as unknown as the other.  The one-directional results
about the coincident masses (vanishing in every window forces zeros of POSITIVE ordinate onto
the line, or out of the band) are stated for positive ordinates because the pair measure only
sees the windows `(0, T]`; negative ordinates follow by conjugation (`is_nontrivial_zero_conj`,
from Mathlib's `riemannZeta_conj`), and the unconditional two-sided form
`spectralGapHyp_iff_bandCoincidentMass` needs in addition that no nontrivial zero is real.
That classical fact was not on the tree, and we found no form of it in Mathlib at this pin
(which has `riemannZeta_ne_zero_of_one_le_re` only); it is proved here.  It is the one
zero-free statement in this file, and it concerns the real segment `(0, 1)` only, not the
interior of the strip: nothing in it bears on `SpectralGapHyp` or on RH, and it is not evidence
for either.  The bound `offDiag ≤ NOffLine · N` without the `N0 ·
NOffLine` term, and the eventual constant `1/3 + ε` it would give, are NOT proved and are not
bookkeeping: an on-line zero of multiplicity 2 sharing its ordinate with an off-line mirror pair
violates the bare inequality, and nothing on the tree excludes that configuration (RH does).
The cubic small-distance law (the pair-correlation density of the zeros vanishing quadratically
in the normalised ordinate difference, so that the pair measure of an interval of half-width `δ`
around `s = 0` is of order `δ³`) is the GUE prediction of Montgomery's pair-correlation
conjecture (1973); it is NOT a theorem, nothing here proves or assumes it, and the only thing
this file says about `s = 0` is the identity `coincidentMass_eq` for the atom there and the
bounds on its two parts in terms of the counts.  Nothing here uses the 7/8 theorem.
-/
import MNF.RH.ReservoirMass

open Set

namespace MNF.RH

/-! ## DEFINITIONS: the zones of the strip and the pair measure ("the cube") -/

/-- The mirror ρ ↦ 1 − ρ̄ of the functional-equation symmetry: the same imaginary part, the real
part reflected in 1/2.  (The same body as zeta23's `reflect`.) -/
def mirror (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- The critical line, Re ρ = 1/2. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- The open band of half-width Δ around the line, the line itself removed:
0 < |Re ρ − 1/2| < Δ. -/
def InBand (Δ : ℝ) (ρ : ℂ) : Prop := 0 < |ρ.re - 1 / 2| ∧ |ρ.re - 1 / 2| < Δ

/-- The reservoir at threshold Δ (this file's word for the points at distance ≥ Δ from the
line, see the header): |Re ρ − 1/2| ≥ Δ. -/
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

/-! ## §1 The mirror and the zones -/

/-! ### The mirror ρ ↦ 1 − ρ̄ -/

lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re := by simp [mirror]

lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im := by simp [mirror]

lemma mirror_mirror (ρ : ℂ) : mirror (mirror ρ) = ρ := by simp [mirror]

lemma mirror_injective : Function.Injective mirror :=
  Function.LeftInverse.injective mirror_mirror

/-- The mirror is the tree's reflection, definitionally.  (The `aux_` prefix marks a statement
that mentions a name from outside this file, here `Zeta23.reflect`.) -/
lemma aux_mirror_eq_reflect (ρ : ℂ) : mirror ρ = Zeta23.reflect ρ := rfl

/-! ### The mirror preserves zeros, windows and multiplicities -/

lemma is_nontrivial_zero_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    is_nontrivial_zero (mirror ρ) :=
  Zeta23.zetaZeroConfig.reflect_mem ρ hz

lemma mirror_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) :
    mirror ρ ∈ zerosIn T₁ T₂ :=
  reflect_mem_zerosIn h

lemma zeta_order_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    zeta_order (mirror ρ) = zeta_order ρ :=
  zeta_order_reflectZ hz

/-- Conjugation symmetry of the nontrivial zeros (Mathlib's `riemannZeta_conj`). -/
lemma is_nontrivial_zero_conj {ρ : ℂ} (hz : is_nontrivial_zero ρ) :
    is_nontrivial_zero ((starRingEnd ℂ) ρ) := by
  obtain ⟨h0, h1, h2⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h0, map_zero]
  · rw [Complex.conj_re]; exact h1
  · rw [Complex.conj_re]; exact h2

/-! ### Fixed points of the mirror are the points of the line -/

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

/-! ### Every nontrivial zero has multiplicity at least one -/

lemma one_le_zeta_order {ρ : ℂ} (hz : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ :=
  zeta_order_ge_one hz

/-! ### Zone bookkeeping -/

set_option linter.unusedVariables false in
/-- The three zones cover the strip.  The hypothesis `0 < Δ` is unused (hence the linter option
above) and is kept only for the statement's shape; the trichotomy itself holds for every `Δ` and
every `ρ : ℂ`.  (For `Δ ≤ 0` the band is empty and the reservoir is the whole plane, so the
zones overlap; they are disjoint exactly when `0 < Δ`.) -/
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

/-! ## §2 Degeneracy -/

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

/-! ## §3 The gap as ordinate injectivity -/

/-! ### The gap hypothesis says exactly that no nontrivial zero lies in the open band -/

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

/-! ### The gap hypothesis as injectivity of the ordinate on the band -/

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

/-! ### Under the gap the band's coincident mass vanishes -/

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

/-! ### A vanishing band coincident mass excludes band zeros of positive ordinate -/

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

/-! ### The equivalence "gap ↔ the band's coincident mass vanishes in every window" -/

/-- Under the explicit hypothesis that no nontrivial zero is real (a real zero has ordinate `0`
and lies in no window `(0, T]`, so the pair measure cannot see it).  Negative ordinates are
handled by conjugation, positive ones by `not_inBand_of_bandCoincidentMass_eq_zero`. -/
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

/-! ### No nontrivial zero is real -/

section RealZero
open Complex MeasureTheory

/-- The N = 1 Euler–Maclaurin remainder of ζ on the real axis is bounded by `1/(2σ)`:
`‖∫_1^∞ (⌊x⌋ + 1/2 − x) / x^{σ+1} dx‖ ≤ 1/2/σ` for `0 < σ`. -/
lemma zeta_em_remainder_norm_le {σ : ℝ} (hσ : 0 < σ) :
    ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤ 1 / 2 / σ := by
  have hint : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
    Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (c := 1) (by linarith) one_pos) (1 / 2)
  have hval : ∫ x in Ioi (1 : ℝ), (1 / 2 : ℝ) * x ^ (-σ - 1) = 1 / 2 / σ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (a := -σ - 1) (c := 1) (by linarith) one_pos,
      Real.one_rpow, show -σ - 1 + 1 = -σ by ring, neg_div_neg_eq]
    ring
  refine le_trans (norm_integral_le_of_norm_le hint ?_) (le_of_eq hval)
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hpos : (0 : ℝ) < x ^ (σ + 1) := Real.rpow_pos_of_pos hx0 _
  have hre : ((σ : ℂ) + 1).re = σ + 1 := by simp
  have h1 : (1 / 2 : ℝ) * x ^ (-σ - 1) = 1 / 2 / x ^ (σ + 1) := by
    rw [show -σ - 1 = -(σ + 1) by ring, Real.rpow_neg hx0.le]
    ring
  rw [ZetaSum_aux1_4' x hx0 (σ : ℂ), hre, h1]
  exact div_le_div_of_nonneg_right (ZetaSum_aux1_3 x) hpos.le

/-- **ζ has no real zero in (0, 1).** -/
theorem riemannZeta_ofReal_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hre : (0 : ℝ) < (σ : ℂ).re := by simpa using h0
  have hs1 : (σ : ℂ) ≠ 1 := Complex.ofReal_ne_one.mpr h1.ne
  have hs0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  have hJ := zeta_em_remainder_norm_le h0
  rw [← Zeta0EqZeta (N := 1) one_pos hre hs1]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1) with hJdef
  intro h
  have hσJ : (σ : ℂ) * J = 1 / (1 - (σ : ℂ)) - 1 / 2 := by
    linear_combination h
  have hnorm : ‖(σ : ℂ) * J‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
    calc σ * ‖J‖ ≤ σ * (1 / 2 / σ) := mul_le_mul_of_nonneg_left hJ h0.le
      _ = 1 / 2 := by field_simp
  have hreal : (1 / (1 - (σ : ℂ)) - 1 / 2) = ((1 / (1 - σ) - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hσJ, hreal, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have h1σ : 0 < 1 - σ := by linarith
  have hgt : 1 < 1 / (1 - σ) := one_lt_one_div h1σ (by linarith)
  have := le_abs_self (1 / (1 - σ) - 1 / 2)
  linarith

/-- **Every nontrivial zero of ζ has nonzero imaginary part**: ζ has no zero on the real
segment (0, 1). -/
theorem nontrivial_zero_im_ne_zero : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.im ≠ 0 := by
  intro ρ ⟨hz, h0, h1⟩ him
  have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hρ] at hz
  exact riemannZeta_ofReal_ne_zero_of_mem_Ioo h0 h1 hz

end RealZero

/-- **The gap as the vanishing of the band's atom.**  The unconditional form: the gap at `Δ`
holds iff the band's coincident mass vanishes in every window (negative ordinates by
conjugation, real zeros excluded by `nontrivial_zero_im_ne_zero`).  An equivalence, not a
proof of either side: it relocates `SpectralGapHyp Δ`, which stays as open as before. -/
theorem spectralGapHyp_iff_bandCoincidentMass (Δ : ℝ) :
    SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0 :=
  spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero nontrivial_zero_im_ne_zero Δ

/-! ### Nonnegativity and comparison with the off-diagonal coincident mass -/

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

/-! ## §4 The pair measure and its marginals -/

/-! ### Finite sums over a window as `Finset` sums -/

/-- A finite sum over `s ∩ {x | p x}`, `s` finite, is the `Finset` sum over `hs.toFinset.filter p`. -/
lemma finsum_mem_inter_setOf_eq_sum_filter {M : Type*} [AddCommMonoid M] {s : Set ℂ}
    (hs : s.Finite) (p : ℂ → Prop) [DecidablePred p] (g : ℂ → M) :
    ∑ᶠ x ∈ s ∩ {x | p x}, g x = ∑ x ∈ hs.toFinset.filter p, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (hs.subset inter_subset_left)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finite.mem_toFinset, mem_inter_iff, mem_ofPred_eq]

/-- `NOffLine 0 T` as a `Finset` sum over the filtered window. -/
lemma NOffLine_real_eq_sum_filter {T : ℝ} (hfin : (zerosIn 0 T).Finite) :
    (NOffLine 0 T : ℝ) = ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.re ≠ 1 / 2), (zeta_order ρ : ℝ) := by
  classical
  unfold NOffLine
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
  push_cast
  rfl

/-- `N0 0 T` as a `Finset` sum over the filtered window. -/
lemma N0_real_eq_sum_filter {T : ℝ} (hfin : (zerosIn 0 T).Finite) :
    (N0 0 T : ℝ) = ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.re = 1 / 2), (zeta_order ρ : ℝ) := by
  classical
  unfold N0
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
  push_cast
  rfl

/-- The window splits exactly into its on-line and its off-line zeros (with multiplicity). -/
theorem Ncount_eq_N0_add_NOffLine (T₁ T₂ : ℝ) : Ncount T₁ T₂ = N0 T₁ T₂ + NOffLine T₁ T₂ := by
  classical
  have hfin := zerosIn_finite T₁ T₂
  unfold N0 NOffLine
  rw [Ncount_eq_sum hfin, finsum_mem_inter_setOf_eq_sum_filter hfin,
    finsum_mem_inter_setOf_eq_sum_filter hfin, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs <;> simp_all

/-! ### `pairSum` as a double `Finset` sum over the finite window -/

/-- `pairSum T f` as a double `Finset` sum, given any proof that the window `zerosIn 0 T` is finite
(`zerosIn_finite 0 T` supplies one; the proof is a hypothesis so that no theorem appears inside
the statement). -/
theorem pairSum_eq_sum {T : ℝ} (hfin : (zerosIn 0 T).Finite) (f : ℝ → ℝ → ℝ → ℝ) :
    pairSum T f = ∑ ρ ∈ hfin.toFinset, ∑ ρ' ∈ hfin.toFinset,
      (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im) := by
  unfold pairSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]

/-- The same, with the window's finiteness proof `zerosIn_finite 0 T` written into the
statement.  (The `aux_` prefix marks a statement that mentions a proof term or a name from
outside this file.) -/
theorem aux_pairSum_eq_finset_sum (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    pairSum T f = ∑ ρ ∈ (zerosIn_finite 0 T).toFinset, ∑ ρ' ∈ (zerosIn_finite 0 T).toFinset,
      (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im) :=
  pairSum_eq_sum (zerosIn_finite 0 T) f

/-! ### The total mass: `pairSum T 1 = N(0,T)²` -/

/-- The pair measure of the constant `1` is `N(0,T)²`. -/
theorem pairSum_const (T : ℝ) : pairSum T (fun _ _ _ => 1) = (Ncount 0 T : ℝ) ^ 2 := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, Ncount_eq_sum hfin]
  push_cast
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  ring

/-! ### The marginals: a test function of one coordinate only -/

/-- The first marginal: a test function of the first real part alone integrates to
`N(0,T) · Σ_ρ m(ρ) g(Re ρ − 1/2)`. -/
theorem pairSum_fst (T : ℝ) (g : ℝ → ℝ) :
    pairSum T (fun a _ _ => g a) =
      (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2) := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, Ncount_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [mul_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  ring

/-- The second marginal: the same for the second real part. -/
theorem pairSum_snd (T : ℝ) (g : ℝ → ℝ) :
    pairSum T (fun _ b _ => g b) =
      (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2) := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, Ncount_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  ring

/-! ### The first marginal of the reservoir indicator: `N(0,T) · N_off(δ; 0, T)` -/

/-- The pair measure of `1[δ ≤ |a|]` (a function of the first real part) is
`N(0,T) · NOff δ 0 T`. -/
theorem pairSum_fst_indicator (T δ : ℝ) :
    pairSum T (fun a _ _ => if δ ≤ |a| then 1 else 0) = (Ncount 0 T : ℝ) * (NOff δ 0 T : ℝ) := by
  rw [pairSum_fst]
  congr 1
  rw [NOff_eq_sum_ite, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs <;> simp

/-! ### The first marginal of `|a|`: `N(0,T) · reservoirMass T`, and the double layer cake -/

/-- The pair measure of `|a|` (the distance of the first zero from the line) is
`N(0,T) · reservoirMass T`. -/
theorem pairSum_fst_abs (T : ℝ) :
    pairSum T (fun a _ _ => |a|) = (Ncount 0 T : ℝ) * reservoirMass T := by
  rw [pairSum_fst]
  rfl

/-- **The double layer cake**: `pairSum T |a| = N(0,T) · ∫₀^{1/2} NOff δ 0 T dδ`
(from `reservoirMass_eq_integral`). -/
theorem pairSum_fst_abs_eq_integral (T : ℝ) :
    pairSum T (fun a _ _ => |a|) =
      (Ncount 0 T : ℝ) * ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ) := by
  rw [pairSum_fst_abs, reservoirMass_eq_integral]

/-! ### The swap symmetry of ordered pairs -/

/-- Swapping the two zeros of each ordered pair: `pairSum T f = pairSum T (f ∘ swap)`, the
ordinate difference changing sign. -/
theorem pairSum_swap (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    pairSum T f = pairSum T (fun a b s => f b a (-s)) := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, pairSum_eq_sum hfin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  rw [neg_sub, mul_comm (zeta_order ρ' : ℝ)]

/-! ### Positivity and monotonicity -/

/-- The pair measure of a nonnegative test function is nonnegative. -/
theorem pairSum_nonneg (T : ℝ) {f : ℝ → ℝ → ℝ → ℝ} (hf : ∀ a b s, 0 ≤ f a b s) :
    0 ≤ pairSum T f := by
  rw [pairSum_eq_sum (zerosIn_finite 0 T)]
  exact Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun ρ' _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hf _ _ _)

/-- The pair measure is monotone in the test function. -/
theorem pairSum_mono (T : ℝ) {f g : ℝ → ℝ → ℝ → ℝ} (h : ∀ a b s, f a b s ≤ g a b s) :
    pairSum T f ≤ pairSum T g := by
  rw [pairSum_eq_sum (zerosIn_finite 0 T), pairSum_eq_sum (zerosIn_finite 0 T)]
  exact Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun ρ' _ =>
    mul_le_mul_of_nonneg_left (h _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-! ### The diagonal mass `Σ m(ρ)²`: between `N(0,T)` and `N(0,T)²` -/

/-- The diagonal mass is nonnegative. -/
theorem diagonalMass_nonneg (T : ℝ) : 0 ≤ diagonalMass T := by
  unfold diagonalMass
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)]
  exact Finset.sum_nonneg fun ρ _ => sq_nonneg _

/-- `Σ m(ρ)² ≤ (Σ m(ρ))²`: each `m(ρ) ≤ Σ m` since all multiplicities are nonnegative. -/
theorem diagonalMass_le_sq_Ncount (T : ℝ) : diagonalMass T ≤ (Ncount 0 T : ℝ) ^ 2 := by
  have hfin := zerosIn_finite 0 T
  unfold diagonalMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Ncount_eq_sum hfin]
  push_cast
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun ρ' _ => Nat.cast_nonneg (zeta_order ρ')) hρ) (Nat.cast_nonneg _)

/-- `N(0,T) ≤ Σ m(ρ)²`: each zero has multiplicity `m(ρ) ≥ 1` (`zeta_order_ge_one`), so
`m(ρ) ≤ m(ρ)²`. -/
theorem Ncount_le_diagonalMass (T : ℝ) : (Ncount 0 T : ℝ) ≤ diagonalMass T := by
  have hfin := zerosIn_finite 0 T
  unfold diagonalMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Ncount_eq_sum hfin]
  push_cast
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have h1 : (1 : ℝ) ≤ (zeta_order ρ : ℝ) := by
    exact_mod_cast zeta_order_ge_one (hfin.mem_toFinset.1 hρ).1
  exact le_self_pow₀ h1 two_ne_zero

/-! ## §5 The atom at `s = 0` -/

/-! ### The atom splits into the diagonal and the off-diagonal coincident mass -/

/-- **The atom at `s = 0`**: the coincident mass is the diagonal mass `Σ m(ρ)²` plus the
off-diagonal coincident mass (ordered pairs of distinct zeros with equal ordinates). -/
theorem coincidentMass_eq (T : ℝ) :
    coincidentMass T = diagonalMass T + offDiagonalCoincidentMass T := by
  classical
  have hfin := zerosIn_finite 0 T
  unfold coincidentMass diagonalMass offDiagonalCoincidentMass
  rw [pairSum_eq_sum hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin, Finset.sum_filter]
  have h1 : (zeta_order ρ : ℝ) ^ 2 =
      ∑ ρ' ∈ hfin.toFinset, if ρ' = ρ then (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) else 0 := by
    rw [Finset.sum_ite_eq', if_pos hρ, sq]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  by_cases heq : ρ' = ρ
  · subst heq
    simp
  · by_cases him : ρ'.im = ρ.im
    · rw [if_pos (sub_eq_zero.2 him.symm), if_neg heq, if_pos ⟨heq, him⟩]
      ring
    · rw [if_neg (fun h => him (sub_eq_zero.1 h).symm), if_neg heq, if_neg (fun h => him h.2)]
      ring

/-! ### The off-diagonal coincident mass is nonnegative -/

theorem offDiagonalCoincidentMass_nonneg (T : ℝ) : 0 ≤ offDiagonalCoincidentMass T := by
  classical
  have hfin := zerosIn_finite 0 T
  unfold offDiagonalCoincidentMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_nonneg fun ρ _ => ?_
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
  exact Finset.sum_nonneg fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### Every off-line zero contributes `m(ρ)²` through its mirror -/

/-- **Off-line zeros are seen by the atom**: `Σ_{ρ off-line} m(ρ)² ≤ offDiagonalCoincidentMass T`.
Each off-line `ρ` of the window pairs with `mirror ρ`, which lies in the window, is distinct from
`ρ`, has the same ordinate and the same multiplicity. -/
theorem offLine_sq_le_offDiagonalCoincidentMass (T : ℝ) :
    ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | ρ.re ≠ 1 / 2}, (zeta_order ρ : ℝ) ^ 2 ≤
      offDiagonalCoincidentMass T := by
  classical
  have hfin := zerosIn_finite 0 T
  unfold offDiagonalCoincidentMass
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hinner : ∀ ρ ∈ hfin.toFinset,
      0 ≤ ∑ᶠ ρ' ∈ zerosIn 0 T ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im},
        (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) := by
    intro ρ _
    rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
    exact Finset.sum_nonneg fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun ρ => ρ.re ≠ 1 / 2) hfin.toFinset) (fun ρ hρ _ => hinner ρ hρ))
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [Finset.mem_filter, Finite.mem_toFinset] at hρ
  obtain ⟨hρw, hoff⟩ := hρ
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
  have hmem : mirror ρ ∈ hfin.toFinset.filter (fun ρ' => ρ' ≠ ρ ∧ ρ'.im = ρ.im) := by
    rw [Finset.mem_filter, Finite.mem_toFinset]
    refine ⟨mirror_mem_zerosIn hρw, ?_, mirror_im ρ⟩
    intro heq
    exact hoff ((mirror_eq_self_iff ρ).1 heq)
  calc (zeta_order ρ : ℝ) ^ 2 = (zeta_order ρ : ℝ) * (zeta_order (mirror ρ) : ℝ) := by
        rw [zeta_order_mirror hρw.1, sq]
    _ ≤ _ := Finset.single_le_sum
        (f := fun ρ' => (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ))
        (fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hmem

/-! ### The off-diagonal coincident mass against the counts -/

/-- **The off-diagonal coincident mass against the counts.**  An ordered pair of distinct zeros
with equal ordinates has at least one off-line member: for an off-line `ρ` the partners weigh at
most `N(0,T)`, and for an on-line `ρ` every partner is off-line (two on-line zeros with the same
ordinate coincide), so they weigh at most `NOffLine 0 T`.  Hence
`offDiag ≤ NOffLine · N + N0 · NOffLine`.  (The `N0 · NOffLine` term cannot be dropped by
bookkeeping: see the header.) -/
theorem offDiagonalCoincidentMass_le (T : ℝ) :
    offDiagonalCoincidentMass T ≤
      (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ) + (N0 0 T : ℝ) * (NOffLine 0 T : ℝ) := by
  classical
  have hfin := zerosIn_finite 0 T
  have hNOff := NOffLine_real_eq_sum_filter hfin
  have hN0 := N0_real_eq_sum_filter hfin
  have hNc : (Ncount 0 T : ℝ) = ∑ ρ ∈ hfin.toFinset, (zeta_order ρ : ℝ) := by
    rw [Ncount_eq_sum hfin]; push_cast; rfl
  unfold offDiagonalCoincidentMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  -- the three counts as sums over the whole window with `if`
  rw [hNOff, hN0, Finset.sum_filter, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin, ← Finset.mul_sum]
  have hρw : ρ ∈ zerosIn 0 T := hfin.mem_toFinset.1 hρ
  by_cases hoff : ρ.re ≠ 1 / 2
  · -- off-line: the partners weigh at most `N(0,T)`
    rw [if_pos hoff, if_neg hoff, zero_mul, add_zero, hNc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)
  · -- on-line: every partner is off-line
    rw [if_neg hoff, if_pos (not_not.1 hoff), zero_mul, zero_add, ← Finset.sum_filter]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
    intro ρ' h
    rw [Finset.mem_filter] at h ⊢
    refine ⟨h.1, fun hre => h.2.1 ?_⟩
    have hre' : ρ.re = 1 / 2 := not_not.1 hoff
    exact Complex.ext (by rw [hre, hre']) h.2.2

/-- The simpler form `offDiag ≤ 2 · NOffLine · N(0,T)` (from `N0 ≤ N`). -/
theorem offDiagonalCoincidentMass_le_two_mul (T : ℝ) :
    offDiagonalCoincidentMass T ≤ 2 * (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ) := by
  have h := offDiagonalCoincidentMass_le T
  have h0 : (N0 0 T : ℝ) ≤ Ncount 0 T := by exact_mod_cast N0_le_Ncount 0 T
  have hoff : (0 : ℝ) ≤ NOffLine 0 T := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h0 hoff]

/-! ### Under "all zeros on the line" the off-diagonal coincident mass vanishes -/

theorem offDiagonalCoincidentMass_eq_zero_of_onLine
    (h : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) (T : ℝ) : offDiagonalCoincidentMass T = 0 := by
  have hfin := zerosIn_finite 0 T
  unfold offDiagonalCoincidentMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  have hρw : ρ ∈ zerosIn 0 T := hfin.mem_toFinset.1 hρ
  have hempty : zerosIn 0 T ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im} = ∅ := by
    ext ρ'
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hρ' hne him
    apply hne
    have h1 : ρ.re = 1 / 2 := h ρ hρw.1
    have h2 : ρ'.re = 1 / 2 := h ρ' hρ'.1
    exact Complex.ext (by rw [h1, h2]) him
  rw [hempty, finsum_mem_empty]

/-! ### Conversely: a vanishing off-diagonal coincident mass forces the zeros of positive
ordinate onto the line -/

theorem onLine_of_offDiagonalCoincidentMass_eq_zero (h : ∀ T, offDiagonalCoincidentMass T = 0)
    {ρ : ℂ} (hz : is_nontrivial_zero ρ) (hpos : 0 < ρ.im) : OnLine ρ := by
  classical
  by_contra hon
  have hfin := zerosIn_finite 0 ρ.im
  have hρ : ρ ∈ zerosIn 0 ρ.im := ⟨hz, hpos, le_rfl⟩
  have hle := offLine_sq_le_offDiagonalCoincidentMass ρ.im
  rw [h ρ.im, finsum_mem_inter_setOf_eq_sum_filter hfin] at hle
  have hmem : ρ ∈ hfin.toFinset.filter (fun ρ => ρ.re ≠ 1 / 2) := by
    rw [Finset.mem_filter, Finite.mem_toFinset]
    exact ⟨hρ, hon⟩
  have h1 : (1 : ℝ) ≤ (zeta_order ρ : ℝ) := by exact_mod_cast zeta_order_ge_one hz
  have h2 := Finset.single_le_sum (fun ρ' _ => sq_nonneg (zeta_order ρ' : ℝ)) hmem
  have h3 : (1 : ℝ) ≤ (zeta_order ρ : ℝ) ^ 2 := one_le_pow₀ h1
  linarith

/-! ### The off-diagonal coincident mass is eventually a bounded proportion of `N(0,T)²` -/

/-- From `offDiag ≤ 2 · NOffLine · N` and `offLine_le_one_third`. -/
theorem offDiagonalCoincidentMass_le_two_thirds :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      offDiagonalCoincidentMass T ≤ (2 / 3 + ε) * (Ncount 0 T : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := offLine_le_one_third (ε / 2) (by positivity)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 := offDiagonalCoincidentMass_le_two_mul T
  have hN : (0 : ℝ) ≤ Ncount 0 T := Nat.cast_nonneg _
  calc offDiagonalCoincidentMass T ≤ 2 * (NOffLine 0 T : ℝ) * Ncount 0 T := h2
    _ ≤ 2 * ((1 / 3 + ε / 2) * Ncount 0 T) * Ncount 0 T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) hN
    _ = (2 / 3 + ε) * (Ncount 0 T : ℝ) ^ 2 := by ring

/-- With `N0 = N − NOffLine` (`Ncount_eq_N0_add_NOffLine`), `offDiagonalCoincidentMass_le` reads
`offDiag ≤ NOffLine · (2N − NOffLine) = N² − (N − NOffLine)²`; as `NOffLine ≤ (1/3 + ε') N`
eventually (`offLine_le_one_third`, with `ε' = min (3ε/4) (2/3)` so that `N − NOffLine ≥ 0`),
this is at most `(1 − (2/3 − ε')²) N² ≤ (5/9 + ε) N²`.  Read termwise the same arithmetic is
`(1/3)·1 + (2/3)·(1/3) = 5/9`: the off-line third against everything, the on-line two thirds
against the off-line third.  The constant cannot be improved from these two inputs alone: for a
hypothetical window with one on-line zero of multiplicity `2N/3` and `N/3` simple off-line zeros
all at one ordinate, the off-diagonal coincident mass is `5N²/9 − N/3`. -/
theorem offDiagonalCoincidentMass_le_five_ninths :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      offDiagonalCoincidentMass T ≤ (5 / 9 + ε) * (Ncount 0 T : ℝ) ^ 2 := by
  intro ε hε
  set ε' : ℝ := min (3 * ε / 4) (2 / 3) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'1 : ε' ≤ 3 * ε / 4 := min_le_left _ _
  have hε'2 : ε' ≤ 2 / 3 := min_le_right _ _
  obtain ⟨T₀, hT₀⟩ := offLine_le_one_third ε' hε'pos
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 := offDiagonalCoincidentMass_le T
  have hsplit : (Ncount 0 T : ℝ) = N0 0 T + NOffLine 0 T := by
    exact_mod_cast Ncount_eq_N0_add_NOffLine 0 T
  have hN0 : (N0 0 T : ℝ) = Ncount 0 T - NOffLine 0 T := by linarith
  rw [hN0] at h2
  have hN : (0 : ℝ) ≤ Ncount 0 T := Nat.cast_nonneg _
  have hab : (1 - (1 / 3 + ε')) * (Ncount 0 T : ℝ) ≤ (Ncount 0 T : ℝ) - NOffLine 0 T := by
    nlinarith
  have ha : 0 ≤ (1 - (1 / 3 + ε')) * (Ncount 0 T : ℝ) := mul_nonneg (by linarith) hN
  have hsq := mul_self_le_mul_self ha hab
  nlinarith [mul_nonneg (sq_nonneg (Ncount 0 T : ℝ)) (sq_nonneg ε'),
    mul_nonneg (sq_nonneg (Ncount 0 T : ℝ)) (by linarith : (0 : ℝ) ≤ ε - 4 * ε' / 3)]

/-! ## Axiom audit -/

-- §1 The mirror and the zones
-- §2 Degeneracy
-- §3 The gap as ordinate injectivity
-- §4 The pair measure and its marginals
-- §5 The atom at s = 0

end MNF.RH
