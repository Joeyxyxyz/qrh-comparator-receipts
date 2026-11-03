/-
═══════════════════════════════════════════════════════════════════════
MNF × QUASI-RH BRIDGE  (bridge_2) — ported to OpenAI's toolchain
What the 7/8 zero-free half-plane does — and does not do — to the
MNF gap hypothesis.
═══════════════════════════════════════════════════════════════════════
Lean:    leanprover/lean4:v4.34.1
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612   (the pin of openai/math)
Port of the corpus file MNF_Bridge78.lean (Lean v4.24.0, Mathlib f897ebcf).
Differences from that file: the header and the status comments;
`nontrivial_zero_re_mem` added in §7; one tactic call in `twoFactor_one_sub`
(`push_neg`, deprecated in the newer Mathlib) replaced by a direct term.
No lemma name had to change: this exact file also compiles at the corpus
pin.  At both pins: no warnings, and all 14 axiom reports list only
propext, Classical.choice, Quot.sound.
Imports only `Mathlib.NumberTheory.LSeries.RiemannZeta` (compiled that way;
everything lives in `namespace MNF.Bridge78`, no `open`s).

REGISTER: [WRAPPER] + [TRIPWIRE].  No new analytic number theory.
The 7/8 theorem enters ONLY as the explicit hypothesis

    ZeroFreeRightOf (7/8)  :=  ∀ s : ℂ, 7/8 < s.re → riemannZeta s ≠ 0

which is the statement (their `s` is an implicit argument) of
    OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
(github.com/openai/math, lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean,
 Lean v4.34.1, released 2026-10-06).  In THIS file that theorem is never
used: it stays a hypothesis, and nothing here is unconditional about ζ
beyond what Mathlib already proves.  The companion file
MNF_Bridge78_Unconditional.lean discharges the hypothesis from OpenAI's
proof; what that is worth depends on the Comparator receipt, not on this
file.

CONTENTS
  §1  tau_threshold                  tau-half with any bound c < Δ
  §2  abstract zero sets             strip + (s ↦ 1-s) symmetry + Re ≤ θ
  §3  STRUCTURAL NO-GO               kernel-checked countermodel: the inputs
                                     of §2 at θ = 7/8 do not force the line;
                                     also realised as the zero set of a
                                     polynomial with f(1-s) = f(s)
  §4  ζ-instantiation                corpus definitions, reflection of zeros
  §5  consequences of ZeroFreeRightOf θ
        shifted_bounded_of_zeroFree      |x| ≤ θ - 1/2 on ShiftedZeroSpectrum
        strip_rh_of_gap                  gap at any Δ > θ - 1/2 ⟹ zeros on line
        strip_rh_iff_remaining_strip     RH(strip) ⟺ no zeros in 1/2 < Re ≤ θ
  §6  Mathlib's `RiemannHypothesis`  equivalences under ZeroFreeRightOf θ, θ < 1
  §7  θ = 7/8 specialisations        the statements to cite
  §8  EULER-TYPE NO-GO               F = ζ·Q, Q a Dirichlet polynomial in 2^{-s}:
                                     the same zeros as ζ in Re s > 7/8, a
                                     symmetric functional equation, and a zero
                                     at Re s ≈ 0.737

HOW TO READ §3, §7 AND §8 TOGETHER.  §7 says exactly what is left IF the
7/8 theorem is correct: the strip 1/2 < Re s ≤ 7/8.  §3 and §8 are
countermodels whose stated properties are kernel-checked (the one exception,
multiplicativity of the coefficients in §8, is by hand and marked so).
They do not say RH is unprovable; they say what a proof cannot rely on alone.

KILL CRITERIA for any future argument for the gap:
  K1  `analytic_no_go` (§3).  An entire function (a quartic polynomial) with
      the exact functional equation f(1-s) = f(s) (the symmetry ξ has), real
      on the real axis, zeros in the open strip with Re ≤ 7/8, zeros off the
      line.
      ⇒ an argument using only analyticity, the reflection and conjugation
        symmetries of the zero set, the strip, and the 7/8 bound is wrong.
        (Four zeros only: K1 says nothing about arguments that use growth or
        the density of zeros.)
  K2  Davenport–Heilbronn (informal; NOT formalised here).  A Dirichlet
      series with a functional equation and no Euler product, with zeros off
      the line inside the strip (Spira, Math. Comp. 63 (1994)) and also zeros
      with Re s > 1 (Davenport–Heilbronn 1936; Titchmarsh §10.25).  Because
      of the latter it does NOT satisfy the analogue of the 7/8 bound, so K2
      only tests arguments that do not use that bound.
  K3  `euler_type_no_go`, `completed_twoFactor_symm` (§8).
      F(s) = ζ(s)·Q(s),  Q(s) = 1 + (43/15)·2^{-s} + 2·4^{-s}
                              = (1 + (5/3)·2^{-s})(1 + (6/5)·2^{-s}).
      Kernel-checked: in Re s > 7/8 the zeros of F are exactly those of ζ
      (so F satisfies the 7/8 bound iff ζ does); F has a zero at
      Re s = log₂(5/3) ≈ 0.737; Q(1-s) = 2^{2s-1}·Q(s); and the completed
      function 2^s·Λ(s)·Q(s) is invariant under s ↦ 1-s (Λ = Mathlib's
      completedRiemannZeta).
      By hand, not formalised: F has multiplicative coefficients (it is ζ
      with its factor at 2 replaced by Q(s)/(1 - 2^{-s})).
      Caveat: the replaced factor is not an Euler factor in the usual sense —
      it has zeros, and those are F's off-line zeros; F fails the
      Selberg-class Euler-product axiom.
      ⇒ multiplicative coefficients + a functional equation + the 7/8 bound
        are not enough.  K3 does NOT test arguments that use the
        non-vanishing of every local factor.
If an argument would go through verbatim for any of these, it is wrong.
Heuristically, a closing lemma has to use something ζ has and each of the
three lacks.  The natural candidate is the Euler product in its strong form:
a local factor (1 - p^{-s})^{-1}, hence zero-free, at EVERY prime — e.g.
through 1/ζ(s) = Σ μ(n) n^{-s} with |μ(n)| ≤ 1.  (Guidance, not a theorem of
this file.)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MNF.Bridge78


-- ═══════════════════════════════════════════════════════
-- §1  GENERALISED TAU-HALF
-- ═══════════════════════════════════════════════════════

/-- Corpus definition, verbatim (output72 §1). -/
def SpectralGapProperty (S : Set ℝ) (Δ : ℝ) : Prop :=
  ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ

/-- **Generalised tau-half.** A set bounded by `c` with a gap at any
threshold `Δ > c` is contained in `{0}`. -/
theorem tau_threshold (S : Set ℝ) {c Δ : ℝ}
    (h_bound : ∀ x ∈ S, |x| ≤ c) (hcΔ : c < Δ)
    (h_gap : SpectralGapProperty S Δ) : S ⊆ {0} := by
  intro x hx
  rcases h_gap x hx with rfl | hge
  · exact Set.mem_singleton 0
  · exact absurd (h_bound x hx) (not_le.mpr (lt_of_lt_of_le hcΔ hge))

-- ═══════════════════════════════════════════════════════
-- §2  ABSTRACT ZERO SETS
-- ═══════════════════════════════════════════════════════

/-- Shifted spectrum `{Re ρ - 1/2 : ρ ∈ Z}` of an arbitrary set `Z ⊆ ℂ`. -/
def Shifted (Z : Set ℂ) : Set ℝ := {x | ∃ ρ ∈ Z, x = ρ.re - 1/2}

/-- The two structural facts the Level-1 chain uses about the nontrivial
zeros: they lie in the open strip, and the set is closed under `s ↦ 1 - s`. -/
structure StripSymmetric (Z : Set ℂ) : Prop where
  strip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1
  reflect : ∀ ρ ∈ Z, 1 - ρ ∈ Z

theorem re_one_sub (ρ : ℂ) : (1 - ρ).re = 1 - ρ.re := by simp

/-- A right-hand bound `Re ≤ θ` on a reflection-symmetric set bounds the
shifted spectrum by `θ - 1/2` on both sides. -/
theorem shifted_bound_of_right_bound {Z : Set ℂ} (hZ : StripSymmetric Z) {θ : ℝ}
    (hθ : ∀ ρ ∈ Z, ρ.re ≤ θ) : ∀ x ∈ Shifted Z, |x| ≤ θ - 1/2 := by
  rintro x ⟨ρ, hρ, rfl⟩
  have h1 := hθ ρ hρ
  have h2 := hθ (1 - ρ) (hZ.reflect ρ hρ)
  rw [re_one_sub] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Right-hand bound `θ` + gap at any `Δ > θ - 1/2` ⟹ every point is on the line. -/
theorem on_line_of_gap {Z : Set ℂ} (hZ : StripSymmetric Z) {θ Δ : ℝ}
    (hθ : ∀ ρ ∈ Z, ρ.re ≤ θ) (hΔ : θ - 1/2 < Δ)
    (h_gap : SpectralGapProperty (Shifted Z) Δ) : ∀ ρ ∈ Z, ρ.re = 1/2 := by
  intro ρ hρ
  have hmem : ρ.re - 1/2 ∈ Shifted Z := ⟨ρ, hρ, rfl⟩
  have h0 := tau_threshold (Shifted Z) (shifted_bound_of_right_bound hZ hθ) hΔ h_gap hmem
  have h0' : ρ.re - 1/2 = 0 := h0
  linarith

/-- Conversely, "all on the line" gives the gap at every threshold. -/
theorem gap_of_on_line {Z : Set ℂ} (h : ∀ ρ ∈ Z, ρ.re = 1/2) (Δ : ℝ) :
    SpectralGapProperty (Shifted Z) Δ := by
  rintro x ⟨ρ, hρ, rfl⟩
  left
  rw [h ρ hρ]; ring

/-- **The remaining strip.** For a reflection-symmetric set with `Re ≤ θ`:
all points on the line ⟺ no point with `1/2 < Re ≤ θ`. -/
theorem on_line_iff_remaining_strip_empty {Z : Set ℂ} (hZ : StripSymmetric Z) {θ : ℝ}
    (hθ : ∀ ρ ∈ Z, ρ.re ≤ θ) :
    (∀ ρ ∈ Z, ρ.re = 1/2) ↔ (∀ ρ ∈ Z, ¬ (1/2 < ρ.re ∧ ρ.re ≤ θ)) := by
  constructor
  · intro h ρ hρ hstrip
    have := h ρ hρ
    linarith [hstrip.1]
  · intro h ρ hρ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hr := hZ.reflect ρ hρ
      refine h (1 - ρ) hr ⟨?_, hθ _ hr⟩
      rw [re_one_sub]; linarith
    · exact h ρ hρ ⟨hgt, hθ ρ hρ⟩

-- ═══════════════════════════════════════════════════════
-- §3  STRUCTURAL NO-GO  (kernel-checked tripwire)
-- ═══════════════════════════════════════════════════════

/-- The four points `1/4 ± i`, `3/4 ± i`. -/
def Counter : Set ℂ := {ρ | (ρ.re = 1/4 ∨ ρ.re = 3/4) ∧ (ρ.im = 1 ∨ ρ.im = -1)}

theorem counter_stripSymmetric : StripSymmetric Counter where
  strip := by
    rintro ρ ⟨hre | hre, _⟩ <;> rw [hre] <;> constructor <;> norm_num
  reflect := by
    rintro ρ ⟨hre, him⟩
    refine ⟨?_, ?_⟩
    · rw [re_one_sub]
      rcases hre with h | h <;> rw [h]
      · right; norm_num
      · left; norm_num
    · have him' : (1 - ρ).im = -ρ.im := by simp
      rw [him']
      rcases him with h | h <;> rw [h]
      · right; rfl
      · left; norm_num

/-- `Counter` is also closed under complex conjugation (the other symmetry of the zero set). -/
theorem counter_conj : ∀ ρ ∈ Counter, (starRingEnd ℂ) ρ ∈ Counter := by
  rintro ρ ⟨hre, him⟩
  refine ⟨by simpa using hre, ?_⟩
  have : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
  rw [this]
  rcases him with h | h <;> rw [h]
  · right; rfl
  · left; norm_num

theorem counter_right_bound : ∀ ρ ∈ Counter, ρ.re ≤ 7/8 := by
  rintro ρ ⟨hre | hre, _⟩ <;> rw [hre] <;> norm_num

theorem counter_shifted_bound : ∀ x ∈ Shifted Counter, |x| ≤ 3/8 := by
  have h := shifted_bound_of_right_bound counter_stripSymmetric counter_right_bound
  intro x hx
  have := h x hx
  norm_num at this ⊢
  exact this

theorem counter_off_line : ¬ ∀ ρ ∈ Counter, ρ.re = 1/2 := by
  intro h
  have hmem : (⟨1/4, 1⟩ : ℂ) ∈ Counter := ⟨Or.inl rfl, Or.inl rfl⟩
  have := h _ hmem
  norm_num at this

/-- **STRUCTURAL NO-GO.** Strip + reflection symmetry + the `7/8` bound do
not imply "all on the line". Every hypothesis is satisfied by `Counter`,
and the conclusion fails there. -/
theorem structural_inputs_insufficient :
    ¬ ∀ Z : Set ℂ, StripSymmetric Z → (∀ ρ ∈ Z, ρ.re ≤ 7/8) → ∀ ρ ∈ Z, ρ.re = 1/2 :=
  fun h => counter_off_line (h Counter counter_stripSymmetric counter_right_bound)

/-- Same statement in gap form: the structural inputs do not yield the gap
at any threshold `Δ > 3/8` (for `Δ > 3/8` the gap is equivalent to the line,
by `on_line_of_gap`). -/
theorem structural_inputs_do_not_give_gap {Δ : ℝ} (hΔ : 3/8 < Δ) :
    ¬ ∀ Z : Set ℂ, StripSymmetric Z → (∀ ρ ∈ Z, ρ.re ≤ 7/8) →
        SpectralGapProperty (Shifted Z) Δ := by
  intro h
  refine counter_off_line ?_
  exact on_line_of_gap counter_stripSymmetric counter_right_bound (by linarith)
    (h Counter counter_stripSymmetric counter_right_bound)


/-! ### The same no-go for an entire function with an exact functional equation

`Counter` is not just a set: it is the full zero set of a real-coefficient
quartic that satisfies `f (1 - s) = f s` identically. So "analytic +
functional equation + real on the real axis + zeros in the strip with
`Re ≤ 7/8`" still does not force the line. -/

/-- A real-coefficient quartic, symmetric under `s ↦ 1 - s`, whose zero set is `Counter`. -/
noncomputable def counterPoly (s : ℂ) : ℂ := ((s - 1/4) ^ 2 + 1) * ((s - 3/4) ^ 2 + 1)

/-- Exact functional equation `f (1 - s) = f s`. -/
theorem counterPoly_symm (s : ℂ) : counterPoly (1 - s) = counterPoly s := by
  unfold counterPoly; ring

/-- Real on the real axis: `f (conj s) = conj (f s)`. -/
theorem counterPoly_conj (s : ℂ) :
    counterPoly ((starRingEnd ℂ) s) = (starRingEnd ℂ) (counterPoly s) := by
  unfold counterPoly
  simp only [map_mul, map_add, map_pow, map_sub, map_one, map_div₀, map_ofNat]

theorem sq_add_one_eq_zero_iff (z : ℂ) : z ^ 2 + 1 = 0 ↔ z = Complex.I ∨ z = -Complex.I := by
  have hfac : z ^ 2 + 1 = (z - Complex.I) * (z + Complex.I) := by
    linear_combination Complex.I_sq
  rw [hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- The zero set of `counterPoly` is exactly `Counter`. -/
theorem counterPoly_eq_zero_iff (s : ℂ) : counterPoly s = 0 ↔ s ∈ Counter := by
  unfold counterPoly
  rw [mul_eq_zero, sq_add_one_eq_zero_iff, sq_add_one_eq_zero_iff]
  constructor
  · rintro ((h | h) | (h | h))
    · have hs : s = 1/4 + Complex.I := by linear_combination h
      refine ⟨Or.inl ?_, Or.inl ?_⟩ <;> rw [hs] <;> simp
    · have hs : s = 1/4 - Complex.I := by linear_combination h
      refine ⟨Or.inl ?_, Or.inr ?_⟩ <;> rw [hs] <;> simp
    · have hs : s = 3/4 + Complex.I := by linear_combination h
      refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> rw [hs] <;> simp
    · have hs : s = 3/4 - Complex.I := by linear_combination h
      refine ⟨Or.inr ?_, Or.inr ?_⟩ <;> rw [hs] <;> simp
  · rintro ⟨hre | hre, him | him⟩
    · left; left; apply Complex.ext <;> simp [hre, him]
    · left; right; apply Complex.ext <;> simp [hre, him]
    · right; left; apply Complex.ext <;> simp [hre, him]
    · right; right; apply Complex.ext <;> simp [hre, him]

/-- `counterPoly` is entire. -/
theorem counterPoly_differentiable : Differentiable ℂ counterPoly := by
  unfold counterPoly
  fun_prop

/-- **ANALYTIC NO-GO.** An entire function `f` (a real-coefficient quartic)
with the exact functional equation `f (1 - s) = f s`, real on the real axis,
every zero in the open strip with real part `≤ 7/8` — and zeros off the
critical line. -/
theorem analytic_no_go :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ s, f (1 - s) = f s) ∧
      (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) ∧
      (∀ s, f s = 0 → 0 < s.re ∧ s.re < 1 ∧ s.re ≤ 7/8) ∧
      ¬ (∀ s, f s = 0 → s.re = 1/2) := by
  refine ⟨counterPoly, counterPoly_differentiable, counterPoly_symm, counterPoly_conj, ?_, ?_⟩
  · intro s hs
    have hmem := (counterPoly_eq_zero_iff s).mp hs
    exact ⟨(counter_stripSymmetric.strip s hmem).1, (counter_stripSymmetric.strip s hmem).2,
      counter_right_bound s hmem⟩
  · intro h
    exact counter_off_line (fun ρ hρ => h ρ ((counterPoly_eq_zero_iff ρ).mpr hρ))

-- ═══════════════════════════════════════════════════════
-- §4  ζ-INSTANTIATION
-- ═══════════════════════════════════════════════════════

/-- Corpus definition, verbatim (output72 §1). -/
def is_nontrivial_zero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Corpus definition, verbatim (output72 §1). -/
def ShiftedZeroSpectrum : Set ℝ :=
  {x | ∃ ρ, is_nontrivial_zero ρ ∧ x = ρ.re - 1/2}

/-- The nontrivial zeros as a set. -/
def ZetaZeros : Set ℂ := {ρ | is_nontrivial_zero ρ}

theorem shifted_eq : ShiftedZeroSpectrum = Shifted ZetaZeros := by
  ext x
  constructor
  · rintro ⟨ρ, hρ, hx⟩
    exact ⟨ρ, hρ, hx⟩
  · rintro ⟨ρ, hρ, hx⟩
    exact ⟨ρ, hρ, hx⟩

/-- A point of the open strip is not a non-positive integer. -/
theorem ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro h
  have hre : s.re = -(n : ℝ) := by rw [h]; simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem ne_one_of_re_lt_one {s : ℂ} (hs : s.re < 1) : s ≠ 1 := by
  intro h
  rw [h] at hs
  simp at hs

/-- Functional-equation symmetry of the nontrivial zeros (Mathlib's
`riemannZeta_one_sub`). -/
theorem nontrivial_zero_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    is_nontrivial_zero (1 - ρ) := by
  obtain ⟨hz, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub (ne_neg_nat_of_re_pos h0) (ne_one_of_re_lt_one h1), hz, mul_zero]
  · rw [re_one_sub]; linarith
  · rw [re_one_sub]; linarith

theorem zetaZeros_stripSymmetric : StripSymmetric ZetaZeros :=
  ⟨fun _ h => ⟨h.2.1, h.2.2⟩, fun _ h => nontrivial_zero_reflect h⟩

-- ═══════════════════════════════════════════════════════
-- §5  CONSEQUENCES OF A ZERO-FREE RIGHT HALF-PLANE
-- ═══════════════════════════════════════════════════════

/-- `ζ` has no zeros with real part `> θ`. At `θ = 7/8` this is verbatim the
conclusion of `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`. -/
def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

theorem zetaZeros_right_bound {θ : ℝ} (h : ZeroFreeRightOf θ) :
    ∀ ρ ∈ ZetaZeros, ρ.re ≤ θ := by
  intro ρ hρ
  by_contra hlt
  exact h ρ (not_le.mp hlt) hρ.1

/-- The boundedness leg, sharpened: `|x| ≤ θ - 1/2` on the shifted spectrum. -/
theorem shifted_bounded_of_zeroFree {θ : ℝ} (h : ZeroFreeRightOf θ) :
    ∀ x ∈ ShiftedZeroSpectrum, |x| ≤ θ - 1/2 := by
  rw [shifted_eq]
  exact shifted_bound_of_right_bound zetaZeros_stripSymmetric (zetaZeros_right_bound h)

/-- The gap leg, with its threshold lowered from `1/2` to any `Δ > θ - 1/2`. -/
theorem strip_rh_of_gap {θ Δ : ℝ} (h : ZeroFreeRightOf θ) (hΔ : θ - 1/2 < Δ)
    (h_gap : SpectralGapProperty ShiftedZeroSpectrum Δ) :
    ∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2 := by
  rw [shifted_eq] at h_gap
  intro ρ hρ
  exact on_line_of_gap zetaZeros_stripSymmetric (zetaZeros_right_bound h) hΔ h_gap ρ hρ

/-- Conversely the strip form of RH gives the gap at every threshold. -/
theorem gap_of_strip_rh (h : ∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2) (Δ : ℝ) :
    SpectralGapProperty ShiftedZeroSpectrum Δ := by
  rw [shifted_eq]
  exact gap_of_on_line (fun ρ hρ => h ρ hρ) Δ

/-- **The remaining strip.** With `ζ` zero-free in `Re s > θ` (`θ < 1`):
all nontrivial zeros on the line ⟺ `ζ` zero-free in `1/2 < Re s ≤ θ`. -/
theorem strip_rh_iff_remaining_strip {θ : ℝ} (hθ : θ < 1) (h : ZeroFreeRightOf θ) :
    (∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2) ↔
      (∀ s : ℂ, 1/2 < s.re → s.re ≤ θ → riemannZeta s ≠ 0) := by
  constructor
  · intro hRH s h1 h2 hz
    have hs : is_nontrivial_zero s := ⟨hz, by linarith, by linarith⟩
    have := hRH s hs
    linarith
  · intro hfree
    have key := (on_line_iff_remaining_strip_empty zetaZeros_stripSymmetric
      (zetaZeros_right_bound h)).mpr
      (fun ρ hρ hstrip => hfree ρ hstrip.1 hstrip.2 hρ.1)
    exact fun ρ hρ => key ρ hρ

-- ═══════════════════════════════════════════════════════
-- §6  MATHLIB'S `RiemannHypothesis`
-- ═══════════════════════════════════════════════════════

/-- Mathlib's `RiemannHypothesis` implies the strip form (no hypothesis needed). -/
theorem strip_rh_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2 := by
  rintro ρ ⟨hz, h0, h1⟩
  refine hRH ρ hz ?_ (ne_one_of_re_lt_one h1)
  rintro ⟨n, hn⟩
  have hre : ρ.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- With `ζ` zero-free in `Re s > θ`, `θ < 1`: a zero of `ζ` that is not a
trivial zero lies in the open critical strip. (Functional equation + `Γ ≠ 0`
+ zeros of `cos`; the right half-plane is covered by the hypothesis itself,
so Mathlib's `Re s ≥ 1` nonvanishing theorem is not needed.) -/
theorem in_strip_of_nontrivial {θ : ℝ} (hθ : θ < 1) (h : ZeroFreeRightOf θ) {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  have hlt1 : s.re < 1 := by
    by_contra hge
    exact h s (by linarith [not_lt.mp hge]) hz
  refine ⟨?_, hlt1⟩
  by_contra hpos
  have hle : s.re ≤ 0 := not_lt.mp hpos
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  -- functional equation at t = 1 - s, where Re t ≥ 1
  have htre : 1 ≤ (1 - s).re := by rw [re_one_sub]; linarith
  have ht_neg : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) :=
    ne_neg_nat_of_re_pos (by linarith)
  have ht_one : (1 - s) ≠ 1 := fun h1 => hs0 (by linear_combination -h1)
  have hfe := riemannZeta_one_sub ht_neg ht_one
  have h1t : 1 - (1 - s) = s := by ring
  rw [h1t, hz] at hfe
  have hζt : riemannZeta (1 - s) ≠ 0 := h _ (by linarith)
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
    intro h0
    exact h2π ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζt)
      hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  -- π (1 - s) / 2 = (2k+1) π / 2  ⟹  s = -2k
  have hs_eq : s = -2 * (k : ℂ) := by
    have h2 : (Real.pi : ℂ) * (1 - s) = (2 * (k : ℂ) + 1) * Real.pi := by
      linear_combination 2 * hk
    have h3 : (Real.pi : ℂ) * (1 - s - (2 * (k : ℂ) + 1)) = 0 := by
      linear_combination h2
    have h4 : 1 - s - (2 * (k : ℂ) + 1) = 0 := (mul_eq_zero.mp h3).resolve_left hπ
    linear_combination -h4
  have hre : s.re = -2 * (k : ℝ) := by
    have := congrArg Complex.re hs_eq
    simpa using this
  -- Re s ≤ 0 and s ≠ 0 force k ≥ 1
  have hk1 : 1 ≤ k := by
    by_contra hk'
    have hk0 : k ≤ 0 := by omega
    have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have hkz : (k : ℝ) = 0 := by linarith
    have hk00 : k = 0 := by exact_mod_cast hkz
    apply hs0
    rw [hs_eq, hk00]; simp
  -- so s = -2 ((k-1) + 1) is a trivial zero
  apply htriv
  refine ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hcast
    simpa using this
  rw [hc, hs_eq]; ring

/-- Strip form ⟹ Mathlib's `RiemannHypothesis`, given a zero-free right half-plane. -/
theorem riemannHypothesis_of_strip_rh {θ : ℝ} (hθ : θ < 1) (h : ZeroFreeRightOf θ)
    (hs : ∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2) : RiemannHypothesis := by
  intro s hz htriv _
  exact hs s ⟨hz, in_strip_of_nontrivial hθ h hz htriv⟩

theorem riemannHypothesis_iff_strip_rh {θ : ℝ} (hθ : θ < 1) (h : ZeroFreeRightOf θ) :
    RiemannHypothesis ↔ ∀ ρ, is_nontrivial_zero ρ → ρ.re = 1/2 :=
  ⟨strip_rh_of_riemannHypothesis, riemannHypothesis_of_strip_rh hθ h⟩

-- ═══════════════════════════════════════════════════════
-- §7  θ = 7/8 :  THE STATEMENTS TO CITE
-- ═══════════════════════════════════════════════════════

/-
Discharging `h78`.  Inside the openai/math `lean/` tree the hypothesis is the
term

    fun s hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

and MNF_Bridge78_Unconditional.lean applies every theorem of this section to
it.  In this file it stays a hypothesis.
-/

/-- Under the 7/8 theorem the shifted zero spectrum lies in `[-3/8, 3/8]`. -/
theorem shifted_bounded_three_eighths (h78 : ZeroFreeRightOf (7/8)) :
    ∀ x ∈ ShiftedZeroSpectrum, |x| ≤ 3/8 := by
  intro x hx
  have := shifted_bounded_of_zeroFree h78 x hx
  norm_num at this ⊢
  exact this

/-- Under the 7/8 theorem every nontrivial zero lies in the closed strip
`1/8 ≤ Re s ≤ 7/8` (the right bound is the hypothesis; the left one is its
mirror image under `s ↦ 1 - s`). -/
theorem nontrivial_zero_re_mem (h78 : ZeroFreeRightOf (7/8)) {ρ : ℂ}
    (hρ : is_nontrivial_zero ρ) : 1/8 ≤ ρ.re ∧ ρ.re ≤ 7/8 := by
  have h1 := zetaZeros_right_bound h78 ρ hρ
  have h2 := zetaZeros_right_bound h78 (1 - ρ) (nontrivial_zero_reflect hρ)
  rw [re_one_sub] at h2
  constructor <;> linarith

/-- Under the 7/8 theorem, Mathlib's `RiemannHypothesis` is equivalent to the
MNF gap at ANY threshold `Δ > 3/8` (previously: `Δ = 1/2`). -/
theorem riemannHypothesis_iff_gap (h78 : ZeroFreeRightOf (7/8)) {Δ : ℝ} (hΔ : 3/8 < Δ) :
    RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ := by
  have hθ : (7/8 : ℝ) < 1 := by norm_num
  constructor
  · intro hRH
    exact gap_of_strip_rh (strip_rh_of_riemannHypothesis hRH) Δ
  · intro hgap
    exact riemannHypothesis_of_strip_rh hθ h78
      (strip_rh_of_gap h78 (by linarith) hgap)

/-- **What is left of RH after the 7/8 theorem**: exactly the statement that
`ζ` has no zeros in the strip `1/2 < Re s ≤ 7/8`. -/
theorem riemannHypothesis_iff_remaining_strip (h78 : ZeroFreeRightOf (7/8)) :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 7/8 → riemannZeta s ≠ 0 := by
  have hθ : (7/8 : ℝ) < 1 := by norm_num
  rw [riemannHypothesis_iff_strip_rh hθ h78]
  exact strip_rh_iff_remaining_strip hθ h78

/-- The ζ-zero set satisfies every hypothesis of the no-go of §3 (given the
7/8 theorem). So §3 applies to the actual situation: the facts recorded here
about `ZetaZeros` are also true of `Counter`, where the conclusion fails. -/
theorem zetaZeros_satisfies_structural_inputs (h78 : ZeroFreeRightOf (7/8)) :
    StripSymmetric ZetaZeros ∧ (∀ ρ ∈ ZetaZeros, ρ.re ≤ 7/8) :=
  ⟨zetaZeros_stripSymmetric, zetaZeros_right_bound h78⟩

-- ═══════════════════════════════════════════════════════
-- §8  EULER-TYPE NO-GO  (K3)
-- ═══════════════════════════════════════════════════════

theorem log_five_thirds_le : Real.log (5/3) ≤ 7/8 * Real.log 2 := by
  have h1 : Real.log ((5/3 : ℝ) ^ 8) ≤ Real.log ((2 : ℝ) ^ 7) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h1
  push_cast at h1
  linarith

theorem half_log_two_lt : 1/2 * Real.log 2 < Real.log (5/3) := by
  have h1 : Real.log (2 : ℝ) < Real.log ((5/3 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

theorem log_six_fifths_le : Real.log (6/5) ≤ 7/8 * Real.log 2 :=
  le_trans (Real.log_le_log (by norm_num) (by norm_num)) log_five_thirds_le

/-- The Dirichlet polynomial `Q(s) = 1 + (43/15)·2^{-s} + 2·4^{-s}`.
By hand (not formalised): `ζ(s)·Q(s)` is the Dirichlet series `Σ a(n) n^{-s}`
with `a = 1 * g`, `g` supported on `{1, 2, 4}`, so its coefficients are
multiplicative; it is `ζ` with the factor at `2` replaced by
`Q(s) / (1 - 2^{-s})`, which is not an Euler factor in the usual sense (it
has zeros). -/
noncomputable def twoFactor (s : ℂ) : ℂ :=
  1 + (43/15) * (2:ℂ) ^ (-s) + 2 * ((2:ℂ) ^ (-s)) ^ 2

theorem twoFactor_eq (s : ℂ) :
    twoFactor s = 2 * ((2:ℂ) ^ (-s) + 3/5) * ((2:ℂ) ^ (-s) + 5/6) := by
  unfold twoFactor; ring

/-- `‖2^{-s}‖ = exp (-(Re s) · log 2)`. -/
theorem norm_two_cpow_neg (s : ℂ) : ‖(2:ℂ) ^ (-s)‖ = Real.exp (-(s.re) * Real.log 2) := by
  have h2 : (2:ℂ) = ((2:ℝ) : ℂ) := by norm_num
  rw [h2, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1
  simp [mul_comm]

/-- If `2^{-s} = -c` with `c > 0` real, then `Re s · log 2 = -log c`. -/
theorem re_of_two_cpow_neg_eq {s : ℂ} {c : ℝ} (hc : 0 < c) (h : (2:ℂ) ^ (-s) = -(c : ℂ)) :
    s.re * Real.log 2 = -Real.log c := by
  have hn := norm_two_cpow_neg s
  rw [h, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc.le] at hn
  have := congrArg Real.log hn
  rw [Real.log_exp] at this
  linarith

/-- `Q` has no zeros in `Re s > 7/8`: its zeros have real part `log₂(5/3) ≈ 0.737`
or `log₂(6/5) ≈ 0.263`. -/
theorem twoFactor_ne_zero {s : ℂ} (hs : 7/8 < s.re) : twoFactor s ≠ 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [twoFactor_eq]
  intro h0
  rcases mul_eq_zero.mp h0 with h1 | h2
  · rcases mul_eq_zero.mp h1 with h | h
    · norm_num at h
    · have h' : (2:ℂ) ^ (-s) = -((3/5 : ℝ) : ℂ) := by
        push_cast; linear_combination h
      have hre := re_of_two_cpow_neg_eq (by norm_num : (0:ℝ) < 3/5) h'
      have hl : -Real.log (3/5 : ℝ) = Real.log (5/3) := by
        rw [← Real.log_inv]; norm_num
      have := log_five_thirds_le
      nlinarith
  · have h' : (2:ℂ) ^ (-s) = -((5/6 : ℝ) : ℂ) := by
      push_cast; linear_combination h2
    have hre := re_of_two_cpow_neg_eq (by norm_num : (0:ℝ) < 5/6) h'
    have hl : -Real.log (5/6 : ℝ) = Real.log (6/5) := by
      rw [← Real.log_inv]; norm_num
    have := log_six_fifths_le
    nlinarith

/-- An off-line zero of `Q`: `(log (5/3) + π i) / log 2`. -/
noncomputable def twoFactorZero : ℂ :=
  ((Real.log (5/3) : ℂ) + Real.pi * Complex.I) / (Real.log 2 : ℂ)

theorem twoFactorZero_re : twoFactorZero.re = Real.log (5/3) / Real.log 2 := by
  unfold twoFactorZero
  rw [Complex.div_ofReal_re]
  simp

theorem two_cpow_neg_twoFactorZero : (2:ℂ) ^ (-twoFactorZero) = -(3/5) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlog2c : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog2
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
  have hL : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hL]
  have harg : (Real.log 2 : ℂ) * (-twoFactorZero)
      = -(Real.log (5/3) : ℂ) + -(Real.pi * Complex.I) := by
    unfold twoFactorZero
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg (Real.pi * Complex.I), Complex.exp_pi_mul_I]
  have he : Complex.exp (-(Real.log (5/3) : ℂ)) = ((3/5 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [he]
  push_cast
  norm_num

theorem twoFactor_twoFactorZero : twoFactor twoFactorZero = 0 := by
  rw [twoFactor_eq, two_cpow_neg_twoFactorZero]; ring

/-- The zero sits inside the remaining strip: `1/2 < log₂(5/3) ≤ 7/8`. -/
theorem twoFactorZero_in_remaining_strip :
    1/2 < twoFactorZero.re ∧ twoFactorZero.re ≤ 7/8 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [twoFactorZero_re]
  constructor
  · rw [lt_div_iff₀ hlog2]; exact half_log_two_lt
  · rw [div_le_iff₀ hlog2]; exact log_five_thirds_le

/-- Functional equation of the factor: `Q(1-s) = 2^{2s-1} Q(s)`. Equivalently
`2^s · Q(s)` is invariant under `s ↦ 1 - s`, so with `ξ(s) = ξ(1-s)` the
completed function `2^s · ξ(s) · Q(s)` has the standard symmetric functional
equation. -/
theorem twoFactor_one_sub (s : ℂ) :
    twoFactor (1 - s) = (2:ℂ) ^ (2 * s - 1) * twoFactor s := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  have he : (2:ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => h2 h.1
  have e1 : (2:ℂ) ^ (-s) = ((2:ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
  have e2 : (2:ℂ) ^ (-(1 - s)) = (2:ℂ) ^ s / 2 := by
    have : -(1 - s) = s - 1 := by ring
    rw [this, Complex.cpow_sub _ _ h2, Complex.cpow_one]
  have e3 : (2:ℂ) ^ (2 * s - 1) = ((2:ℂ) ^ s) ^ 2 / 2 := by
    rw [Complex.cpow_sub _ _ h2, Complex.cpow_one]
    congr 1
    have : (2:ℂ) * s = ((2:ℕ) : ℂ) * s := by norm_num
    rw [this, Complex.cpow_nat_mul]
  unfold twoFactor
  rw [e2, e3, e1]
  field_simp
  ring

/-- Every zero of `Q` has real part `log₂(5/3)` or `log₂(6/5)`. -/
theorem twoFactor_zero_re {s : ℂ} (h0 : twoFactor s = 0) :
    s.re = Real.log (5/3) / Real.log 2 ∨ s.re = Real.log (6/5) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [twoFactor_eq] at h0
  rcases mul_eq_zero.mp h0 with h1 | h2
  · rcases mul_eq_zero.mp h1 with h | h
    · norm_num at h
    · left
      have h' : (2:ℂ) ^ (-s) = -((3/5 : ℝ) : ℂ) := by push_cast; linear_combination h
      have hre := re_of_two_cpow_neg_eq (by norm_num : (0:ℝ) < 3/5) h'
      have hl : -Real.log (3/5 : ℝ) = Real.log (5/3) := by rw [← Real.log_inv]; norm_num
      rw [eq_div_iff hlog2.ne']; linarith
  · right
    have h' : (2:ℂ) ^ (-s) = -((5/6 : ℝ) : ℂ) := by push_cast; linear_combination h2
    have hre := re_of_two_cpow_neg_eq (by norm_num : (0:ℝ) < 5/6) h'
    have hl : -Real.log (5/6 : ℝ) = Real.log (6/5) := by rw [← Real.log_inv]; norm_num
    rw [eq_div_iff hlog2.ne']; linarith

/-- **Completed functional equation for `F = ζ·Q`.** With `Λ` Mathlib's
`completedRiemannZeta` (`π^{-s/2} Γ(s/2) ζ(s)`), the function
`2^s · Λ(s) · Q(s)` is invariant under `s ↦ 1 - s`. -/
theorem completed_twoFactor_symm (s : ℂ) :
    (2:ℂ) ^ (1 - s) * completedRiemannZeta (1 - s) * twoFactor (1 - s)
      = (2:ℂ) ^ s * completedRiemannZeta s * twoFactor s := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  have hpow : (2:ℂ) ^ (1 - s) * (2:ℂ) ^ (2 * s - 1) = (2:ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ h2]; congr 1; ring
  rw [completedRiemannZeta_one_sub, twoFactor_one_sub]
  calc (2:ℂ) ^ (1 - s) * completedRiemannZeta s * ((2:ℂ) ^ (2 * s - 1) * twoFactor s)
      = ((2:ℂ) ^ (1 - s) * (2:ℂ) ^ (2 * s - 1)) * completedRiemannZeta s * twoFactor s := by
        ring
    _ = (2:ℂ) ^ s * completedRiemannZeta s * twoFactor s := by rw [hpow]

/-- **EULER-TYPE NO-GO (K3).** For `F(s) = ζ(s) · Q(s)`:
* in `Re s > 7/8` the zeros of `F` are exactly the zeros of `ζ`
  (so `F` satisfies the 7/8 bound iff `ζ` does);
* `F` has a zero with `1/2 < Re s ≤ 7/8` (at `Re s = log₂(5/3)`);
* the factor `Q` has the functional equation `Q(1-s) = 2^{2s-1} Q(s)`
  (see `completed_twoFactor_symm` for the completed form).
Together with multiplicativity of the coefficients of `F` (by hand, see
`twoFactor`): multiplicative coefficients, a functional equation and the 7/8
bound do not force the line. The off-line zeros of `F` are the zeros of its
altered factor at `2`, so this does not test arguments that use the
non-vanishing of every local factor. -/
theorem euler_type_no_go :
    (∀ s : ℂ, 7/8 < s.re → (riemannZeta s * twoFactor s = 0 ↔ riemannZeta s = 0)) ∧
    (∃ s : ℂ, 1/2 < s.re ∧ s.re ≤ 7/8 ∧ riemannZeta s * twoFactor s = 0) ∧
    (∀ s : ℂ, twoFactor (1 - s) = (2:ℂ) ^ (2 * s - 1) * twoFactor s) := by
  refine ⟨fun s hs => ⟨fun h => ?_, fun h => ?_⟩,
    ⟨twoFactorZero, twoFactorZero_in_remaining_strip.1, twoFactorZero_in_remaining_strip.2, ?_⟩,
    twoFactor_one_sub⟩
  · exact (mul_eq_zero.mp h).resolve_right (twoFactor_ne_zero hs)
  · rw [h, zero_mul]
  · rw [twoFactor_twoFactorZero, mul_zero]

/-- Under the 7/8 theorem, `F = ζ · Q` is itself zero-free in `Re s > 7/8`,
yet vanishes inside the remaining strip. -/
theorem euler_type_no_go_under_h78 (h78 : ZeroFreeRightOf (7/8)) :
    (∀ s : ℂ, 7/8 < s.re → riemannZeta s * twoFactor s ≠ 0) ∧
    (∃ s : ℂ, 1/2 < s.re ∧ s.re ≤ 7/8 ∧ riemannZeta s * twoFactor s = 0) :=
  ⟨fun s hs => mul_ne_zero (h78 s hs) (twoFactor_ne_zero hs), euler_type_no_go.2.1⟩

end MNF.Bridge78

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.Bridge78.tau_threshold
#print axioms MNF.Bridge78.structural_inputs_insufficient
#print axioms MNF.Bridge78.structural_inputs_do_not_give_gap
#print axioms MNF.Bridge78.analytic_no_go
#print axioms MNF.Bridge78.nontrivial_zero_reflect
#print axioms MNF.Bridge78.in_strip_of_nontrivial
#print axioms MNF.Bridge78.nontrivial_zero_re_mem
#print axioms MNF.Bridge78.shifted_bounded_three_eighths
#print axioms MNF.Bridge78.riemannHypothesis_iff_gap
#print axioms MNF.Bridge78.riemannHypothesis_iff_remaining_strip
#print axioms MNF.Bridge78.euler_type_no_go
#print axioms MNF.Bridge78.completed_twoFactor_symm
#print axioms MNF.Bridge78.twoFactor_zero_re
#print axioms MNF.Bridge78.euler_type_no_go_under_h78
