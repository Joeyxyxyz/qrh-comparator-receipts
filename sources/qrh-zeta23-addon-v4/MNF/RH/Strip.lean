/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — THE STRIP  (MNF/RH/Strip.lean)
[BOOKKEEPING] the band around the line under N, E and injection; what distinguishes a true zero
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree, on top of MNF/RH/Density.lean and the kernel-checked
injection/ejection algebra MNF/Extension/InjectionEjection.lean (56 theorems; its own header
records the pin at which Comparator accepted it, Lean v4.34.1 / Mathlib d13f23b7; it compiles
here at the zeta23 pin).

The question this file answers formally: in shifted coordinates x = Re ρ − 1/2, the open band
|x| < Δ is the Δ-reservoir plus the point 0.  Can the band hold "injected zeros" — values whose
nullification reading is 0 although their content is not — and how is a TRUE zero (x = 0, the
zero on the line) told apart from them?  The answer below is: only by the trace δ*, which needs
the reading at every threshold; at any single threshold they are indistinguishable
(`band_injection_blind`).

  §1  MNF.RH's `nullify` and the algebra's `nullify` are the same operator (`nullify_eq_extension`).
  §2  The band and the true zero.  Inside the band, E fixes a point iff it is 0
      (`eject_fixed_iff_zero`); every other band point is sent by the operator E to ±Δ
      (`eject_band_edge`): "everything ejects away from 0" describes the values of E and
      nothing about the zeros.  Globally, 0 is the only real
      that is gapped at every threshold, fixed by E at every threshold, and nullified at every
      threshold (`eq_zero_iff_gapped_all`, `eq_zero_iff_eject_fixed_all`,
      `eq_zero_iff_nullified_all`).  The last one is the trivial criterion x = 0 ↔ ∀ Δ > 0,
      |x| < Δ, which is what the nickname "st()" refers to; no nonstandard object is involved.
  §3  Injection into the band.  Any displacement can be fragmented until its reading at Δ is 0
      (`displacement_injectable`); the reading of an injected x is the reading of x at the
      dilated threshold kΔ (`injected_reads_zero_iff`).  READINGS ARE BLIND IN THE BAND: every
      band point, split into any number k ≥ 1 of equal pieces (`inject x k`), reads 0
      (`band_injection_blind`; unequal splittings are not covered: Δ = 1, x = 0.1, the
      representation [5, −4.9] reads 0.1).  What is not blind:
      the trace δ* of the exact representation, which is |x| (`trace_singleton`, `trace_zero`),
      and the trace of an injected zero, which decays like |x|/k but never vanishes
      (`trace_inject_pos`, `trace_inject_tendsto`).
  §4  On the spectrum.  For any ρ : ℂ (zero or not), Re ρ = 1/2 is equivalent to each of: its
      displacement is fixed by E at every threshold, is nullified at every threshold, has
      trace 0 (`on_line_iff_eject_fixed_all`, `on_line_iff_nullified_all`,
      `on_line_iff_trace_zero`).  Each is x = 0 in other words; none is a criterion checkable
      at finitely many thresholds, which is why the "∀ Δ" is the whole difficulty.
  §5  What the gap says in these words: under `SpectralGapHyp Δ` no nontrivial zero has its
      displacement in the Δ-band other than 0 (`band_trivial_of_gap`, with its converse
      `gap_of_band_trivial`: this is the definition of the gap restated in band language, and it
      says nothing about the `inject` operator of §3).  The same hypothesis is what
      `onLineDensityOne_of_reservoir_of_gap` (Density.lean) uses, through `NNear_eq_N0_of_gap`,
      to turn the δ = Δ instance of `ReservoirDensityOne` into `OnLineDensityOne`.

What this file does NOT do.  It proves no analytic fact about ζ.  It does not decide whether
any band is injected into: that is `SpectralGapHyp Δ`, which for Δ ≥ 1/2 is RH and for
0 < Δ < 1/2 is an open zero-free strip.  The criteria of §4 quantify over every threshold; the
"∀ Δ" is where the whole difficulty sits, and the file makes that visible rather than removing it.
-/
import MNF.RH.Density
import MNF.Extension.InjectionEjection

namespace MNF.RH

open Complex Set
open MNF.Extension (eject Gapped inject content nu deltaStar kstar)

/-! ### §1 One operator -/

/-- MNF.RH's nullification (Gap.lean) and the algebra's (InjectionEjection.lean) agree. -/
theorem nullify_eq_extension (Δ x : ℝ) : nullify Δ x = MNF.Extension.nullify Δ x := by
  unfold nullify MNF.Extension.nullify
  by_cases h : Δ ≤ |x| <;> simp [h]

/-! ### §2 The band and the true zero -/

/-- The open Δ-band around the line, in shifted coordinates: |x| < Δ.  Its points other than 0
form the Δ-reservoir. -/
def Band (Δ : ℝ) : Set ℝ := {x | |x| < Δ}

/-- The band is exactly where N(Δ,·) reads 0. -/
theorem mem_Band_iff_nullified {Δ x : ℝ} (hΔ : 0 < Δ) : x ∈ Band Δ ↔ nullify Δ x = 0 :=
  (nullify_eq_zero_iff hΔ x).symm

/-- **Inside the band, E fixes a point iff it is the true zero.** -/
theorem eject_fixed_iff_zero {Δ x : ℝ} (hΔ : 0 < Δ) (hx : x ∈ Band Δ) :
    eject Δ x = x ↔ x = 0 := by
  constructor
  · intro hfix
    by_contra h0
    have hlt : |x| < Δ := hx
    have hE : eject Δ x = (if 0 < x then Δ else -Δ) := by
      unfold MNF.Extension.eject
      rw [if_neg h0, if_neg (not_le.mpr hlt)]
    rw [hE] at hfix
    by_cases hpos : 0 < x
    · rw [if_pos hpos] at hfix
      rw [← hfix, abs_of_pos hΔ] at hlt
      exact lt_irrefl _ hlt
    · rw [if_neg hpos] at hfix
      rw [← hfix, abs_neg, abs_of_pos hΔ] at hlt
      exact lt_irrefl _ hlt
  · rintro rfl
    simp [MNF.Extension.eject]

/-- **Everything else in the band ejects to its edge**: |E(Δ,x)| = Δ for 0 < |x| < Δ. -/
theorem eject_band_edge {Δ x : ℝ} (hΔ : 0 < Δ) (hx : x ∈ Band Δ) (h0 : x ≠ 0) :
    |eject Δ x| = Δ := by
  have hlt : |x| < Δ := hx
  unfold MNF.Extension.eject
  rw [if_neg h0, if_neg (not_le.mpr hlt)]
  split_ifs <;> simp [abs_of_pos hΔ]

/-- 0 is the only real that is gapped at every threshold. -/
theorem eq_zero_iff_gapped_all (x : ℝ) : x = 0 ↔ ∀ Δ > 0, Gapped Δ x := by
  constructor
  · rintro rfl Δ _
    exact Or.inl rfl
  · intro h
    by_contra h0
    have hpos : 0 < |x| := abs_pos.mpr h0
    rcases h (2 * |x|) (by positivity) with h1 | h1
    · exact h0 h1
    · linarith

/-- 0 is the only real fixed by E at every threshold. -/
theorem eq_zero_iff_eject_fixed_all (x : ℝ) : x = 0 ↔ ∀ Δ > 0, eject Δ x = x := by
  rw [eq_zero_iff_gapped_all]
  constructor
  · intro h Δ hΔ
    exact MNF.Extension.aux_eject_idem_1 Δ x (h Δ hΔ)
  · intro h Δ hΔ
    have hg := MNF.Extension.eject_gapped Δ hΔ x
    rwa [h Δ hΔ] at hg

/-- 0 is the only real nullified at every threshold: the st()-criterion in standard words. -/
theorem eq_zero_iff_nullified_all (x : ℝ) : x = 0 ↔ ∀ Δ > 0, nullify Δ x = 0 := by
  constructor
  · rintro rfl Δ hΔ
    exact (nullify_eq_zero_iff hΔ 0).mpr (by simpa using hΔ)
  · intro h
    by_contra h0
    have hpos : 0 < |x| := abs_pos.mpr h0
    have := (nullify_eq_zero_iff hpos x).mp (h |x| hpos)
    exact lt_irrefl _ this

/-! ### §3 Injection into the band -/

/-- **Injected zeros exist**: any displacement x, fragmented into k* equal pieces, keeps its
content and reads 0 at threshold Δ. -/
theorem displacement_injectable (Δ x : ℝ) (hΔ : 0 < Δ) :
    ∃ k : ℕ, 0 < k ∧ content (inject x k) = x ∧ nu Δ (inject x k) = 0 :=
  ⟨kstar Δ x, Nat.succ_pos _, MNF.Extension.content_inject x _ (Nat.succ_pos _),
    MNF.Extension.inject_at_kstar Δ x hΔ⟩

/-- The reading of an injected displacement is its reading at the dilated threshold kΔ:
it is 0 iff |x| < kΔ. -/
theorem injected_reads_zero_iff {Δ x : ℝ} (hΔ : 0 < Δ) {k : ℕ} (hk : 0 < k) :
    nu Δ (inject x k) = 0 ↔ |x| < k * Δ := by
  rw [MNF.Extension.nu_inject Δ x k hk, ← nullify_eq_extension]
  exact nullify_eq_zero_iff (mul_pos (by exact_mod_cast hk) hΔ) x

/-- **Readings are blind in the band**: every band point, split into k ≥ 1 equal pieces, reads
0 at Δ — so a reading of 0 at Δ cannot tell a true zero from an injected one.  (Unequal
splittings are not covered.) -/
theorem band_injection_blind {Δ x : ℝ} (hΔ : 0 < Δ) (hx : x ∈ Band Δ) {k : ℕ} (hk : 0 < k) :
    nu Δ (inject x k) = 0 := by
  rw [injected_reads_zero_iff hΔ hk]
  have hlt : |x| < Δ := hx
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- The trace of the exact representation of x ≠ 0 is its distance from the line. -/
theorem trace_singleton (x : ℝ) (hx : x ≠ 0) : deltaStar [x] = |x| :=
  MNF.Extension.deltaStar_singleton x hx

/-- The trace of the true zero is 0 (no rung reads anything; `sSup ∅ = 0`). -/
theorem trace_zero : deltaStar [(0 : ℝ)] = 0 := by
  unfold MNF.Extension.deltaStar
  have h : {Δ : ℝ | 0 < Δ ∧ nu Δ [(0 : ℝ)] ≠ 0} = ∅ := by
    ext Δ
    simp [MNF.Extension.nu, MNF.Extension.nullify]
  rw [h, Real.sSup_empty]

/-- **Injected zeros decay but do not vanish**: the trace of the k-fold fragmentation of
x ≠ 0 is |x|/k > 0. -/
theorem trace_inject_pos {x : ℝ} (hx : x ≠ 0) {k : ℕ} (hk : 0 < k) :
    0 < deltaStar (inject x k) := by
  rw [MNF.Extension.deltaStar_inject x hx k hk]
  exact div_pos (abs_pos.mpr hx) (by exact_mod_cast hk)

/-- ...and tends to 0 with the fragmentation depth: finer injection hides an off-line zero at
ever finer rungs, never at all rungs. -/
theorem trace_inject_tendsto {x : ℝ} (hx : x ≠ 0) :
    Filter.Tendsto (fun k : ℕ => deltaStar (inject x k)) Filter.atTop (nhds 0) := by
  have h : (fun k : ℕ => deltaStar (inject x k)) =ᶠ[Filter.atTop] fun k : ℕ => |x| / k := by
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    exact MNF.Extension.deltaStar_inject x hx k hk
  rw [Filter.tendsto_congr' h]
  exact tendsto_const_div_atTop_nhds_zero_nat |x|

/-! ### §4 On the spectrum -/

/-- Re ρ = 1/2 iff the displacement is fixed by E at every threshold (x = 0 in other words). -/
theorem on_line_iff_eject_fixed_all (ρ : ℂ) :
    ρ.re = 1 / 2 ↔ ∀ Δ > 0, eject Δ (ρ.re - 1 / 2) = ρ.re - 1 / 2 := by
  rw [← eq_zero_iff_eject_fixed_all]
  constructor <;> intro h <;> linarith

/-- Re ρ = 1/2 iff the displacement is nullified at every threshold (x = 0 in other words). -/
theorem on_line_iff_nullified_all (ρ : ℂ) :
    ρ.re = 1 / 2 ↔ ∀ Δ > 0, nullify Δ (ρ.re - 1 / 2) = 0 := by
  rw [← eq_zero_iff_nullified_all]
  constructor <;> intro h <;> linarith

/-- Re ρ = 1/2 iff the trace of the displacement is 0 (x = 0 in other words). -/
theorem on_line_iff_trace_zero (ρ : ℂ) : ρ.re = 1 / 2 ↔ deltaStar [ρ.re - 1 / 2] = 0 := by
  constructor
  · intro h
    rw [show ρ.re - 1 / 2 = 0 by linarith]
    exact trace_zero
  · intro h
    by_contra hne
    have hx : ρ.re - 1 / 2 ≠ 0 := fun h' => hne (by linarith)
    rw [trace_singleton _ hx] at h
    exact hx (abs_eq_zero.mp h)

/-! ### §5 The gap in these words -/

/-- **Under a gap at Δ, the only zero displacement in the Δ-band is 0** (a restatement of
`SpectralGapHyp Δ`): a nontrivial zero whose displacement lies in the band is on the line. -/
theorem band_trivial_of_gap {Δ : ℝ} (hgap : SpectralGapHyp Δ) (ρ : ℂ)
    (hρ : is_nontrivial_zero ρ) (hx : ρ.re - 1 / 2 ∈ Band Δ) : ρ.re = 1 / 2 := by
  rcases hgap (ρ.re - 1 / 2) ⟨ρ, hρ, rfl⟩ with h0 | hge
  · linarith
  · have hlt : |ρ.re - 1 / 2| < Δ := hx
    linarith

/-- Conversely, if every zero displacement in the Δ-band is 0, there is a gap at Δ; with the
previous theorem this is `SpectralGapHyp Δ` rewritten in band language. -/
theorem gap_of_band_trivial {Δ : ℝ}
    (h : ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re - 1 / 2 ∈ Band Δ → ρ.re = 1 / 2) :
    SpectralGapHyp Δ := by
  rintro x ⟨ρ, hρ, rfl⟩
  by_cases hb : ρ.re - 1 / 2 ∈ Band Δ
  · left
    linarith [h ρ hρ hb]
  · right
    have : ¬ |ρ.re - 1 / 2| < Δ := hb
    exact not_lt.mp this

end MNF.RH
