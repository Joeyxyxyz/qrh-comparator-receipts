/-
MNF_Injection_Ejection.lean — injection, ejection, cascades, residues and soft gates
for the Messina Nullification Framework.

STATUS: VERIFIED 2026-11-03 on Joey's Ubuntu laptop (ComparaJuan). The sketch as received
(MNF_Injection_Ejection_sketch_as_received.lean) elaborated with zero errors at the pin below:
all 31 definitions, and every one of its 18 attempted proofs closed as written. Its 38 `sorry`
proofs were then filled by Claude Code (eight prover agents, statements untouched, 13 helper
lemmas named aux_*), and the whole file was re-checked: zero errors, zero sorry; each of the 56
theorems depends on exactly [propext, Classical.choice, Quot.sound] (audit.out); Comparator
d03acab1 accepted all 56 against a mirror challenge with every definition compared by body,
Lean kernel and NanoDa (comparator-precheck.log). The docstrings' "Intended proof" notes are
the sketch author's; the proofs below are the checked ones.

Tags in docstrings:
  [CORPUS]   copied from Joey's corpus (Nullification_Core.lean, MNFmeetsDavisSet4.lean,
             Batch4_2, Batch17, output56); the corpus files import nothing from each other,
             so the core is re-declared here to keep the file self-contained.
  [PROPOSED] introduced in the 2026-11 exploration (mnf2_formal/catalogue.md §3.2,
             mnf2_algebra/algebra.md §3–§8, mnf2_lab/results.md §3) and synthesised in
             mnf2_synth/MNF_beyond_projection.md.  Every [PROPOSED] theorem is exercised by
             the numpy property tests in mnf2_algebra/mnf_ops.py (seeds 0, 7, 123; all pass).

Environment used (the handoff named Lean v4.24.0 / Mathlib f897ebcf; this session's pinned
tree is newer, and the file was not tried at the older pin):
  leanprover/lean4:v4.34.1, Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612.
Uses `Real`, `abs`, `max`, `min`, `List.sum/map/replicate/flatMap/any`, `Nat.floor`, `sSup`,
`Nat.iterate`, `Fin n → ℝ`, `Matrix.vecCons`, `Real.rpow`, `decide` and order lemmas.
-/

import Mathlib

open Real
open scoped Classical   -- Prop-valued `if` (e.g. on `IsReservoir`) needs a Decidable instance; added after the adversarial check

noncomputable section
namespace MNF.Extension

/-! ## §0  Corpus core, copied verbatim  [CORPUS] -/

/-- [CORPUS] Nullification_Core.lean: keep at or above threshold, kill below. -/
def nullify (Δ : ℝ) (x : ℝ) : ℝ := if |x| ≥ Δ then x else 0

/-- [CORPUS] Nullification_Core.lean: the remainder. -/
def remainder (Δ : ℝ) (x : ℝ) : ℝ := x - nullify Δ x

/-- [CORPUS] MNFmeetsDavisSet4.lean / wormhole_4: the probes. -/
def NorthProbe (Δ : ℝ) (x : ℝ) : ℝ := x - Δ / 2
def SouthProbe (Δ : ℝ) (x : ℝ) : ℝ := -(x - Δ / 2)

/-- [CORPUS] MNFmeetsDavisSet4.lean:92 — ejection is a boundary predicate, never used in a theorem there. -/
def IsEjectionThreshold (Δ : ℝ) (x : ℝ) : Prop := x = Δ

/-- [CORPUS-equivalent] the signed reservoir [±0.0e]: nonzero and strictly inside the gap. -/
def IsReservoir (Δ : ℝ) (x : ℝ) : Prop := x ≠ 0 ∧ |x| < Δ

/-- [PROPOSED name for a corpus object] the gapped set G_Δ = range (nullify Δ) (corpus `spectral_gap`). -/
def Gapped (Δ : ℝ) (x : ℝ) : Prop := x = 0 ∨ Δ ≤ |x|

/-- [CORPUS] conservation N + R = id (proof copied from Nullification_Core.lean). -/
theorem conservation (Δ : ℝ) (x : ℝ) : nullify Δ x + remainder Δ x = x := by
  simp only [remainder, add_sub_cancel]

/-- [PROPOSED strengthening] idempotence holds for every Δ; the corpus copies all carry a
superfluous hypothesis `0 ≤ Δ` (catalogue §4.9).  Intended proof: unfold and case-split; in the
`else` branch the inner argument is 0 and both inner branches return 0. -/
theorem idempotent' (Δ : ℝ) (x : ℝ) : nullify Δ (nullify Δ x) = nullify Δ x := by
  unfold nullify
  split_ifs <;> simp_all

/-! ## §1  Two laws the corpus states nowhere  [PROPOSED] -/

/-- [PROPOSED] Dilation covariance ("only x/Δ matters").  Absent from the 301 files: the only
"scale invariance" theorem, `same_wall_scale_invariance`, concludes `True`.
Intended proof: |c·x| = c·|x| for c > 0 and c·Δ ≤ c·|x| ↔ Δ ≤ |x|. -/
theorem dilation_covariance (Δ x c : ℝ) (hc : 0 < c) :
    nullify (c * Δ) (c * x) = c * nullify Δ x := by
  unfold nullify
  rw [abs_mul, abs_of_pos hc]
  by_cases h : Δ ≤ |x|
  · rw [if_pos (mul_le_mul_of_nonneg_left h hc.le), if_pos h]
  · rw [if_neg (fun h' => h (le_of_mul_le_mul_left h' hc)), if_neg h, mul_zero]

/-- [PROPOSED] The correct two-sided Δ-monotonicity.  The corpus proves `threshold_monotone`
(N Δ₂ x ≤ N Δ₁ x) on ℕ only; on ℝ that statement is false for x < 0 (x = −1, Δ₁ = ½, Δ₂ = 2).
Intended proof: case split; the only non-trivial case Δ₂ ≤ |x| ∧ ¬(Δ₁ ≤ |x|) contradicts h. -/
theorem abs_nullify_antitone_in_threshold (Δ₁ Δ₂ x : ℝ) (h : Δ₁ ≤ Δ₂) :
    |nullify Δ₂ x| ≤ |nullify Δ₁ x| := by
  unfold nullify
  split_ifs with h₂ h₁ h₁
  · exact le_refl _
  · exact absurd (le_trans h h₂) h₁
  · simp
  · simp

/-! ## §2  Ejection as an operator, and the deficit that generates the algebra  [PROPOSED] -/

/-- [PROPOSED] Ejection operator E(Δ,x) = sgn(x)·max(|x|,Δ), E(Δ,0) = 0: identity on the gapped
set, lifts the reservoir to the threshold.  Written without `Real.sign` to keep the cases explicit. -/
def eject (Δ : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else if Δ ≤ |x| then x else if 0 < x then Δ else -Δ

/-- [PROPOSED] Ejection deficit J = E − id: (Δ − |x|)·sgn x on the reservoir, 0 elsewhere. -/
def deficit (Δ : ℝ) (x : ℝ) : ℝ := eject Δ x - x

/-- [PROPOSED] range(E) ⊆ G_Δ.  Intended: case split; reservoir branch gives |±Δ| = Δ. -/
theorem eject_gapped (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : Gapped Δ (eject Δ x) := by
  unfold Gapped eject
  split_ifs with h0 h1 h2
  · left; rfl
  · right; exact h1
  · right; rw [abs_of_pos hΔ]
  · right; rw [abs_neg, abs_of_pos hΔ]

/-- [PROPOSED] E is idempotent. -/
theorem aux_eject_idem_1 (Δ : ℝ) (y : ℝ) (h : Gapped Δ y) : eject Δ y = y := by
  rcases h with rfl | h
  · simp [eject]
  · unfold eject
    split_ifs <;> simp_all

theorem eject_idem (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : eject Δ (eject Δ x) = eject Δ x :=
  aux_eject_idem_1 Δ _ (eject_gapped Δ hΔ x)

/-- [PROPOSED] N ∘ E = E (N fixes the gapped set). -/
theorem aux_nullify_eject_1 (Δ : ℝ) (y : ℝ) (h : Gapped Δ y) : nullify Δ y = y := by
  rcases h with rfl | h
  · simp [nullify]
  · unfold nullify
    rw [if_pos h]

theorem nullify_eject (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : nullify Δ (eject Δ x) = eject Δ x :=
  aux_nullify_eject_1 Δ _ (eject_gapped Δ hΔ x)

/-- [PROPOSED] E ∘ N = N (E fixes the gapped set). -/
theorem aux_eject_nullify_1 (Δ : ℝ) (x : ℝ) : Gapped Δ (nullify Δ x) := by
  unfold Gapped nullify
  split_ifs with h
  · right; exact h
  · left; rfl

theorem eject_nullify (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : eject Δ (nullify Δ x) = nullify Δ x :=
  aux_eject_idem_1 Δ _ (aux_eject_nullify_1 Δ x)

/-- [PROPOSED] R ∘ E = 0. -/
theorem remainder_eject (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : remainder Δ (eject Δ x) = 0 := by
  unfold remainder
  rw [nullify_eject Δ hΔ x, sub_self]

/-- [PROPOSED] Gap jump: E − N = Δ·sgn(x) on the reservoir and 0 on the gapped set. -/
theorem eject_sub_nullify (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    eject Δ x - nullify Δ x = if IsReservoir Δ x then (if 0 < x then Δ else -Δ) else 0 := by
  by_cases h0 : x = 0
  · subst h0; simp [eject, nullify, IsReservoir, not_le.mpr hΔ]
  · by_cases h : Δ ≤ |x|
    · simp [eject, nullify, IsReservoir, h0, h, not_lt.mpr h]
    · simp [eject, nullify, IsReservoir, h0, h, not_le.mp h]

/-- [PROPOSED] The corpus ejection predicate becomes an identity: for every positive-reservoir
value, E lands exactly on the ejection threshold and the probe reads Δ/2
(corpus `ejection_probe_reading : NorthProbe Δ Δ = Δ/2`). -/
theorem eject_probe_reading (Δ : ℝ) (x : ℝ) (hx : 0 < x) (hxΔ : x < Δ) :
    IsEjectionThreshold Δ (eject Δ x) ∧ NorthProbe Δ (eject Δ x) = Δ / 2 := by
  have hne : x ≠ 0 := ne_of_gt hx
  have habs : ¬ (Δ ≤ |x|) := by rw [abs_of_pos hx]; exact not_le.mpr hxΔ
  have hE : eject Δ x = Δ := by simp [eject, hne, habs, hx]
  refine ⟨?_, ?_⟩
  · simpa [IsEjectionThreshold] using hE
  · rw [NorthProbe, hE]; ring

/-- [PROPOSED] Dilation covariance of E. -/
theorem eject_dilation (Δ x c : ℝ) (hc : 0 < c) : eject (c * Δ) (c * x) = c * eject Δ x := by
  unfold eject
  have hcx : c * x = 0 ↔ x = 0 := by simp [hc.ne']
  have h1 : c * Δ ≤ |c * x| ↔ Δ ≤ |x| := by
    rw [abs_mul, abs_of_pos hc]
    constructor
    · intro h; exact le_of_mul_le_mul_left h hc
    · intro h; exact mul_le_mul_of_nonneg_left h hc.le
  have h2 : 0 < c * x ↔ 0 < x := by
    constructor
    · intro h; nlinarith
    · intro h; exact mul_pos hc h
  simp only [hcx, h1, h2]
  split_ifs <;> ring

/-- [PROPOSED] Threshold semilattice for N: N_a ∘ N_b = N_{max a b}.  No positivity needed.
Intended: case split on |x| against a and b; the branch b ≤ |x| < a gives N_a x = 0 = N_{max} x. -/
theorem nullify_comp_nullify (a b x : ℝ) : nullify a (nullify b x) = nullify (max a b) x := by
  simp only [nullify, ge_iff_le]
  by_cases hb : b ≤ |x|
  · rw [if_pos hb]
    by_cases ha : a ≤ |x|
    · rw [if_pos ha, if_pos (max_le ha hb)]
    · rw [if_neg ha, if_neg (fun h => ha (le_trans (le_max_left a b) h))]
  · rw [if_neg hb, if_neg (fun h => hb (le_trans (le_max_right a b) h))]
    simp

/-- [PROPOSED] Threshold semilattice for E: E_a ∘ E_b = E_{max a b}. -/
theorem eject_comp_eject (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    eject a (eject b x) = eject (max a b) x := by
  by_cases h0 : x = 0
  · subst h0; simp [eject]
  · by_cases hbx : b ≤ |x|
    · have hEb : eject b x = x := by simp [eject, h0, hbx]
      rw [hEb]
      by_cases hax : a ≤ |x|
      · simp [eject, h0, hax, max_le hax hbx]
      · have hmax : max a b = a := max_eq_left (le_trans hbx (not_le.mp hax).le)
        rw [hmax]
    · have hm : ¬ max a b ≤ |x| := fun h => hbx (le_trans (le_max_right a b) h)
      by_cases hx : 0 < x
      · have hEb : eject b x = b := by simp [eject, h0, hbx, hx]
        rw [hEb]
        simp only [eject, if_neg hb.ne', abs_of_pos hb, if_pos hb, if_neg h0, if_neg hm, if_pos hx]
        exact (max_def a b).symm
      · have hEb : eject b x = -b := by simp [eject, h0, hbx, hx]
        rw [hEb]
        have hnb : -b ≠ 0 := by linarith
        have hnb' : ¬ 0 < -b := by linarith
        simp only [eject, if_neg hnb, abs_neg, abs_of_pos hb, if_neg hnb', if_neg h0, if_neg hm,
          if_neg hx]
        rw [max_def]
        split_ifs <;> ring

/-- [PROPOSED] N is the right adjoint of the inclusion of the gapped set on [0,∞) ("floor"):
g ≤ x ↔ g ≤ N x for gapped g ≥ 0.  Intended: if Δ ≤ x then N x = x; else g ≤ x < Δ forces g = 0. -/
theorem nullify_floor (Δ : ℝ) (hΔ : 0 < Δ) (g x : ℝ) (hg : Gapped Δ g) (hg0 : 0 ≤ g) (hx : 0 ≤ x) :
    g ≤ x ↔ g ≤ nullify Δ x := by
  unfold nullify
  rw [abs_of_nonneg hx]
  split_ifs with h
  · exact Iff.rfl
  · constructor
    · intro hgx
      rcases hg with rfl | hΔg
      · exact le_refl 0
      · rw [abs_of_nonneg hg0] at hΔg
        exact absurd (lt_of_lt_of_le (not_le.mp h) (le_trans hΔg hgx)) (lt_irrefl _)
    · intro hg'; exact le_trans hg' hx

/-- [PROPOSED] E is the left adjoint of the inclusion on [0,∞) ("ceiling"): x ≤ g ↔ E x ≤ g.
Intended: x = 0 trivial; 0 < x < Δ: g ≥ x > 0 gapped forces g ≥ Δ = E x; Δ ≤ x: E x = x. -/
theorem eject_ceiling (Δ : ℝ) (hΔ : 0 < Δ) (g x : ℝ) (hg : Gapped Δ g) (hg0 : 0 ≤ g) (hx : 0 ≤ x) :
    x ≤ g ↔ eject Δ x ≤ g := by
  unfold eject
  by_cases h0 : x = 0
  · subst h0; simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    rw [if_neg h0, abs_of_pos hxpos, if_pos hxpos]
    by_cases h : Δ ≤ x
    · rw [if_pos h]
    · rw [if_neg h]
      constructor
      · intro hxg
        rcases hg with rfl | hΔg
        · exact absurd (lt_of_lt_of_le hxpos hxg) (lt_irrefl 0)
        · rw [abs_of_nonneg hg0] at hΔg; exact hΔg
      · intro hΔg; exact le_trans (not_le.mp h).le hΔg

/-- [PROPOSED] The deficit is an involution on the reservoir (reflection about Δ/2): J ∘ J = R.
Intended: on the reservoir |J x| = Δ − |x| ∈ (0,Δ) with the sign of x, so J (J x) = x = R x;
on the gapped set J x = 0 and R x = 0. -/
theorem aux_deficit_deficit_1 (Δ x : ℝ) :
    deficit Δ x = if x = 0 then 0 else if Δ ≤ |x| then 0 else if 0 < x then Δ - x else -Δ - x := by
  unfold deficit eject
  split_ifs <;> linarith

theorem deficit_deficit (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : deficit Δ (deficit Δ x) = remainder Δ x := by
  simp only [aux_deficit_deficit_1, remainder, nullify, ge_iff_le]
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases (Δ - x) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases abs_cases (-Δ - x) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  split_ifs <;> first | linarith | simp_all

/-- [PROPOSED] J is tripotent: J ∘ J ∘ J = J. -/
theorem aux_deficit_tripotent_1 (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : nullify Δ (deficit Δ x) = 0 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [deficit, eject, nullify]
  rcases lt_or_gt_of_ne hx0 with hx | hx <;>
  simp only [aux_deficit_deficit_1, nullify, ge_iff_le] <;>
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases (Δ - x) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases abs_cases (-Δ - x) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  split_ifs <;> first | linarith | simp_all

theorem deficit_tripotent (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    deficit Δ (deficit Δ (deficit Δ x)) = deficit Δ x := by
  rw [deficit_deficit Δ hΔ (deficit Δ x), remainder, aux_deficit_tripotent_1 Δ hΔ x, sub_zero]

/-- [PROPOSED] N ∘ J = 0 (the deficit lives in the reservoir ∪ {0}). -/
theorem nullify_deficit (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : nullify Δ (deficit Δ x) = 0 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [deficit, eject, nullify]
  rcases lt_or_gt_of_ne hx0 with hx | hx <;>
  simp only [aux_deficit_deficit_1, nullify, ge_iff_le] <;>
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases (Δ - x) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases abs_cases (-Δ - x) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  split_ifs <;> first | linarith | simp_all

/-- [PROPOSED] Probe swap: the corpus probe pair is the deficit's action on the positive reservoir,
NorthProbe (J x) = SouthProbe x.  Intended: J x = Δ − x there, and (Δ − x) − Δ/2 = −(x − Δ/2). -/
theorem northProbe_deficit (Δ : ℝ) (x : ℝ) (hx : 0 < x) (hxΔ : x < Δ) :
    NorthProbe Δ (deficit Δ x) = SouthProbe Δ x := by
  have hne : x ≠ 0 := ne_of_gt hx
  have habs : ¬ (Δ ≤ |x|) := by rw [abs_of_pos hx]; exact not_le.mpr hxΔ
  have hE : eject Δ x = Δ := by simp [eject, hne, habs, hx]
  simp only [deficit, NorthProbe, SouthProbe, hE]
  ring

/-- [PROPOSED] E = id + J (definitional). -/
theorem eject_eq_id_add_deficit (Δ x : ℝ) : eject Δ x = x + deficit Δ x := by
  unfold deficit; ring

/-- [PROPOSED] N = id − J ∘ J (pointwise), from `deficit_deficit` and `conservation`. -/
theorem nullify_eq_id_sub_deficit_sq (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    nullify Δ x = x - deficit Δ (deficit Δ x) := by
  rw [deficit_deficit Δ hΔ x]; unfold remainder; ring

/-- [PROPOSED, mnf2_lit §9 + synthesis §2.2] The Euclidean projection onto the non-convex set
G_Δ: 0 below the midpoint, E above it (set-valued at |x| = Δ/2; we take E there).
The corpus probe x − Δ/2 is its decision function; N and E are its two branches. -/
def metricProj (Δ : ℝ) (x : ℝ) : ℝ := if |x| < Δ / 2 then 0 else eject Δ x

/-- [PROPOSED] On the reservoir the projection takes the N-branch iff the probe of |x| is negative. -/
theorem metricProj_branch (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : IsReservoir Δ x) :
    metricProj Δ x = if NorthProbe Δ |x| < 0 then nullify Δ x else eject Δ x := by
  have hn : nullify Δ x = 0 := by
    unfold nullify
    rw [if_neg (not_le.mpr hx.2)]
  simp only [metricProj, NorthProbe, hn]
  split_ifs <;> first | rfl | linarith

/-- [PROPOSED, synthesis §2.2] Branch swap: on the positive reservoir away from the midpoint,
P + P ∘ J = N + E (checked numerically in mnf2_synth/check_synth.py; fails exactly at x = Δ/2). -/
theorem metricProj_deficit_swap (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : 0 < x) (hxΔ : x < Δ)
    (hmid : x ≠ Δ / 2) :
    metricProj Δ x + metricProj Δ (deficit Δ x) = nullify Δ x + eject Δ x := by
  have hne : x ≠ 0 := ne_of_gt hx
  have habs : |x| = x := abs_of_pos hx
  have hnle : ¬ (Δ ≤ |x|) := by rw [habs]; exact not_le.mpr hxΔ
  have hE : eject Δ x = Δ := by simp [eject, hne, hnle, hx]
  have hJ : deficit Δ x = Δ - x := by rw [deficit, hE]
  have hN : nullify Δ x = 0 := by simp [nullify, hnle]
  have hJpos : 0 < Δ - x := by linarith
  have hJabs : |Δ - x| = Δ - x := abs_of_pos hJpos
  have hnle2 : ¬ (Δ ≤ |Δ - x|) := by rw [hJabs]; exact not_le.mpr (by linarith)
  have hE2 : eject Δ (Δ - x) = Δ := by simp [eject, hJpos.ne', hnle2, hJpos]
  rw [hJ]
  unfold metricProj
  rw [habs, hJabs, hE, hE2, hN]
  rcases lt_or_gt_of_ne hmid with h | h
  · rw [if_pos h, if_neg (by linarith)]
  · rw [if_neg (by linarith), if_pos (by linarith)]; ring

/-! ## §3  Representations: the level on which injection lives  [PROPOSED] -/

/-- [PROPOSED] A representation of a value is a finite list of pieces; the value is their sum. -/
abbrev Rep := List ℝ

/-- [PROPOSED] content ρ = Σ pᵢ. -/
def content (ρ : Rep) : ℝ := ρ.sum

/-- [PROPOSED] piecewise reading ν_Δ(ρ) = Σ N(Δ,pᵢ) — "nullify, then pool" (= Batch3 `sumN`). -/
def nu (Δ : ℝ) (ρ : Rep) : ℝ := (ρ.map (nullify Δ)).sum

/-- [PROPOSED] hidden part h_Δ(ρ) = Σ R(Δ,pᵢ) (= Batch3 `sumR`). -/
def hidden (Δ : ℝ) (ρ : Rep) : ℝ := (ρ.map (remainder Δ)).sum

/-- [PROPOSED] piecewise ejection ε_Δ(ρ) = Σ E(Δ,pᵢ). -/
def eps (Δ : ℝ) (ρ : Rep) : ℝ := (ρ.map (eject Δ)).sum

/-- [PROPOSED] all nonzero pieces share a sign. -/
def SameSign (ρ : Rep) : Prop := (∀ p ∈ ρ, 0 ≤ p) ∨ (∀ p ∈ ρ, p ≤ 0)

/-- [PROPOSED] General list conservation ν + h = content.  The corpus proves it only for `[]`,
`[x]` and `[3,12]` (Batch3 aristotle); the general statement is `sorry` in
Nullification_Aristotle_Extension.lean.  Intended: induction on ρ with `conservation`. -/
theorem rep_conservation (Δ : ℝ) (ρ : Rep) : nu Δ ρ + hidden Δ ρ = content ρ := by
  induction ρ with
  | nil => simp [nu, hidden, content]
  | cons p ρ ih =>
    simp only [nu, hidden, content, List.map_cons, List.sum_cons] at ih ⊢
    linarith [conservation Δ p]

/-- [PROPOSED] Non-distributivity at the representation level: ν ≠ N ∘ content
(corpus witness Δ/2 + Δ/2, `not_linear`). -/
theorem rep_not_distributive (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ ρ : Rep, nu Δ ρ ≠ nullify Δ (content ρ) := by
  refine ⟨[Δ / 2, Δ / 2], ?_⟩
  have h1 : |Δ / 2| < Δ := by rw [abs_of_pos (by linarith)]; linarith
  have h2 : |Δ| ≥ Δ := by rw [abs_of_pos hΔ]
  have hc : content [Δ / 2, Δ / 2] = Δ := by
    simp only [content, List.sum_cons, List.sum_nil]; ring
  rw [hc]
  simp only [nu, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold nullify
  rw [if_neg (not_le.mpr h1), if_pos h2]
  linarith

/-! ## §4  Injection = fragmentation; compaction  [PROPOSED] -/

/-- [PROPOSED] Fragmentation injection I_k x = (x/k, …, x/k). -/
def inject (x : ℝ) (k : ℕ) : Rep := List.replicate k (x / k)

/-- [PROPOSED] Compaction C ρ = (content ρ): the left inverse of every I_k. -/
def compact (ρ : Rep) : Rep := [content ρ]

/-- [PROPOSED] Refinement: every piece is split into k equal same-sign pieces. -/
def refine (ρ : Rep) (k : ℕ) : Rep := ρ.flatMap (fun p => List.replicate k (p / k))

/-- [PROPOSED] Injection index k*(Δ,x) = ⌊|x|/Δ⌋ + 1: the smallest k with every equal piece
sub-threshold. -/
def kstar (Δ : ℝ) (x : ℝ) : ℕ := ⌊|x| / Δ⌋₊ + 1

/-- [PROPOSED] Injection conserves content: content (I_k x) = x for k ≥ 1. -/
theorem content_inject (x : ℝ) (k : ℕ) (hk : 0 < k) : content (inject x k) = x := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [content, inject, List.sum_replicate, nsmul_eq_mul]
  field_simp

/-- [PROPOSED, Thm 4.4(i)] Injection is threshold dilation: ν_Δ ∘ I_k = N_{kΔ}.
Intended: ν = k·N(Δ, x/k); Δ ≤ |x|/k ↔ k·Δ ≤ |x| (`le_div_iff`), then `ring`. -/
theorem nu_inject (Δ x : ℝ) (k : ℕ) (hk : 0 < k) : nu Δ (inject x k) = nullify (k * Δ) x := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp only [nu, inject, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  unfold nullify
  simp only [ge_iff_le]
  have habs : |x / k| = |x| / k := by rw [abs_div, Nat.abs_cast]
  by_cases h : (k:ℝ) * Δ ≤ |x|
  · have h' : Δ ≤ |x / k| := by rw [habs, le_div_iff₀ hk']; linarith
    rw [if_pos h', if_pos h]; field_simp
  · have h' : ¬ Δ ≤ |x / k| := by rw [habs, le_div_iff₀ hk']; intro h''; apply h; linarith
    rw [if_neg h', if_neg h]; ring

/-- [PROPOSED] Piecewise ejection of an injected value: ε_Δ ∘ I_k = E_{kΔ}. -/
theorem eps_inject (Δ x : ℝ) (hΔ : 0 < Δ) (k : ℕ) (hk : 0 < k) :
    eps Δ (inject x k) = eject (k * Δ) x := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp only [eps, inject, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  unfold eject
  by_cases hx : x = 0
  · subst hx; simp
  · have hxk : x / k ≠ 0 := div_ne_zero hx hk'.ne'
    rw [if_neg hxk, if_neg hx]
    have habs : |x / k| = |x| / k := by rw [abs_div, Nat.abs_cast]
    by_cases h : (k:ℝ) * Δ ≤ |x|
    · have h' : Δ ≤ |x / k| := by rw [habs, le_div_iff₀ hk']; linarith
      rw [if_pos h', if_pos h]; field_simp
    · have h' : ¬ Δ ≤ |x / k| := by rw [habs, le_div_iff₀ hk']; intro h''; apply h; linarith
      rw [if_neg h', if_neg h]
      by_cases hpos : 0 < x
      · rw [if_pos (div_pos hpos hk'), if_pos hpos]
      · have hnp : ¬ 0 < x / k := by rw [lt_div_iff₀ hk', zero_mul]; exact hpos
        rw [if_neg hnp, if_neg hpos]; ring

/-- [PROPOSED] Every k with |x| < kΔ injects: the piecewise reading is 0 (corollary of `nu_inject`). -/
theorem inject_nullified (Δ x : ℝ) (hΔ : 0 < Δ) (k : ℕ) (hk : 0 < k) (h : |x| < k * Δ) :
    nu Δ (inject x k) = 0 := by
  rw [nu_inject Δ x k hk]; unfold nullify; rw [if_neg (not_le.mpr h)]

/-- [PROPOSED] The injection index injects: k* equal pieces are all sub-threshold.
Intended: |x|/Δ < ⌊|x|/Δ⌋₊ + 1 = k*, so |x| < k*·Δ. -/
theorem inject_at_kstar (Δ x : ℝ) (hΔ : 0 < Δ) : nu Δ (inject x (kstar Δ x)) = 0 := by
  apply inject_nullified Δ x hΔ (kstar Δ x) (Nat.succ_pos _)
  unfold kstar
  have h := Nat.lt_floor_add_one (|x| / Δ)
  rw [div_lt_iff₀ hΔ] at h
  exact_mod_cast h

/-- [PROPOSED] Eventual nullification (the dual of the corpus `accumulation_crosses_threshold`):
every value is nullified by sufficiently fine fragmentation. -/
theorem eventual_nullification (Δ x : ℝ) (hΔ : 0 < Δ) :
    ∃ K : ℕ, ∀ k ≥ K, nu Δ (inject x k) = 0 := by
  refine ⟨kstar Δ x, fun k hk => ?_⟩
  have h1 : |x| < (kstar Δ x : ℝ) * Δ := by
    unfold kstar
    have h := Nat.lt_floor_add_one (|x| / Δ)
    rw [div_lt_iff₀ hΔ] at h
    exact_mod_cast h
  have h2 : (kstar Δ x : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.succ_pos _) hk
  apply inject_nullified Δ x hΔ k hkpos
  calc |x| < (kstar Δ x : ℝ) * Δ := h1
    _ ≤ k * Δ := mul_le_mul_of_nonneg_right h2 hΔ.le

/-- [PROPOSED] A Type A degenerate zero on demand (corpus `IsDegenerateZero_TypeA`, Batch4_2):
for every observable x there is a fragmentation whose pieces are all nullified while the pool is not. -/
theorem typeA_on_demand (Δ x : ℝ) (hΔ : 0 < Δ) (hx : Δ ≤ |x|) :
    ∃ k : ℕ, 0 < k ∧ (∀ p ∈ inject x k, nullify Δ p = 0) ∧ nullify Δ (content (inject x k)) ≠ 0 := by
  refine ⟨kstar Δ x, Nat.succ_pos _, ?_, ?_⟩
  · intro p hp
    have hp' : p = x / (kstar Δ x : ℝ) := List.eq_of_mem_replicate hp
    have hk : (|x| / Δ) < (kstar Δ x : ℝ) := by
      unfold kstar; push_cast; exact Nat.lt_floor_add_one _
    have hkpos : (0 : ℝ) < (kstar Δ x : ℝ) := by
      unfold kstar; push_cast; positivity
    have hlt : |p| < Δ := by
      rw [hp', abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos]
      rw [div_lt_iff₀ hΔ] at hk
      linarith
    unfold nullify
    rw [if_neg (not_le.mpr hlt)]
  · rw [content_inject x (kstar Δ x) (Nat.succ_pos _)]
    unfold nullify
    rw [if_pos hx]
    intro h0
    rw [h0, abs_zero] at hx
    linarith

/-- [PROPOSED] Compaction is the left inverse of injection. -/
theorem compact_inject (x : ℝ) (k : ℕ) (hk : 0 < k) : compact (inject x k) = [x] := by
  simp [compact, content_inject x k hk]

/-- [PROPOSED] N (and E) see through injection: they act on content. -/
theorem nullify_sees_through (Δ x : ℝ) (k : ℕ) (hk : 0 < k) :
    nullify Δ (content (inject x k)) = nullify Δ x := by
  rw [content_inject x k hk]

/-- [PROPOSED] I_j ∘ I_k = I_{jk}: refining an injection is a finer injection (monoid ℕ≥1). -/
theorem aux_refine_inject_1 (a : ℝ) (j k : ℕ) :
    (List.replicate j a).flatMap (fun p : ℝ => List.replicate k (p / k)) = List.replicate (j * k) (a / k) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, Nat.succ_mul, add_comm, List.replicate_add]

theorem refine_inject (x : ℝ) (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    refine (inject x j) k = inject x (j * k) := by
  unfold refine inject
  rw [aux_refine_inject_1, div_div, Nat.cast_mul]

/-! ## §5  Cascades: a ladder is a family of readings, not a composite  [PROPOSED] -/

/-- [PROPOSED] The cascade of ρ over a ladder of thresholds (coarse to fine). -/
def cascade (ρ : Rep) (ladder : List ℝ) : List ℝ := ladder.map (fun Δ => nu Δ ρ)

/-- [PROPOSED] Composing N over a ladder collapses to the coarsest rung (so a ladder is NOT an
iterated operator; corollary of `nullify_comp_nullify`). -/
theorem ladder_not_composite (a b x : ℝ) (hab : b ≤ a) : nullify a (nullify b x) = nullify a x := by
  rw [nullify_comp_nullify, max_eq_left hab]

/-- [PROPOSED] Ejection threshold of a representation δ*(ρ) = sup {Δ > 0 | ν_Δ(ρ) ≠ 0}
(sSup ∅ = 0 in Mathlib's ℝ). -/
def deltaStar (ρ : Rep) : ℝ := sSup {Δ : ℝ | 0 < Δ ∧ nu Δ ρ ≠ 0}

/-- [PROPOSED] The exact representation ejects at its content: δ*((x)) = |x|.
Intended: the set is (0, |x|], bounded above by |x| and containing |x|. -/
theorem deltaStar_singleton (x : ℝ) (hx : x ≠ 0) : deltaStar [x] = |x| := by
  have hx0 : 0 < |x| := abs_pos.mpr hx
  have hset : {Δ : ℝ | 0 < Δ ∧ nu Δ [x] ≠ 0} = {Δ : ℝ | 0 < Δ ∧ Δ ≤ |x|} := by
    ext Δ
    simp only [Set.mem_setOf_eq, nu, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, nullify]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h
      exact h2 (if_neg h)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [if_pos h2]; exact hx
  unfold deltaStar
  rw [hset]
  apply IsGreatest.csSup_eq
  refine ⟨⟨hx0, le_refl _⟩, ?_⟩
  intro Δ hΔ
  exact hΔ.2

/-- [PROPOSED] Nothing survives above the largest piece. -/
theorem nu_eq_zero_of_all_below (Δ : ℝ) (ρ : Rep) (h : ∀ p ∈ ρ, |p| < Δ) : nu Δ ρ = 0 := by
  unfold nu
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  unfold nullify
  rw [if_neg (not_le.mpr (h p hp))]

/-- [PROPOSED] δ*(I_k x) = |x|/k (from `nu_inject`). -/
theorem deltaStar_inject (x : ℝ) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) :
    deltaStar (inject x k) = |x| / k := by
  have hx0 : 0 < |x| := abs_pos.mpr hx
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hset : {Δ : ℝ | 0 < Δ ∧ nu Δ (inject x k) ≠ 0} = {Δ : ℝ | 0 < Δ ∧ Δ ≤ |x| / k} := by
    ext Δ
    simp only [Set.mem_setOf_eq, nu_inject Δ x k hk, nullify]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h
      apply h2
      rw [if_neg]
      intro h'
      apply h
      rw [le_div_iff₀ hkpos]
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [le_div_iff₀ hkpos] at h2
      rw [if_pos (by linarith)]
      exact hx
  unfold deltaStar
  rw [hset]
  apply IsGreatest.csSup_eq
  refine ⟨⟨by positivity, le_refl _⟩, ?_⟩
  intro Δ hΔ
  exact hΔ.2

/-- [PROPOSED, refinement theorem] A same-sign refinement never increases the reading.
Intended: a surviving piece splits into pieces of which at most all survive (same sign, so the
survivors' sum is ≤ the piece); a dead piece has only dead sub-pieces (|p/k| ≤ |p| < Δ). -/
theorem aux_sameSign_refine_le_1 (Δ : ℝ) (k : ℕ) (hk : 0 < k) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ nu Δ (List.replicate k (p / k)) ∧ nu Δ (List.replicate k (p / k)) ≤ nullify Δ p := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  simp only [nu, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  have hpk : 0 ≤ p / k := div_nonneg hp hk'.le
  have hle : p / k ≤ p := div_le_self hp hk1
  have hmul : (k:ℝ) * (p / k) = p := by field_simp
  unfold nullify
  rw [abs_of_nonneg hpk, abs_of_nonneg hp]
  split_ifs with h1 h2 h2
  · rw [hmul]; exact ⟨hp, le_rfl⟩
  · exact absurd (le_trans h1 hle) h2
  · simp [hp]
  · simp

theorem aux_sameSign_refine_le_2 (Δ : ℝ) (k : ℕ) (hk : 0 < k) (p : ℝ) (hp : p ≤ 0) :
    nullify Δ p ≤ nu Δ (List.replicate k (p / k)) ∧ nu Δ (List.replicate k (p / k)) ≤ 0 := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  simp only [nu, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  have hpk : p / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp hk'.le
  have hle : p ≤ p / k := by
    rw [le_div_iff₀ hk']; nlinarith
  have hmul : (k:ℝ) * (p / k) = p := by field_simp
  unfold nullify
  rw [abs_of_nonpos hpk, abs_of_nonpos hp]
  split_ifs with h1 h2 h2
  · rw [hmul]; exact ⟨le_rfl, hp⟩
  · simp [hp]
  · exfalso; linarith
  · simp

theorem aux_sameSign_refine_le_3 (Δ : ℝ) (k : ℕ) (hk : 0 < k) (ρ : Rep) (h : ∀ p ∈ ρ, 0 ≤ p) :
    0 ≤ nu Δ (refine ρ k) ∧ nu Δ (refine ρ k) ≤ nu Δ ρ := by
  induction ρ with
  | nil => simp [nu, refine]
  | cons p ρ ih =>
    have hp : 0 ≤ p := h p (by simp)
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h1 := aux_sameSign_refine_le_1 Δ k hk p hp
    have e : nu Δ (refine (p :: ρ) k) = nu Δ (List.replicate k (p / k)) + nu Δ (refine ρ k) := by
      simp only [nu, refine, List.flatMap_cons, List.map_append, List.sum_append]
    rw [e]
    simp only [nu, List.map_cons, List.sum_cons] at ih' ⊢
    simp only [nu] at h1
    constructor <;> linarith [ih'.1, ih'.2, h1.1, h1.2]

theorem aux_sameSign_refine_le_4 (Δ : ℝ) (k : ℕ) (hk : 0 < k) (ρ : Rep) (h : ∀ p ∈ ρ, p ≤ 0) :
    nu Δ ρ ≤ nu Δ (refine ρ k) ∧ nu Δ (refine ρ k) ≤ 0 := by
  induction ρ with
  | nil => simp [nu, refine]
  | cons p ρ ih =>
    have hp : p ≤ 0 := h p (by simp)
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h1 := aux_sameSign_refine_le_2 Δ k hk p hp
    have e : nu Δ (refine (p :: ρ) k) = nu Δ (List.replicate k (p / k)) + nu Δ (refine ρ k) := by
      simp only [nu, refine, List.flatMap_cons, List.map_append, List.sum_append]
    rw [e]
    simp only [nu, List.map_cons, List.sum_cons] at ih' ⊢
    simp only [nu] at h1
    constructor <;> linarith [ih'.1, ih'.2, h1.1, h1.2]

theorem sameSign_refine_le (Δ : ℝ) (hΔ : 0 < Δ) (ρ : Rep) (h : SameSign ρ) (k : ℕ) (hk : 0 < k) :
    |nu Δ (refine ρ k)| ≤ |nu Δ ρ| := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := aux_sameSign_refine_le_3 Δ k hk ρ h
    rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]
    exact h2
  · obtain ⟨h1, h2⟩ := aux_sameSign_refine_le_4 Δ k hk ρ h
    rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]
    linarith

/-- [PROPOSED] Same-sign readings never exceed the content. -/
theorem aux_sameSign_nu_le_content_1 (Δ : ℝ) (ρ : Rep) (h : ∀ p ∈ ρ, 0 ≤ p) :
    0 ≤ nu Δ ρ ∧ nu Δ ρ ≤ content ρ := by
  induction ρ with
  | nil => simp [nu, content]
  | cons p ρ ih =>
    have hp : 0 ≤ p := h p (by simp)
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [nu, content, List.map_cons, List.sum_cons] at ih' ⊢
    have : 0 ≤ nullify Δ p ∧ nullify Δ p ≤ p := by
      unfold nullify; split_ifs <;> simp [hp]
    constructor <;> linarith [ih'.1, ih'.2, this.1, this.2]

theorem aux_sameSign_nu_le_content_2 (Δ : ℝ) (ρ : Rep) (h : ∀ p ∈ ρ, p ≤ 0) :
    content ρ ≤ nu Δ ρ ∧ nu Δ ρ ≤ 0 := by
  induction ρ with
  | nil => simp [nu, content]
  | cons p ρ ih =>
    have hp : p ≤ 0 := h p (by simp)
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [nu, content, List.map_cons, List.sum_cons] at ih' ⊢
    have : p ≤ nullify Δ p ∧ nullify Δ p ≤ 0 := by
      unfold nullify; split_ifs <;> simp [hp]
    constructor <;> linarith [ih'.1, ih'.2, this.1, this.2]

theorem sameSign_nu_le_content (Δ : ℝ) (ρ : Rep) (h : SameSign ρ) : |nu Δ ρ| ≤ |content ρ| := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := aux_sameSign_nu_le_content_1 Δ ρ h
    rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]
    exact h2
  · obtain ⟨h1, h2⟩ := aux_sameSign_nu_le_content_2 Δ ρ h
    rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]
    linarith

/-- [PROPOSED] Same-sign readings are sign-safe: a nonzero reading has the content's sign. -/
theorem sameSign_sign (Δ : ℝ) (ρ : Rep) (h : SameSign ρ) (hn : nu Δ ρ ≠ 0) :
    0 < nu Δ ρ * content ρ := by
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := aux_sameSign_nu_le_content_1 Δ ρ h
    have hpos : 0 < nu Δ ρ := lt_of_le_of_ne h1 (Ne.symm hn)
    exact mul_pos hpos (lt_of_lt_of_le hpos h2)
  · obtain ⟨h1, h2⟩ := aux_sameSign_nu_le_content_2 Δ ρ h
    have hneg : nu Δ ρ < 0 := lt_of_le_of_ne h2 hn
    exact mul_pos_of_neg_of_neg hneg (lt_of_le_of_lt h1 hneg)

/-- [PROPOSED] For mixed signs refinement can INCREASE the reading (residue regime):
(3, −2.9) reads 3 at Δ = 3 while its compaction (0.1) reads 0. -/
theorem mixed_refine_can_increase : ∃ (Δ : ℝ) (ρ : Rep), |nu Δ (compact ρ)| < |nu Δ ρ| := by
  refine ⟨3, [3, -2.9], ?_⟩
  simp only [nu, compact, content, nullify, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- [PROPOSED, Thm 5.5] An exact-zero reading is uninformative: it is consistent with content 0
and with nonzero content, and does not persist to a finer rung ((0.4, 0.3) at Δ = 1 reads 0, at
Δ = 0.35 reads 0.4). -/
theorem zero_reading_uninformative :
    ∃ (Δ : ℝ) (ρ₁ ρ₂ : Rep), nu Δ ρ₁ = 0 ∧ nu Δ ρ₂ = 0 ∧ content ρ₁ = 0 ∧ content ρ₂ ≠ 0 ∧
      ∃ Δ' < Δ, nu Δ' ρ₂ ≠ 0 := by
  refine ⟨1, [0], [0.4, 0.3], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, 0.35, by norm_num, ?_⟩ <;>
  · simp only [nu, content, nullify, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num [abs_of_nonneg, abs_of_nonpos]

/-! ### In-process cascades (the lab's 25/25 result): nullification inside the dynamics is
    not nullification of the final partition  [PROPOSED] -/

/-- [PROPOSED] One truncated step of a linear dynamics on n coefficients: apply L, then nullify
every coordinate (what a Pauli-path or MPS simulator does at every time step / bond). -/
def inProcessStep {n : ℕ} (Δ : ℝ) (L : (Fin n → ℝ) → (Fin n → ℝ)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => nullify Δ (L v i)

/-- [PROPOSED] t in-process steps. -/
def inProcess {n : ℕ} (Δ : ℝ) (L : (Fin n → ℝ) → (Fin n → ℝ)) : ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0 => id
  | t + 1 => fun v => inProcessStep Δ L (inProcess Δ L t v)

/-- [PROPOSED] Post-hoc nullification of the exact t-step evolution. -/
def postHoc {n : ℕ} (Δ : ℝ) (L : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => nullify Δ ((L^[t] v) i)

/-- [PROPOSED] In-process and post-hoc truncation differ, and the difference is in the confining
direction.  Witness (checked in mnf2_synth/check_synth.py): v = (Δ, 0), L v = (v₀/2 + 2·v₁, v₀/2).
Exactly: L v = (Δ/2, Δ/2), L² v = (5Δ/4, Δ/4), post-hoc N gives (5Δ/4, 0); in-process kills both
halves after step 1 and returns (0, 0).  This is corpus `not_linear` realised along a path. -/
theorem inProcess_ne_postHoc (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (L : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (v : Fin 2 → ℝ),
      inProcess Δ L 2 v = 0 ∧ postHoc Δ L 2 v ≠ 0 := by
  refine ⟨fun v => ![v 0 / 2 + 2 * v 1, v 0 / 2], ![Δ, 0], ?_, ?_⟩
  · have hlt : ¬ (Δ ≤ |Δ / 2|) := by
      rw [abs_of_pos (by linarith)]; linarith
    have h1 : inProcessStep Δ (fun v : Fin 2 → ℝ => ![v 0 / 2 + 2 * v 1, v 0 / 2]) ![Δ, 0] = 0 := by
      funext i
      fin_cases i <;> simp [inProcessStep, nullify, hlt]
    have h2 : inProcessStep Δ (fun v : Fin 2 → ℝ => ![v 0 / 2 + 2 * v 1, v 0 / 2]) 0 = 0 := by
      funext i
      fin_cases i <;> simp [inProcessStep, nullify]
    simp only [inProcess, id]
    rw [h1, h2]
  · intro h
    have h0 := congrFun h 0
    have hL : ((fun v : Fin 2 → ℝ => ![v 0 / 2 + 2 * v 1, v 0 / 2])^[2] ![Δ, 0]) 0 = 5 * Δ / 4 := by
      show ((fun v : Fin 2 → ℝ => ![v 0 / 2 + 2 * v 1, v 0 / 2])
        ((fun v : Fin 2 → ℝ => ![v 0 / 2 + 2 * v 1, v 0 / 2]) ![Δ, 0])) 0 = 5 * Δ / 4
      simp; ring
    simp only [postHoc, hL, Pi.zero_apply] at h0
    unfold nullify at h0
    rw [if_pos (by rw [abs_of_pos (by linarith)]; linarith)] at h0
    linarith

/-! ## §6  Signed cancellation residue and the sign gate  [PROPOSED] -/

/-- [PROPOSED] Cancellation residue res_Δ(ρ) = ν_Δ(ρ) − N(Δ, content ρ). -/
def residue (Δ : ℝ) (ρ : Rep) : ℝ := nu Δ ρ - nullify Δ (content ρ)

/-- [PROPOSED] res = R(content) − hidden (from `rep_conservation` and `conservation`). -/
theorem residue_eq (Δ : ℝ) (ρ : Rep) : residue Δ ρ = remainder Δ (content ρ) - hidden Δ ρ := by
  unfold residue remainder
  linarith [rep_conservation Δ ρ]

/-- [PROPOSED, Prop 6.3b(a)] Two-piece sign safety: with two pieces a nonzero reading has the
content's sign.  Intended: both survive → ν = p + q; one survives, say p, then |p| ≥ Δ > |q| so
sgn (p + q) = sgn p. -/
theorem two_piece_sign_safe (Δ : ℝ) (hΔ : 0 < Δ) (p q : ℝ) (hn : nu Δ [p, q] ≠ 0) :
    0 < nu Δ [p, q] * (p + q) := by
  unfold nu nullify at hn ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hn ⊢
  split_ifs at hn ⊢ with h1 h2 h2
  · exact mul_self_pos.mpr hn
  · have hq := abs_lt.mp (not_le.mp h2)
    rcases le_abs.mp h1 with h | h
    · nlinarith
    · nlinarith
  · have hp := abs_lt.mp (not_le.mp h1)
    rcases le_abs.mp h2 with h | h
    · nlinarith
    · nlinarith
  · exact absurd (by ring) hn

/-- [PROPOSED, Thm 6.3] Every reservoir value has mixed-sign representations reading +Δ and −Δ:
both readings are pure residue and only one has the sign of x.
Witnesses for 0 < x < Δ: ρ⁺ = (Δ, x − Δ), ρ⁻ = (−Δ, (x+Δ)/2, (x+Δ)/2). -/
theorem residue_both_signs (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : 0 < x) (hxΔ : x < Δ) :
    ∃ ρp ρm : Rep, content ρp = x ∧ content ρm = x ∧ nu Δ ρp = Δ ∧ nu Δ ρm = -Δ := by
  refine ⟨[Δ, x - Δ], [-Δ, (x + Δ) / 2, (x + Δ) / 2], ?_, ?_, ?_, ?_⟩
  · simp only [content, List.sum_cons, List.sum_nil]; ring
  · simp only [content, List.sum_cons, List.sum_nil]; ring
  · have hA : nullify Δ Δ = Δ := by
      unfold nullify; rw [if_pos (le_abs_self Δ)]
    have hB : nullify Δ (x - Δ) = 0 := by
      unfold nullify; rw [if_neg (not_le.mpr (by rw [abs_of_neg (by linarith)]; linarith))]
    simp [nu, hA, hB]
  · have hA : nullify Δ (-Δ) = -Δ := by
      unfold nullify; rw [if_pos (by rw [abs_neg]; exact le_abs_self Δ)]
    have hB : nullify Δ ((x + Δ) / 2) = 0 := by
      unfold nullify; rw [if_neg (not_le.mpr (by rw [abs_of_pos (by linarith)]; linarith))]
    simp [nu, hA, hB]

/-- [PROPOSED, Thm 6.4(c′)] Full realisability: any reading with |r| ≥ Δ is produced by some
representation of ANY value x.  Witness ρ = (r, (x−r)/j, …, (x−r)/j) with j = k*(Δ, x − r).
Consequence: readings alone carry no information about x without a structural assumption on
the fragmentation; the sign gate is minimax, not a certificate. -/
theorem realise (Δ : ℝ) (hΔ : 0 < Δ) (x r : ℝ) (hr : Δ ≤ |r|) :
    ∃ ρ : Rep, content ρ = x ∧ nu Δ ρ = r := by
  refine ⟨r :: inject (x - r) (kstar Δ (x - r)), ?_, ?_⟩
  · have h := content_inject (x - r) (kstar Δ (x - r)) (Nat.succ_pos _)
    unfold content at h ⊢
    rw [List.sum_cons, h]; ring
  · have h := inject_at_kstar Δ (x - r) hΔ
    unfold nu at h ⊢
    rw [List.map_cons, List.sum_cons, h]
    unfold nullify; rw [if_pos hr]; ring

/-- [PROPOSED] The G4 sign gate on a list of readings of one value: both signs present → 0
(a cancellation residue is present and the readings cannot say which); one sign → that sign;
no nonzero reading → 0 (abstention). -/
def signGate (rs : List ℝ) : ℤ :=
  let pos := rs.any (fun r => decide (0 < r))
  let neg := rs.any (fun r => decide (r < 0))
  if pos && neg then 0 else if pos then 1 else if neg then -1 else 0

/-- [PROPOSED, Thm 6.4(b)] Any rule that asserts a sign on a contradictory multiset is wrong
on some value: the multiset is realisable from a value of the opposite sign.
Intended: take x := −(F M) (nonzero, opposite sign) and realise every reading from x. -/
theorem aux_gate_minimax_1 (Δ x : ℝ) (hΔ : 0 < Δ) (M : List ℝ) (hM : ∀ r ∈ M, Δ ≤ |r|) :
    ∃ ρs : List Rep, ρs.map (nu Δ) = M ∧ ∀ ρ ∈ ρs, content ρ = x := by
  induction M with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons r M ih =>
    obtain ⟨ρs, h1, h2⟩ := ih (fun r' hr' => hM r' (List.mem_cons_of_mem _ hr'))
    obtain ⟨ρ, hc, hn⟩ := realise Δ hΔ x r (hM r List.mem_cons_self)
    refine ⟨ρ :: ρs, ?_, ?_⟩
    · simp [h1, hn]
    · intro ρ' hρ'
      rcases List.mem_cons.mp hρ' with h | h
      · rw [h]; exact hc
      · exact h2 ρ' h

theorem gate_minimax (Δ : ℝ) (hΔ : 0 < Δ) (F : List ℝ → ℤ) (M : List ℝ)
    (hMΔ : ∀ r ∈ M, Δ ≤ |r|) (hF : F M ≠ 0) :
    ∃ x : ℝ, x ≠ 0 ∧ (∃ ρs : List Rep, ρs.map (nu Δ) = M ∧ ∀ ρ ∈ ρs, content ρ = x) ∧
      (F M : ℝ) * x < 0 := by
  have hF' : (F M : ℝ) ≠ 0 := by exact_mod_cast hF
  obtain ⟨ρs, h1, h2⟩ := aux_gate_minimax_1 Δ (-(F M : ℝ)) hΔ M hMΔ
  refine ⟨-(F M : ℝ), neg_ne_zero.mpr hF', ⟨ρs, h1, h2⟩, ?_⟩
  nlinarith [mul_self_pos.mpr hF']

/-! ## §7  Soft (gated) nullification: where z·|r|^p sits  [PROPOSED] -/

/-- [PROPOSED] Soft gate on a witness w: g(w) = min(1, w/Δ)^p.  p = ½, Δ = 1 on w = |r| is the
G2_v9 correction. -/
def softGate (Δ p w : ℝ) : ℝ := (min 1 (w / Δ)) ^ p

/-- [PROPOSED] Gated nullification S_g(x; w) = x·g(w). -/
def softNullify (Δ p x w : ℝ) : ℝ := x * softGate Δ p w

/-- [PROPOSED, Thm 7.2(i)] With the witness fixed, the gated operator is idempotent for all x
iff the gate is hard (0 or 1).  Intended: x·g² = x·g for all x ↔ g² = g. -/
theorem soft_idem_iff (Δ p w : ℝ) :
    (∀ x, softNullify Δ p (softNullify Δ p x w) w = softNullify Δ p x w) ↔
      (softGate Δ p w = 0 ∨ softGate Δ p w = 1) := by
  unfold softNullify
  generalize softGate Δ p w = g
  constructor
  · intro h
    have hg : g * g = g := by simpa using h 1
    have hg' : g * (g - 1) = 0 := by linear_combination hg
    rcases mul_eq_zero.mp hg' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (h | h) x <;> simp [h]

/-- [PROPOSED, Thm 7.2(iii)] A strictly soft gate has no spectral gap in x: it maps Δ'/(2g) into (0, Δ'). -/
theorem soft_no_gap (g Δ' : ℝ) (hg : 0 < g) (hg1 : g < 1) (hΔ' : 0 < Δ') :
    ∃ x : ℝ, 0 < |x * g| ∧ |x * g| < Δ' := by
  refine ⟨Δ' / (2 * g), ?_, ?_⟩
  · have h : Δ' / (2 * g) * g = Δ' / 2 := by field_simp
    rw [h, abs_of_pos (by positivity)]; positivity
  · have h : Δ' / (2 * g) * g = Δ' / 2 := by field_simp
    rw [h, abs_of_pos (by positivity)]; linarith

/-- [PROPOSED] The hard gate on the witness w = |x| is N itself. -/
theorem hardGate_is_nullify (Δ x : ℝ) : x * (if Δ ≤ |x| then 1 else 0) = nullify Δ x := by
  unfold nullify; split_ifs <;> simp

/-! ## §8  The additive value-level pair (mnf2_formal/catalogue.md §3.2), for completeness  [PROPOSED] -/

/-- [PROPOSED] Additive injection: the part of x + y that stays in the reservoir.  Changes the
content (it is negative accumulation); every theorem about it is a renaming of corpus lemmas. -/
def injectAdd (Δ x y : ℝ) : ℝ := remainder Δ (x + y)

/-- [PROPOSED] Additive ejection: the part of x + y that crosses. -/
def ejectAdd (Δ x y : ℝ) : ℝ := nullify Δ (x + y)

/-- [PROPOSED] = corpus `conservation` at x + y. -/
theorem injectAdd_ejectAdd (Δ x y : ℝ) : injectAdd Δ x y + ejectAdd Δ x y = x + y := by
  unfold injectAdd ejectAdd; rw [add_comm]; exact conservation Δ (x + y)

/-- [PROPOSED] = corpus `not_linear`: additive injection does not commute with N. -/
theorem ejectAdd_not_additive (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ x y : ℝ, ejectAdd Δ x y ≠ nullify Δ x + nullify Δ y := by
  refine ⟨Δ / 2, Δ / 2, ?_⟩
  unfold ejectAdd nullify
  have h1 : |Δ / 2 + Δ / 2| ≥ Δ := by
    rw [show Δ / 2 + Δ / 2 = Δ by ring, abs_of_pos hΔ]
  have h2 : ¬ (|Δ / 2| ≥ Δ) := by
    rw [abs_of_pos (by linarith)]; linarith
  rw [if_pos h1, if_neg h2]; linarith

end MNF.Extension
