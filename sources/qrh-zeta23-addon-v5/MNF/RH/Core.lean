/-
═══════════════════════════════════════════════════════════════════════
MNF × RIEMANN ZETA — CORE  (MNF/RH/Core.lean)
Unconditional facts about the nontrivial zeros of ζ, their multiplicities,
and the functional-equation symmetry.  Everything in this file is proved
from Mathlib alone: no axiom, no `sorry`, no hypothesis about ζ.
═══════════════════════════════════════════════════════════════════════
Builds at both pins the corpus uses:
  corpus  Lean v4.24.0 / Mathlib f897ebcf
  openai  Lean v4.34.1 / Mathlib d13f23b7   (the pin of github.com/openai/math)

Contents
  §1  definitions     is_nontrivial_zero, ZetaZeros, zeta_order, ShiftedZeroSpectrum,
                      AllZerosSimple, DerivativeNonvanishing
  §2  analyticity     analyticAt_riemannZeta, zeta_order_ne_top, zeta_order_ge_one
  §3  multiplicity    order_one_iff_deriv, deriv_zero_of_high_order
  §4  symmetry        nontrivial_zero_reflect, feFactor, deriv_reflect,
                      analyticOrderAt_reflect, zeta_order_reflect, shifted_symmetric
  §5  where zeros are riemannHypothesis_iff_strip (Mathlib's RH ↔ every nontrivial
                      zero has Re = 1/2), shifted_bounded (|x| < 1/2)

Register: [PROVED] for every theorem below (kernel-checked; see the
`#print axioms` block at the end: only propext, Classical.choice, Quot.sound).

Provenance.  §2–§3 restate, with fresh proofs, the lemmas the corpus files
output71_minimal_axiom / output79 / output84 proved at the corpus pin
(zeta_order_ge_one, order_one_iff_deriv, deriv_zero_of_high_order).  §4 proves
what output86 assumed as the axiom `func_eq_deriv` (here only at zeros, which is
where it is true) and what the hackathon scan listed as `multiplicity_symmetric`
and `shifted_spectrum_symmetric`.  §5 proves what output71/72 assumed as the
`Bridge` hypothesis (Spec ⊆ {0} → Mathlib's RiemannHypothesis).
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace MNF.RH

open Complex Filter Topology
open scoped Real

/-! ### §1 Definitions -/

/-- A nontrivial zero: a zero of `ζ` in the open critical strip. -/
def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def ZetaZeros : Set ℂ := {ρ | is_nontrivial_zero ρ}

/-- Multiplicity of `ρ` as a zero of `ζ` (0 if `ζ` is not analytic there or `ζ ρ ≠ 0`;
`ENat.toNat` sends `⊤` to 0, but `⊤` never occurs at a nontrivial zero: `zeta_order_ne_top`). -/
noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The MNF "shifted zero spectrum": real parts of the nontrivial zeros, centred on the line. -/
def ShiftedZeroSpectrum : Set ℝ := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}

def AllZerosSimple : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ = 1

def DerivativeNonvanishing : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → deriv riemannZeta ρ ≠ 0

theorem ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [this, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

theorem ne_one_of_re_lt_one {s : ℂ} (hs : s.re < 1) : s ≠ 1 := by
  intro h; rw [h] at hs; simp at hs

theorem re_one_sub (ρ : ℂ) : (1 - ρ).re = 1 - ρ.re := by simp

/-! ### §2 Analyticity and finiteness of the order -/

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  refine DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) ?_ (hU.mem_nhds hs)
  intro z hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

/-- `ζ` is analytic on the open half-plane `Re s < 1`, which is convex, hence preconnected. -/
theorem analyticOnNhd_riemannZeta_left : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.re < 1} :=
  fun _ hz => analyticAt_riemannZeta (ne_one_of_re_lt_one hz)

theorem isPreconnected_halfPlane : IsPreconnected {s : ℂ | s.re < 1} :=
  (convex_halfSpace_re_lt (r := 1)).isPreconnected

/-- `ζ` is not identically zero near any point with `Re s < 1`: its order there is finite
(identity theorem on the half-plane, anchored at `ζ 0 = -1/2 ≠ 0`). -/
theorem analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s.re < 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h0 : analyticOrderAt riemannZeta 0 ≠ ⊤ := by
    have : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    rw [analyticOrderAt_eq_zero.2 (Or.inr this)]
    exact ENat.zero_ne_top
  exact analyticOnNhd_riemannZeta_left.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_halfPlane (by simp) hs h0

theorem zeta_order_ne_top {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ :=
  analyticOrderAt_riemannZeta_ne_top h.2.2

theorem analyticOrderAt_eq_zeta_order {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    analyticOrderAt riemannZeta ρ = (zeta_order ρ : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (zeta_order_ne_top h)
  unfold zeta_order
  rw [← hn]
  simp

/-- Every nontrivial zero has multiplicity at least one. -/
theorem zeta_order_ge_one {ρ : ℂ} (h : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ := by
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨analyticAt_riemannZeta (ne_one_of_re_lt_one h.2.2), h.1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  unfold zeta_order at h0
  rcases ENat.toNat_eq_zero.1 h0 with h0 | h0
  · exact hne h0
  · exact zeta_order_ne_top h h0

/-! ### §3 Multiplicity one ⟺ nonvanishing derivative -/

/-- Derivative at `ρ` of `(z - ρ)^m · g z` for `m ≥ 1`: it is `g ρ` when `m = 1` and `0` otherwise. -/
theorem deriv_centered_pow_mul {g : ℂ → ℂ} {ρ : ℂ} (hg : DifferentiableAt ℂ g ρ) {m : ℕ}
    (hm : 1 ≤ m) : deriv (fun z => (z - ρ) ^ m * g z) ρ = if m = 1 then g ρ else 0 := by
  have h1 : HasDerivAt (fun z : ℂ => (z - ρ) ^ m) ((m : ℂ) * (ρ - ρ) ^ (m - 1) * 1) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).pow m
  rw [show (fun z => (z - ρ) ^ m * g z) = (fun z => (z - ρ) ^ m) * g from rfl,
    (h1.mul hg.hasDerivAt).deriv]
  rcases m with _ | _ | m
  · omega
  · simp
  · simp [pow_succ]

/-- A nontrivial zero is simple iff `ζ'` does not vanish there. -/
theorem order_one_iff_deriv {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    zeta_order ρ = 1 ↔ deriv riemannZeta ρ ≠ 0 := by
  have hA := analyticAt_riemannZeta (ne_one_of_re_lt_one h.2.2)
  obtain ⟨g, hg, hg0, hev⟩ := hA.analyticOrderAt_eq_natCast.1 (analyticOrderAt_eq_zeta_order h)
  have hd : deriv riemannZeta ρ = deriv (fun z => (z - ρ) ^ zeta_order ρ * g z) ρ := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hev] with z hz
    simpa [smul_eq_mul] using hz
  rw [hd, deriv_centered_pow_mul hg.differentiableAt (zeta_order_ge_one h)]
  constructor
  · intro h1; simp [h1, hg0]
  · intro hne; by_contra hne1; simp [hne1] at hne

theorem deriv_zero_of_high_order {ρ : ℂ} (h : is_nontrivial_zero ρ) (h2 : 2 ≤ zeta_order ρ) :
    deriv riemannZeta ρ = 0 := by
  by_contra hne
  have := (order_one_iff_deriv h).2 hne
  omega

theorem allZerosSimple_iff_derivativeNonvanishing : AllZerosSimple ↔ DerivativeNonvanishing :=
  ⟨fun hs ρ hρ => (order_one_iff_deriv hρ).1 (hs ρ hρ),
   fun hd ρ hρ => (order_one_iff_deriv hρ).2 (hd ρ hρ)⟩

/-! ### §4 The functional-equation symmetry `ρ ↦ 1 - ρ` -/

/-- Zeros of the strip reflect: `ζ ρ = 0 → ζ (1 - ρ) = 0` (from Mathlib's `riemannZeta_one_sub`). -/
theorem nontrivial_zero_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) : is_nontrivial_zero (1 - ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub (ne_neg_nat_of_re_pos h.2.1) (ne_one_of_re_lt_one h.2.2), h.1, mul_zero]
  · rw [re_one_sub]; linarith [h.2.2]
  · rw [re_one_sub]; linarith [h.2.1]

/-- The factor in `ζ(1 - s) = feFactor s · ζ s`. -/
noncomputable def feFactor (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2)

theorem cos_pi_half_eq_zero_iff (s : ℂ) : cos (π * s / 2) = 0 ↔ ∃ k : ℤ, s = 2 * k + 1 := by
  rw [Complex.cos_eq_zero_iff]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_left_cancel₀ hπ ?_⟩
    linear_combination 2 * hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem two_pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero this

theorem feFactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : feFactor s ≠ 0 := by
  unfold feFactor
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos h0)) ?_
  · intro h
    exact two_pi_ne_zero ((cpow_eq_zero_iff _ _).1 h).1
  · intro h
    obtain ⟨k, hk⟩ := (cos_pi_half_eq_zero_iff s).1 h
    have hre := congrArg Complex.re hk
    simp at hre
    have hk0 : (0 : ℝ) < 2 * k + 1 := by linarith
    have hk1 : (2 * k + 1 : ℝ) < 1 := by linarith
    have hk0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast hk0
    have hk1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast hk1
    omega

theorem feFactor_analyticAt {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ feFactor s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re}) ?_ (hU.mem_nhds h0)
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hg : DifferentiableAt ℂ Gamma z := differentiableAt_Gamma z (ne_neg_nat_of_re_pos hz)
  have hp : DifferentiableAt ℂ (fun w : ℂ => (2 * π : ℂ) ^ (-w)) z :=
    differentiableAt_id.neg.const_cpow (Or.inl two_pi_ne_zero)
  have hc : DifferentiableAt ℂ (fun w : ℂ => cos (π * w / 2)) z :=
    ((differentiableAt_id.const_mul _).div_const _).ccos
  exact ((hp.const_mul _).mul hg).mul hc

/-- Near any point of the open strip, `ζ(1 - s) = feFactor s · ζ s`. -/
theorem fe_eventually {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 ρ] feFactor * riemannZeta := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with s hs
  simp only [Pi.mul_apply, feFactor]
  exact riemannZeta_one_sub (ne_neg_nat_of_re_pos hs.1) (ne_one_of_re_lt_one hs.2)

/-- `ζ'(1 - ρ) = -feFactor ρ · ζ'(ρ)` at every nontrivial zero `ρ`.
(This is the statement output86 assumed as the axiom `func_eq_deriv`, restricted to zeros,
where it holds; stated for all `s` it is false.) -/
theorem deriv_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    deriv riemannZeta (1 - ρ) = -(feFactor ρ * deriv riemannZeta ρ) := by
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (1 - ρ)) (1 - ρ) :=
    (differentiableAt_riemannZeta (ne_one_of_re_lt_one (nontrivial_zero_reflect h).2.2)).hasDerivAt
  have hcomp : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (1 - ρ) * (-1)) ρ :=
    hζ.comp ρ ((hasDerivAt_id ρ).const_sub 1)
  have hF : HasDerivAt (feFactor * riemannZeta)
      (deriv feFactor ρ * riemannZeta ρ + feFactor ρ * deriv riemannZeta ρ) ρ :=
    (feFactor_analyticAt h.2.1).differentiableAt.hasDerivAt.mul
      (differentiableAt_riemannZeta (ne_one_of_re_lt_one h.2.2)).hasDerivAt
  have hF' : HasDerivAt (fun s => riemannZeta (1 - s))
      (deriv feFactor ρ * riemannZeta ρ + feFactor ρ * deriv riemannZeta ρ) ρ :=
    hF.congr_of_eventuallyEq (fe_eventually h.2.1 h.2.2)
  have := hcomp.unique hF'
  rw [h.1, mul_zero, zero_add] at this
  linear_combination -this

theorem deriv_ne_zero_reflect_iff {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    deriv riemannZeta (1 - ρ) ≠ 0 ↔ deriv riemannZeta ρ ≠ 0 := by
  rw [deriv_reflect h, neg_ne_zero, mul_ne_zero_iff]
  exact ⟨fun h' => h'.2, fun h' => ⟨feFactor_ne_zero h.2.1 h.2.2, h'⟩⟩

/-- Order of `f ∘ (1 - ·)` at `ρ` equals the order of `f` at `1 - ρ`. -/
theorem analyticOrderAt_comp_one_sub {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f (1 - ρ)) :
    analyticOrderAt (fun s => f (1 - s)) ρ = analyticOrderAt f (1 - ρ) := by
  have hA : AnalyticAt ℂ (fun s => f (1 - s)) ρ :=
    hf.comp (analyticAt_const.sub analyticAt_id)
  have hT : Tendsto (fun s : ℂ => 1 - s) (𝓝 ρ) (𝓝 (1 - ρ)) :=
    (continuous_const.sub continuous_id).tendsto ρ
  by_cases htop : analyticOrderAt f (1 - ρ) = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    exact hT.eventually (analyticOrderAt_eq_top.1 htop)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    rw [← hn]
    obtain ⟨g, hg, hg0, hev⟩ := hf.analyticOrderAt_eq_natCast.1 hn.symm
    refine hA.analyticOrderAt_eq_natCast.2 ⟨fun s => (-1) ^ n * g (1 - s), ?_, ?_, ?_⟩
    · exact analyticAt_const.mul (hg.comp (analyticAt_const.sub analyticAt_id))
    · simp [hg0]
    · filter_upwards [hT.eventually hev] with s hs
      rw [hs, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow]
      congr 2
      ring

/-- Multiplicities are symmetric under `ρ ↦ 1 - ρ`. -/
theorem analyticOrderAt_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
  rw [← analyticOrderAt_comp_one_sub (analyticAt_riemannZeta
        (ne_one_of_re_lt_one (nontrivial_zero_reflect h).2.2)),
    analyticOrderAt_congr (fe_eventually h.2.1 h.2.2),
    analyticOrderAt_mul (feFactor_analyticAt h.2.1) (analyticAt_riemannZeta (ne_one_of_re_lt_one h.2.2)),
    analyticOrderAt_eq_zero.2 (Or.inr (feFactor_ne_zero h.2.1 h.2.2)), zero_add]

theorem zeta_order_reflect {ρ : ℂ} (h : is_nontrivial_zero ρ) :
    zeta_order (1 - ρ) = zeta_order ρ := by
  unfold zeta_order; rw [analyticOrderAt_reflect h]

/-- The shifted spectrum is symmetric about `0`. -/
theorem shifted_symmetric {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : -x ∈ ShiftedZeroSpectrum := by
  obtain ⟨ρ, hρ, rfl⟩ := hx
  exact ⟨1 - ρ, nontrivial_zero_reflect hρ, by rw [re_one_sub]; ring⟩

/-! ### §5 Where the zeros are -/

/-- Any zero of `ζ` that is neither a trivial zero nor `1` lies in the open critical strip.
(Right of the strip: Mathlib's nonvanishing on `Re s ≥ 1`.  Left of it: the functional
equation, `Γ ≠ 0`, and the zeros of `cos`.) -/
theorem in_strip_of_zero {s : ℂ} (hs : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1))
    (h1 : s ≠ 1) : 0 < s.re ∧ s.re < 1 := by
  have hlt : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hge) hs
  refine ⟨?_, hlt⟩
  by_contra hle
  have hle' : s.re ≤ 0 := not_lt.1 hle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  have htre : 1 ≤ (1 - s).re := by rw [re_one_sub]; linarith
  have htpos : 0 < (1 - s).re := by linarith
  have ht1 : (1 - s) ≠ 1 := by
    intro h; apply hs0; linear_combination -h
  have hfe := riemannZeta_one_sub (ne_neg_nat_of_re_pos htpos) ht1
  rw [sub_sub_cancel, hs] at hfe
  have hζt : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    have h2 : (2:ℂ) ≠ 0 := two_ne_zero
    have hp : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
      intro h; exact two_pi_ne_zero ((cpow_eq_zero_iff _ _).1 h).1
    have hG : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos htpos
    have := hfe.symm
    simp only [mul_eq_zero, h2, hG, hζt, false_or, or_false] at this
    rcases this with h | h
    · exact absurd h hp
    · exact h
  obtain ⟨k, hk⟩ := (cos_pi_half_eq_zero_iff _).1 hcos
  have hsk : s = -2 * k := by linear_combination -hk
  have hre : s.re = -2 * k := by rw [hsk]; simp
  have hk0 : (0:ℝ) ≤ k := by linarith
  have hk0' : (0:ℤ) ≤ k := by exact_mod_cast hk0
  have hkne : k ≠ 0 := by rintro rfl; apply hs0; simp [hsk]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
  apply htriv
  refine ⟨n, ?_⟩
  rw [hsk, hn]; push_cast; ring

/-- **Mathlib's `RiemannHypothesis` is exactly "every nontrivial zero has `Re = 1/2`".**
This was the corpus's `Bridge` hypothesis (output71/72); it needs no hypothesis. -/
theorem riemannHypothesis_iff_strip :
    RiemannHypothesis ↔ ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re = 1/2 := by
  constructor
  · intro hRH ρ hρ
    refine hRH ρ hρ.1 ?_ (ne_one_of_re_lt_one hρ.2.2)
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    linarith [hρ.2.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  · intro h s hs htriv h1
    exact h s ⟨hs, in_strip_of_zero hs htriv h1⟩

/-- RH ⟺ the shifted spectrum is `⊆ {0}` (the corpus's "Spec ⊆ {0}" form). -/
theorem riemannHypothesis_iff_shifted_subset_zero :
    RiemannHypothesis ↔ ShiftedZeroSpectrum ⊆ {0} := by
  rw [riemannHypothesis_iff_strip]
  constructor
  · rintro h x ⟨ρ, hρ, rfl⟩
    simp [h ρ hρ]
  · intro h ρ hρ
    have := h ⟨ρ, hρ, rfl⟩
    simp at this
    linarith

/-- Every point of the shifted spectrum has `|x| < 1/2`. -/
theorem shifted_bounded {x : ℝ} (hx : x ∈ ShiftedZeroSpectrum) : |x| < 1/2 := by
  obtain ⟨ρ, hρ, rfl⟩ := hx
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hρ.2.1, hρ.2.2]

end MNF.RH

-- ═══════════════════════════════════════════════════════
-- AXIOM AUDIT  (expected: [propext, Classical.choice, Quot.sound] only)
-- ═══════════════════════════════════════════════════════
#print axioms MNF.RH.zeta_order_ge_one
#print axioms MNF.RH.order_one_iff_deriv
#print axioms MNF.RH.deriv_zero_of_high_order
#print axioms MNF.RH.nontrivial_zero_reflect
#print axioms MNF.RH.deriv_reflect
#print axioms MNF.RH.analyticOrderAt_reflect
#print axioms MNF.RH.zeta_order_reflect
#print axioms MNF.RH.shifted_symmetric
#print axioms MNF.RH.in_strip_of_zero
#print axioms MNF.RH.riemannHypothesis_iff_strip
#print axioms MNF.RH.riemannHypothesis_iff_shifted_subset_zero
#print axioms MNF.RH.shifted_bounded
