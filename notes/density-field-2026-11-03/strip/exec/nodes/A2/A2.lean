/-
A2.lean — node A2 of STRIP_PLAN (Density/Exponent.lean): the exponent arithmetic for the
single-window zero-density estimate.  Scratch file, 2026-11-03.

Everything here is pure real analysis (rpow / log / floor / ceil); nothing depends on ζ.

Parameters (the plan's single-window choice): with θ := (2σ₁−1)/(2σ₁) and κ := (2σ₁−1)²/(2σ₁)
  X = ⌊T^θ⌋₊,   N = ⌈T⌉₊ + 5,   η = E₀,   ε² = 1/X,
the W4 excess at these parameters is
  E₀ = A (1+log X)³ X^{1−2σ₁} + 26 B (1+log X)³ (N X)^{2−2σ₁} / T,
      A = 2 + 1/(2σ₁−1), B = 2 + 2/(2−2σ₁),
and the full A0 error (ε² = 1/X, a ≥ 3/2 already used) is
  Esingle = ½ (1/X + E) + π²/X,
  E = E₀(1+E₀) + E₀ + (1 + 1/E₀) · 2 M̄² ((2/3) N^{2−2σ₁} + C_G² N^{−2σ₁} T) / T,
  M̄ = 1 + X^{1−σ₁}/(1−σ₁).
Main result `exponent_single`: ∃ K T₀, 0 < K ∧ 8 ≤ T₀ ∧ ∀ T ≥ T₀,
  4 ≤ X ∧ X ≤ N ∧ Esingle σ₁ C_G T ≤ K (1 + log T)³ T^{−κ}.
Every term of Esingle is also bounded separately (`inv_X_le`, `E0gen_le`, `E0gen_le_const`,
`le_E0gen`, `cross_le`) so that node A1 can sum them itself if it prefers, and `w4_rhs_le`
is the algebra turning the W4 right-hand side (ℓ = T, η = E₀, a ≥ 3/2) into `T * (1 + E)`.

SCRATCH-ONLY DEFINITIONS (inline them in the final module; Comparator compares definition
bodies): `E0gen`, `Egen`, `Esingle`, `K1c`, `Ebarc`, `CMc`, `Ksingle`.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius
open MNF.RH

/-! ## DEFINITIONS (frozen block of STRIP_PLAN, copied verbatim) -/

/-- Möbius mollifier `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`. -/
noncomputable def Mx (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)
/-- the mollified zeta `f = ζ · M_X`. -/
noncomputable def fz (X : ℕ) (s : ℂ) : ℂ := riemannZeta s * Mx X s
/-- coefficient of `m^{-s}` in `S N · M_X`. -/
def cm (N X m : ℕ) : ℤ := ∑ d ∈ m.divisors.filter (· ≤ X), if m / d ≤ N then μ d else 0
/-- number of divisors of `m` that are `≤ X`. -/
def dX (X m : ℕ) : ℕ := (m.divisors.filter (· ≤ X)).card
/-- ε-majorant of `log ‖f‖` (replaces the tree's `Lz`, whose `1 +` kills every saving). -/
noncomputable def Leps (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ := (1 / 2) * Real.log (ε ^ 2 + ‖f z‖ ^ 2)
/-- zeros with `σ ≤ Re ρ`, `T₁ < Im ρ ≤ T₂`, with multiplicity (window form of `NRight`). -/
noncomputable def NSigma (σ T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ MNF.RH.zerosIn T₁ T₂ ∩ {ρ | σ ≤ ρ.re}, zeta_order ρ

/-! ## A2 — exponent arithmetic -/

section ExponentA2

/-! ### Scratch-only definitions (inline in the final module) -/

/-- SCRATCH-ONLY. The W4 excess `E₀` at mollifier length `X`, polynomial length `N`, window
length `T` (real parameters; A1 instantiates `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`, with `N * X` the
cast of the natural product). -/
noncomputable def E0gen (σ₁ X N T : ℝ) : ℝ :=
  (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁)
    + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁) / T

/-- SCRATCH-ONLY. The full A0 error at `η = E₀`, `ε² = 1/X`, `a ≥ 3/2` already used:
`½ (1/X + E) + π²/X` with `E = E₀(1+E₀) + E₀ + (1+1/E₀)·2M̄²((2/3)N^{2−2σ₁} + C_G²N^{−2σ₁}T)/T`. -/
noncomputable def Egen (σ₁ C_G X N T : ℝ) : ℝ :=
  (1 / 2) * (1 / X + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
    + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T))
  + Real.pi ^ 2 / X

/-- SCRATCH-ONLY. `Egen` at the single-window parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5`. -/
noncomputable def Esingle (σ₁ C_G T : ℝ) : ℝ :=
  Egen σ₁ C_G (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ((⌈T⌉₊ + 5 : ℕ) : ℝ) T

/-- SCRATCH-ONLY. The constant in `E₀ ≤ K1c (1+log T)³ T^{−κ}`. -/
noncomputable def K1c (σ₁ : ℝ) : ℝ := 2 * (2 + 1 / (2 * σ₁ - 1)) + 52 * (2 + 2 / (2 - 2 * σ₁))

/-- SCRATCH-ONLY. A uniform bound for `E₀` (logs beaten by `T^κ`). -/
noncomputable def Ebarc (σ₁ : ℝ) : ℝ := K1c σ₁ * (1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3

/-- SCRATCH-ONLY. `M̄² ≤ CMc · X^{2−2σ₁}`. -/
noncomputable def CMc (σ₁ : ℝ) : ℝ := (1 + 1 / (1 - σ₁)) ^ 2

/-- SCRATCH-ONLY. The final constant `K` of `exponent_single`. -/
noncomputable def Ksingle (σ₁ C_G : ℝ) : ℝ :=
  (1 / 2) * (2 + (2 + Ebarc σ₁) * K1c σ₁ + (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2))
    + 2 * Real.pi ^ 2

/-! ### The exponents θ = (2σ₁−1)/(2σ₁), κ = (2σ₁−1)²/(2σ₁) -/

lemma theta_pos {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : 0 < (2 * σ₁ - 1) / (2 * σ₁) :=
  div_pos (by linarith) (by linarith)

lemma theta_le_one {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : (2 * σ₁ - 1) / (2 * σ₁) ≤ 1 :=
  (div_le_one (by linarith)).2 (by linarith)

lemma kappa_pos {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) : 0 < (2 * σ₁ - 1) ^ 2 / (2 * σ₁) :=
  div_pos (pow_pos (by linarith) 2) (by linarith)

lemma kappa_le_theta {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) ≤ (2 * σ₁ - 1) / (2 * σ₁) := by
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

/-- `θ (1 − 2σ₁) = −κ`. -/
lemma theta_mul_eq {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) / (2 * σ₁) * (1 - 2 * σ₁) = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `(2 − 2σ₁) + θ (2 − 2σ₁) − 1 = −2κ` (the off-diagonal exponent). -/
lemma offdiag_exponent {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 - 2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) - 1
      = -(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `κ + θ (2 − 2σ₁) + (1 − 2σ₁) = −κ` (the cross-term exponent: the balance). -/
lemma cross_exponent {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) + (1 - 2 * σ₁)
      = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- `κ + θ (2 − 2σ₁) + (−2σ₁) = −κ − 1`. -/
lemma cross_exponent' {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) :
    (2 * σ₁ - 1) ^ 2 / (2 * σ₁) + (2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁) + (-2 * σ₁)
      = -((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1 := by
  have h2σ : (2 * σ₁) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Sanity: at `σ₁ = 3/4` the exponent `−κ` is `−1/6` (count `T^{5/6}`), and `θ = 1/3`. -/
example : -((2 * (3 / 4 : ℝ) - 1) ^ 2 / (2 * (3 / 4))) = -(1 / 6) := by norm_num
example : (2 * (3 / 4 : ℝ) - 1) / (2 * (3 / 4)) = 1 / 3 := by norm_num
example : 1 - (2 * (3 / 4 : ℝ) - 1) ^ 2 / (2 * (3 / 4)) = 5 / 6 := by norm_num

/-! ### Generic real helpers -/

/-- `⌊x⌋₊ ≥ x/2` for `x ≥ 2`. -/
lemma half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- `(x^a)^2 = x^(2a)` for `x ≥ 0`. -/
lemma rpow_sq_eq {x a : ℝ} (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- `2^e ≤ 2` for `e ≤ 1`. -/
lemma two_rpow_le_two {e : ℝ} (he : e ≤ 1) : (2 : ℝ) ^ e ≤ 2 := by
  calc (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one 2

/-- `(1 + log T)^3 ≤ (1 + 3/κ)^3 T^κ` for `T ≥ 1`, `κ > 0` (logs are beaten by any power). -/
lemma one_add_log_cube_le_rpow {T κ : ℝ} (hT : 1 ≤ T) (hκ : 0 < κ) :
    (1 + Real.log T) ^ 3 ≤ (1 + 3 / κ) ^ 3 * T ^ κ := by
  have hT0 : 0 < T := by linarith
  have hε : 0 < κ / 3 := by positivity
  have hlog : Real.log T ≤ T ^ (κ / 3) / (κ / 3) := Real.log_le_rpow_div hT0.le hε
  have hdiv : T ^ (κ / 3) / (κ / 3) = (3 / κ) * T ^ (κ / 3) := by
    rw [div_eq_mul_inv, inv_div]
    ring
  rw [hdiv] at hlog
  have h1 : 1 ≤ T ^ (κ / 3) := Real.one_le_rpow hT hε.le
  have hpos : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have h2 : 1 + Real.log T ≤ (1 + 3 / κ) * T ^ (κ / 3) := by linarith
  have h3 : (T ^ (κ / 3)) ^ 3 = T ^ κ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    congr 1
    push_cast
    ring
  calc (1 + Real.log T) ^ 3 ≤ ((1 + 3 / κ) * T ^ (κ / 3)) ^ 3 := pow_le_pow_left₀ hpos h2 3
    _ = (1 + 3 / κ) ^ 3 * (T ^ (κ / 3)) ^ 3 := by ring
    _ = (1 + 3 / κ) ^ 3 * T ^ κ := by rw [h3]

/-! ### The single-window parameters -/

/-- The parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5` for `T ≥ T₀ := max 8 (4^{1/θ})`:
`4 ≤ X ≤ N`, `T^θ/2 ≤ X ≤ T^θ`, `T ≤ N ≤ 2T`. -/
lemma single_params {σ₁ : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      8 ≤ T ∧
      4 ≤ ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ∧
      ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ≤ ⌈T⌉₊ + 5 ∧
      (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ∧
      T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) ∧
      T ≤ ((⌈T⌉₊ + 5 : ℕ) : ℝ) ∧ ((⌈T⌉₊ + 5 : ℕ) : ℝ) ≤ 2 * T := by
  have hθ0 := theta_pos hσ
  refine ⟨max 8 ((4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹), le_max_left _ _, fun T hT => ?_⟩
  have hT8 : 8 ≤ T := (le_max_left _ _).trans hT
  have hT4 : (4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹ ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hp4 : (4:ℝ) ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := by
    calc (4:ℝ) = ((4:ℝ) ^ ((2 * σ₁ - 1) / (2 * σ₁))⁻¹) ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          (Real.rpow_inv_rpow (by norm_num) hθ0.ne').symm
      _ ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hT4 hθ0.le
  have hpT : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T := by
    calc T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (theta_le_one hσ)
      _ = T := Real.rpow_one T
  have hp0 : 0 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_nonneg hT0.le _
  have hfl := Nat.floor_le hp0
  have hfl2 := half_le_nat_floor (by linarith : 2 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
  have hce := Nat.le_ceil T
  have hce2 := Nat.ceil_lt_add_one hT0.le
  refine ⟨hT8, ?_, ?_, hfl, by linarith, ?_, ?_⟩
  · exact Nat.le_floor (by exact_mod_cast hp4)
  · apply Nat.floor_le_of_le
    push_cast
    linarith
  · push_cast
    linarith
  · push_cast
    linarith

/-! ### Term bounds (real parameters `X N T` with the inequalities of `single_params`) -/

/-- `X^{1−2σ₁} ≤ 2 T^{−κ}` when `T^θ ≤ 2X`. -/
lemma X_rpow_le {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T) (_hX0 : 0 < X)
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) :
    X ^ (1 - 2 * σ₁) ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have hpk : (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (1 - 2 * σ₁)
      = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    rw [← Real.rpow_mul hT0.le, theta_mul_eq hσ]
  have h1 : X ^ (1 - 2 * σ₁) ≤ (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁)
      = (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (1 - 2 * σ₁) * (2:ℝ) ^ (2 * σ₁ - 1) := by
    rw [Real.div_rpow hp0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
      show -(1 - 2 * σ₁) = 2 * σ₁ - 1 by ring]
  have h3 : (2:ℝ) ^ (2 * σ₁ - 1) ≤ 2 := two_rpow_le_two (by linarith)
  calc X ^ (1 - 2 * σ₁) ≤ (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) ^ (1 - 2 * σ₁) := h1
    _ = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) * (2:ℝ) ^ (2 * σ₁ - 1) := by rw [h2, hpk]
    _ ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) * 2 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
    _ = 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring

/-- `T^{−κ} ≤ X^{1−2σ₁}` when `X ≤ T^θ`. -/
lemma rpow_le_X_rpow {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hT0 : 0 < T) (hX0 : 0 < X)
    (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) :
    T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ≤ X ^ (1 - 2 * σ₁) := by
  rw [← theta_mul_eq hσ, Real.rpow_mul hT0.le]
  exact Real.rpow_le_rpow_of_nonpos hX0 hXp (by linarith)

/-- `(N X)^{2−2σ₁} / T ≤ 2 T^{−κ}` (in fact `≤ 2 T^{−2κ}`) when `X ≤ T^θ`, `N ≤ 2T`. -/
lemma NX_rpow_div_le {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T)
    (hX0 : 0 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    (N * X) ^ (2 - 2 * σ₁) / T ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_nonneg hT0.le _
  have he : 0 ≤ 2 - 2 * σ₁ := by linarith
  have h1 : (N * X) ^ (2 - 2 * σ₁)
      ≤ (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) := by
    apply Real.rpow_le_rpow (mul_nonneg hN0 hX0) _ he
    calc N * X ≤ (2 * T) * T ^ ((2 * σ₁ - 1) / (2 * σ₁)) :=
          mul_le_mul hN2 hXp hX0 (by linarith)
      _ = 2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := by ring
  have h2 : (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁)
      = (2:ℝ) ^ (2 - 2 * σ₁) * T ^ (2 - 2 * σ₁)
          * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) := by
    rw [Real.mul_rpow (by linarith) hp0, Real.mul_rpow (by norm_num) hT0.le]
  have h3 : (2:ℝ) ^ (2 - 2 * σ₁) ≤ 2 := two_rpow_le_two (by linarith)
  have h4 : T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T
      = T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0, ← Real.rpow_sub_one hT0.ne',
      offdiag_exponent hσ]
  have h5 : T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
      ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    apply Real.rpow_le_rpow_of_exponent_le hT1
    have := kappa_pos hσ
    linarith
  have h6 : 0 ≤ T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hp0 _)) hT0.le
  calc (N * X) ^ (2 - 2 * σ₁) / T
      ≤ (2 * T * T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T :=
        div_le_div_of_nonneg_right h1 hT0.le
    _ = (2:ℝ) ^ (2 - 2 * σ₁)
        * (T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T) := by
        rw [h2]; ring
    _ ≤ 2 * (T ^ (2 - 2 * σ₁) * (T ^ ((2 * σ₁ - 1) / (2 * σ₁))) ^ (2 - 2 * σ₁) / T) :=
        mul_le_mul_of_nonneg_right h3 h6
    _ = 2 * T ^ (-(2 * ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by rw [h4]
    _ ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by linarith

/-- `1/X ≤ 2 T^{−κ}` (in fact `≤ 2 T^{−θ}`) when `T^θ ≤ 2X`. -/
lemma inv_X_le {σ₁ T X : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT1 : 1 ≤ T) (_hX0 : 0 < X)
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) :
    1 / X ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < T ^ ((2 * σ₁ - 1) / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have h1 : 1 / X ≤ 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) = 2 * T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) := by
    rw [Real.rpow_neg hT0.le, one_div_div, div_eq_mul_inv]
  have h3 : T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith [kappa_le_theta hσ hσ'])
  calc 1 / X ≤ 1 / (T ^ ((2 * σ₁ - 1) / (2 * σ₁)) / 2) := h1
    _ = 2 * T ^ (-((2 * σ₁ - 1) / (2 * σ₁))) := h2
    _ ≤ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by linarith

/-- The diagonal/off-diagonal excess: `E₀ ≤ K1c (1 + log T)³ T^{−κ}`. -/
lemma E0gen_le {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    E0gen σ₁ X N T
      ≤ K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hXT : X ≤ T := hXp.trans (by
    calc T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ T ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (theta_le_one hσ)
      _ = T := Real.rpow_one T)
  have hL0 : 0 ≤ 1 + Real.log X := by linarith [Real.log_nonneg hX1]
  have hLT0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hLT3 : 0 ≤ (1 + Real.log T) ^ 3 := pow_nonneg hLT0 3
  have hL : (1 + Real.log X) ^ 3 ≤ (1 + Real.log T) ^ 3 :=
    pow_le_pow_left₀ hL0 (by linarith [Real.log_le_log hX0 hXT]) 3
  have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
    have : 0 < 2 * σ₁ - 1 := by linarith
    positivity
  have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
    have : 0 < 2 - 2 * σ₁ := by linarith
    positivity
  have h1 := X_rpow_le hσ hσ' hT1 hX0 hpX
  have h2 := NX_rpow_div_le hσ hσ' hT1 hX0.le hXp hN0 hN2
  calc E0gen σ₁ X N T
      = (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁)
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
          * ((N * X) ^ (2 - 2 * σ₁) / T) := by
        unfold E0gen; ring
    _ ≤ (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log T) ^ 3
          * (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
        + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log T) ^ 3
          * (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hL hA) h1 (Real.rpow_nonneg hX0.le _)
            (mul_nonneg hA hLT3)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hB)) h2
            (div_nonneg (Real.rpow_nonneg (mul_nonneg hN0 hX0.le) _) hT0.le)
            (mul_nonneg (mul_nonneg (by norm_num) hB) hLT3)
    _ = K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
        unfold K1c; ring

/-- Lower bound `2 T^{−κ} ≤ E₀` (so `E₀ > 0`, and `1/η = 1/E₀ ≤ T^κ/2`). -/
lemma le_E0gen {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT0 : 0 < T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) :
    2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ≤ E0gen σ₁ X N T := by
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ (1 + Real.log X) ^ 3 := one_le_pow₀ (by linarith [Real.log_nonneg hX1])
  have hA : 2 ≤ 2 + 1 / (2 * σ₁ - 1) := by
    have : 0 < 2 * σ₁ - 1 := by linarith
    have : 0 < 1 / (2 * σ₁ - 1) := by positivity
    linarith
  have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
    have : 0 < 2 - 2 * σ₁ := by linarith
    positivity
  have h1 := rpow_le_X_rpow hσ hT0 hX0 hXp
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hsecond : 0 ≤ 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3
      * (N * X) ^ (2 - 2 * σ₁) / T := by
    apply div_nonneg _ hT0.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith))
      (Real.rpow_nonneg (mul_nonneg hN0 hX0.le) _)
  have hfirst : 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
      ≤ (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁) := by
    calc 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
        = (2 * 1) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring
      _ ≤ ((2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3) * X ^ (1 - 2 * σ₁) :=
          mul_le_mul (mul_le_mul hA hL1 (by norm_num) (by linarith)) h1 hk0
            (mul_nonneg (by linarith) (by linarith))
  unfold E0gen
  linarith

/-- A uniform bound: `E₀ ≤ Ebarc` for all `T ≥ 8` (the logs are beaten by `T^κ`). -/
lemma E0gen_le_const {σ₁ T X N : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hN0 : 0 ≤ N) (hN2 : N ≤ 2 * T) :
    E0gen σ₁ X N T ≤ Ebarc σ₁ := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hκ := kappa_pos hσ
  have h := E0gen_le hσ hσ' hT hX1 hXp hpX hN0 hN2
  have hlog := one_add_log_cube_le_rpow hT1 hκ
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hTk : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) = 1 := by
    rw [← Real.rpow_add hT0]
    simp
  calc E0gen σ₁ X N T
      ≤ K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := h
    _ ≤ K1c σ₁ * ((1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3 * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hK1) hk0
    _ = K1c σ₁ * (1 + 3 / ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) ^ 3
          * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        ring
    _ = Ebarc σ₁ := by rw [hTk, mul_one]; rfl

/-- The cross term `(1 + 1/E₀)·2M̄²((2/3)N^{2−2σ₁} + C_G²N^{−2σ₁}T)/T ≤ (4 CMc + 3 CMc C_G²) T^{−κ}`:
this is the term that fixes the balance `X = T^{(2σ₁−1)/(2σ₁)}`. -/
lemma cross_le {σ₁ T X N C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hTN : T ≤ N) (hN2 : N ≤ 2 * T)
    (_hCG : 0 ≤ C_G) :
    (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      ≤ (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have h1σ : 0 < 1 - σ₁ := by linarith
  have hκ0 : 0 < (2 * σ₁ - 1) ^ 2 / (2 * σ₁) := kappa_pos hσ
  have hTκ : 0 < T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := Real.rpow_pos_of_pos hT0 _
  have hTκ1 : 1 ≤ T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := Real.one_le_rpow hT1 hκ0.le
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hk0' : 0 < T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_pos_of_pos hT0 _
  -- (a) `1 + 1/E₀ ≤ (3/2) T^κ`
  have hE := le_E0gen hσ hσ' hT0 hX1 hXp hN0.le
  have hE0 : 0 < E0gen σ₁ X N T := lt_of_lt_of_le (by linarith) hE
  have ha : 1 + 1 / E0gen σ₁ X N T ≤ (3 / 2) * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) := by
    have h := one_div_le_one_div_of_le (by linarith : 0 < 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) hE
    have h' : 1 / (2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
        = T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) / 2 := by
      rw [Real.rpow_neg hT0.le, one_div, mul_inv, inv_inv]
      ring
    rw [h'] at h
    linarith
  -- (b) `M̄² ≤ CMc · T^{θ(2−2σ₁)}`
  have hXσ : 1 ≤ X ^ (1 - σ₁) := Real.one_le_rpow hX1 h1σ.le
  have hM : 1 + X ^ (1 - σ₁) / (1 - σ₁) ≤ (1 + 1 / (1 - σ₁)) * X ^ (1 - σ₁) := by
    have : X ^ (1 - σ₁) / (1 - σ₁) = (1 / (1 - σ₁)) * X ^ (1 - σ₁) := by ring
    rw [this]
    nlinarith
  have hM0 : 0 ≤ 1 + X ^ (1 - σ₁) / (1 - σ₁) := by
    have := div_nonneg (Real.rpow_nonneg hX0.le (1 - σ₁)) h1σ.le
    linarith
  have hb : (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
      ≤ CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) := by
    calc (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2 ≤ ((1 + 1 / (1 - σ₁)) * X ^ (1 - σ₁)) ^ 2 :=
          pow_le_pow_left₀ hM0 hM 2
      _ = CMc σ₁ * X ^ (2 - 2 * σ₁) := by
          rw [mul_pow, rpow_sq_eq hX0.le, show 2 * (1 - σ₁) = 2 - 2 * σ₁ by ring]
          rfl
      _ ≤ CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [Real.rpow_mul hT0.le]
          exact Real.rpow_le_rpow hX0.le hXp (by linarith)
  -- (c) `((2/3) N^{2−2σ₁} + C_G² N^{−2σ₁} T)/T ≤ (4/3) T^{1−2σ₁} + C_G² T^{−2σ₁}`
  have hN1 : N ^ (2 - 2 * σ₁) ≤ 2 * T ^ (2 - 2 * σ₁) := by
    calc N ^ (2 - 2 * σ₁) ≤ (2 * T) ^ (2 - 2 * σ₁) :=
          Real.rpow_le_rpow hN0.le hN2 (by linarith)
      _ = (2:ℝ) ^ (2 - 2 * σ₁) * T ^ (2 - 2 * σ₁) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 * T ^ (2 - 2 * σ₁) :=
          mul_le_mul_of_nonneg_right (two_rpow_le_two (by linarith)) (Real.rpow_nonneg hT0.le _)
  have hN2' : N ^ (-2 * σ₁) ≤ T ^ (-2 * σ₁) :=
    Real.rpow_le_rpow_of_nonpos hT0 hTN (by linarith)
  have hc : ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T) / T
      ≤ (4 / 3) * T ^ (1 - 2 * σ₁) + C_G ^ 2 * T ^ (-2 * σ₁) := by
    rw [add_div]
    have e1 : (2 / 3) * N ^ (2 - 2 * σ₁) / T ≤ (4 / 3) * T ^ (1 - 2 * σ₁) := by
      have : T ^ (1 - 2 * σ₁) = T ^ (2 - 2 * σ₁) / T := by
        rw [← Real.rpow_sub_one hT0.ne']
        congr 1
        ring
      rw [this]
      calc (2 / 3) * N ^ (2 - 2 * σ₁) / T ≤ (2 / 3) * (2 * T ^ (2 - 2 * σ₁)) / T :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN1 (by norm_num)) hT0.le
        _ = (4 / 3) * (T ^ (2 - 2 * σ₁) / T) := by ring
    have e2 : C_G ^ 2 * N ^ (-2 * σ₁) * T / T ≤ C_G ^ 2 * T ^ (-2 * σ₁) := by
      rw [mul_div_assoc, div_self hT0.ne', mul_one]
      exact mul_le_mul_of_nonneg_left hN2' (sq_nonneg _)
    linarith
  -- combine
  have hcross0 : 0 ≤ (2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T :=
    add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0.le _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hN0.le _)) hT0.le)
  have key1 : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))
      * T ^ (1 - 2 * σ₁) = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, cross_exponent hσ]
  have key2 : T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))
      * T ^ (-2 * σ₁) = T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, cross_exponent' hσ]
  have key3 : T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1) ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hE1 : 0 ≤ 1 + 1 / E0gen σ₁ X N T := by positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  calc (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      = (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2)
        * (((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T) / T) := by ring
    _ ≤ ((3 / 2) * T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
        * (2 * (CMc σ₁ * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁))))
        * ((4 / 3) * T ^ (1 - 2 * σ₁) + C_G ^ 2 * T ^ (-2 * σ₁)) := by
        apply mul_le_mul (mul_le_mul ha (by linarith [hb]) (by positivity)
          (mul_nonneg (by norm_num) hTκ.le)) hc (div_nonneg hcross0 hT0.le)
        exact mul_nonneg (mul_nonneg (by norm_num) hTκ.le)
          (mul_nonneg (by norm_num) (mul_nonneg hCM0 (Real.rpow_nonneg hT0.le _)))
    _ = 3 * CMc σ₁ * ((4 / 3) * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))
            * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) * T ^ (1 - 2 * σ₁))
          + C_G ^ 2 * (T ^ ((2 * σ₁ - 1) ^ 2 / (2 * σ₁))
            * T ^ ((2 * σ₁ - 1) / (2 * σ₁) * (2 - 2 * σ₁)) * T ^ (-2 * σ₁))) := by ring
    _ = 3 * CMc σ₁ * ((4 / 3) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          + C_G ^ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)) - 1)) := by rw [key1, key2]
    _ ≤ 3 * CMc σ₁ * ((4 / 3) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
          + C_G ^ 2 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCM0)
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left key3 (sq_nonneg _)
    _ = (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2) * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by ring

/-- The assembled bound on `Egen` with real parameters. -/
lemma Egen_le {σ₁ T X N C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT : 8 ≤ T)
    (hX4 : 4 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁)))
    (hpX : T ^ ((2 * σ₁ - 1) / (2 * σ₁)) ≤ 2 * X) (hTN : T ≤ N) (hN2 : N ≤ 2 * T)
    (hCG : 0 ≤ C_G) :
    Egen σ₁ C_G X N T
      ≤ Ksingle σ₁ C_G * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 ≤ T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := Real.rpow_nonneg hT0.le _
  have hLT1 : 1 ≤ (1 + Real.log T) ^ 3 := one_le_pow₀ (by linarith [Real.log_nonneg hT1])
  -- `T^{−κ} ≤ (1 + log T)³ T^{−κ}`
  have hQ : T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))
      ≤ (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    le_mul_of_one_le_left hk0 hLT1
  have hQ0 : 0 ≤ (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) :=
    mul_nonneg (by linarith) hk0
  have h_inv := inv_X_le hσ hσ' hT1 hX0 hpX
  have h_E0 := E0gen_le hσ hσ' hT hX1 hXp hpX hN0 hN2
  have h_E0c := E0gen_le_const hσ hσ' hT hX1 hXp hpX hN0 hN2
  have h_E0ge := le_E0gen hσ hσ' hT0 hX1 hXp hN0
  have h_E0nn : 0 ≤ E0gen σ₁ X N T := by linarith
  have h_cross := cross_le hσ hσ' hT hX1 hXp hTN hN2 hCG
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hEb : 0 ≤ Ebarc σ₁ := by
    have := kappa_pos hσ
    unfold Ebarc
    positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  -- each term against `Q := (1 + log T)³ T^{−κ}`
  have h_inv' : 1 / X ≤ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) :=
    h_inv.trans (by linarith)
  have h_quad : E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
      ≤ (2 + Ebarc σ₁) * K1c σ₁
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    calc E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
        = E0gen σ₁ X N T * (2 + E0gen σ₁ X N T) := by ring
      _ ≤ E0gen σ₁ X N T * (2 + Ebarc σ₁) := by
          apply mul_le_mul_of_nonneg_left _ h_E0nn
          linarith
      _ ≤ (K1c σ₁ * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
            * (2 + Ebarc σ₁) :=
          mul_le_mul_of_nonneg_right h_E0 (by linarith)
      _ = (2 + Ebarc σ₁) * K1c σ₁
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by ring
  have h_cross' : (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
        * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T
      ≤ (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2)
          * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) :=
    h_cross.trans (mul_le_mul_of_nonneg_left hQ
      (add_nonneg (mul_nonneg (by norm_num) hCM0)
        (mul_nonneg (mul_nonneg (by norm_num) hCM0) (sq_nonneg _))))
  have h_pi : Real.pi ^ 2 / X
      ≤ 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
    calc Real.pi ^ 2 / X = Real.pi ^ 2 * (1 / X) := by ring
      _ ≤ Real.pi ^ 2 * (2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))) :=
          mul_le_mul_of_nonneg_left h_inv' (sq_nonneg _)
      _ = 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
          ring
  calc Egen σ₁ C_G X N T
      = (1 / 2) * (1 / X + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
          + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
            * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T))
        + Real.pi ^ 2 / X := rfl
    _ ≤ (1 / 2) * (2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
          + ((2 + Ebarc σ₁) * K1c σ₁
              * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))
            + (4 * CMc σ₁ + 3 * CMc σ₁ * C_G ^ 2)
              * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))))))
        + 2 * Real.pi ^ 2 * ((1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))) := by
        apply add_le_add _ h_pi
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h_inv' (add_le_add h_quad h_cross')
    _ = Ksingle σ₁ C_G * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
        unfold Ksingle
        ring

/-- `Ksingle > 0`. -/
lemma Ksingle_pos {σ₁ C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) : 0 < Ksingle σ₁ C_G := by
  have hK1 : 0 ≤ K1c σ₁ := by
    have hA : 0 ≤ 2 + 1 / (2 * σ₁ - 1) := by
      have : 0 < 2 * σ₁ - 1 := by linarith
      positivity
    have hB : 0 ≤ 2 + 2 / (2 - 2 * σ₁) := by
      have : 0 < 2 - 2 * σ₁ := by linarith
      positivity
    unfold K1c
    linarith
  have hEb : 0 ≤ Ebarc σ₁ := by
    have := kappa_pos hσ
    unfold Ebarc
    positivity
  have hCM0 : 0 ≤ CMc σ₁ := sq_nonneg _
  have h1 : 0 ≤ (2 + Ebarc σ₁) * K1c σ₁ := mul_nonneg (by linarith) hK1
  have h2 : 0 ≤ CMc σ₁ * C_G ^ 2 := mul_nonneg hCM0 (sq_nonneg _)
  have h3 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  unfold Ksingle
  nlinarith

/-! ### The main statement (plan item A2) -/

/-- **A2.** The exponent arithmetic for the single-window estimate: with
`X = ⌊T^{(2σ₁−1)/(2σ₁)}⌋₊`, `N = ⌈T⌉₊ + 5`, for `T ≥ T₀` one has `4 ≤ X ≤ N` and the A0 error
`Esingle σ₁ C_G T` (see the file header) is `≤ K (1 + log T)³ T^{−(2σ₁−1)²/(2σ₁)}`.
`C_G ≥ 0` is the free constant of the approximate formula; `K` depends on `σ₁, C_G`, `T₀` only
on `σ₁`. -/
theorem exponent_single {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) {C_G : ℝ} (hCG : 0 ≤ C_G) :
    ∃ K T₀ : ℝ, 0 < K ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (4 ≤ ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊) ∧
      (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ≤ ⌈T⌉₊ + 5) ∧
      Esingle σ₁ C_G T ≤ K * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))) := by
  obtain ⟨T₀, hT₀, hall⟩ := single_params h1 h1'
  refine ⟨Ksingle σ₁ C_G, T₀, Ksingle_pos h1 h1', hT₀, fun T hT => ?_⟩
  obtain ⟨hT8, hX4, hXN, hXp, hpX, hTN, hN2⟩ := hall T hT
  refine ⟨hX4, hXN, ?_⟩
  have hX4' : (4:ℝ) ≤ (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ : ℝ) := by exact_mod_cast hX4
  exact Egen_le h1 h1' hT8 hX4' hXp hpX hTN hN2 hCG

/-! ### Glue for A1: the W4 right-hand side is `T * (1 + E)` -/

/-- The W4 right-hand side at `ℓ = T`, `η = E₀ = E0gen σ₁ X N T`, any `a ≥ 3/2`, is at most
`T * (1 + E)` with `E` the `a`-free excess inside `Egen` (so `hMS` of A0 holds with this `E`,
uniformly in `a ∈ [3/2, 9/2]` and in `σ`). -/
lemma w4_rhs_le {σ₁ T X N a C_G : ℝ} (hσ : 1 / 2 < σ₁) (hσ' : σ₁ < 1) (hT0 : 0 < T)
    (hX1 : 1 ≤ X) (hXp : X ≤ T ^ ((2 * σ₁ - 1) / (2 * σ₁))) (hN0 : 0 ≤ N) (ha : 3 / 2 ≤ a) :
    (1 + E0gen σ₁ X N T)
        * (T * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁))
      + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T))
    ≤ T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T
        + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T)) := by
  have hX0 : 0 < X := by linarith
  have hE := le_E0gen hσ hσ' hT0 hX1 hXp hN0
  have hE0 : 0 < E0gen σ₁ X N T :=
    lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hT0 (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁))); linarith) hE
  have hE1 : 0 ≤ 1 + 1 / E0gen σ₁ X N T := by positivity
  have hfirst : (1 + E0gen σ₁ X N T)
        * (T * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * X ^ (1 - 2 * σ₁))
          + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * (N * X) ^ (2 - 2 * σ₁))
      = T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T)) := by
    have hT' : T ≠ 0 := hT0.ne'
    unfold E0gen
    field_simp
    ring
  have hNpow : 0 ≤ N ^ (2 - 2 * σ₁) := Real.rpow_nonneg hN0 _
  have hdiv : N ^ (2 - 2 * σ₁) / a ≤ (2 / 3) * N ^ (2 - 2 * σ₁) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hNpow (sub_nonneg.2 ha)]
  have hsecond : (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T))
      ≤ (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by
    apply mul_le_mul_of_nonneg_left _ hE1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add_left hdiv _
  have hT' : T * ((1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T)
      = (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by
    rw [mul_div_assoc', mul_comm T, mul_div_assoc, div_self hT0.ne', mul_one]
  calc _ = T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T))
        + (1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * (N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * N ^ (-2 * σ₁) * T)) := by rw [hfirst]
    _ ≤ T * (1 + (E0gen σ₁ X N T * (1 + E0gen σ₁ X N T) + E0gen σ₁ X N T))
        + T * ((1 + 1 / E0gen σ₁ X N T) * (2 * (1 + X ^ (1 - σ₁) / (1 - σ₁)) ^ 2
          * ((2 / 3) * N ^ (2 - 2 * σ₁) + C_G ^ 2 * N ^ (-2 * σ₁) * T)) / T) := by
        rw [hT']
        exact add_le_add_right hsecond _
    _ = _ := by ring

end ExponentA2

end Zeta23.Density
