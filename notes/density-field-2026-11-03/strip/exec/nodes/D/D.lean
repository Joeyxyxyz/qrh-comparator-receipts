/-
D.lean — STRIP_PLAN node D (Density/Abel.lean): partial-summation lemmas with generic
nonnegative weights `w` whose partial sums satisfy `∑_{m ≤ Y} w m ≤ Y·L`.

  D0  `sum_mul_le_of_partial_sums`      : ∑_{m≤M} w m g m ≤ L ∑_{m≤M} g m          (g ≥ 0 antitone)
  D0' `sum_mul_le_of_partial_sums_tail` : ∑_{X<m≤M} w m g m ≤ L((X+1) g(X+1) + ∑_{X<m≤M} g m)
  D1  `tail_sum_le`                     : ∑_{X<m≤M} w m m^{-2σ} ≤ (2 + 1/(2σ−1)) L X^{1−2σ}
  D2  `weight_sum_le`                   : ∑_{m≤M} (m+1) w m m^{-2σ} ≤ (2 + 2/(2−2σ)) L M^{2−2σ}

D0 is proved by induction on `M` through the strengthened Abel-type invariant
  ∑_{m≤M} w m g m + (M L − W(M)) g M ≤ L ∑_{m≤M} g m,   W(M) := ∑_{m≤M} w m.
D0' follows from D0 applied to the antitone majorant `g̃ m = g (X+1)` (m ≤ X), `g m` (m > X).
D1 uses D0' with `g m = m^{-2σ}` and the integral comparison `∑_{X<m≤M} m^{-2σ} ≤ X^{1−2σ}/(2σ−1)`.
D2 uses D0 with `g m = (m+1) m^{-2σ}` (patched to `2` at m = 0 so that it is antitone on ℕ) and
the tree's `M1.sum_weight_le_logfree`.
-/
import Zeta23.BL.BohrLandauClosure

namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius
open MNF.RH

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

/-! ### D0: Abel summation with generic weights -/

set_option linter.unusedVariables false in
/-- D0. Partial summation: if `0 ≤ w`, `∑_{m ≤ Y} w m ≤ Y L` for every `Y`, and `g ≥ 0` is
antitone, then `∑_{m ≤ M} w m g m ≤ L ∑_{m ≤ M} g m`. -/
theorem sum_mul_le_of_partial_sums {w g : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) (hg : ∀ m, 0 ≤ g m) (hanti : Antitone g)
    (M : ℕ) : ∑ m ∈ Icc 1 M, w m * g m ≤ L * ∑ m ∈ Icc 1 M, g m := by
  -- strengthened invariant: the slack `(M L − W(M)) g M` is carried along
  have key : ∀ M : ℕ, ∑ m ∈ Icc 1 M, w m * g m + ((M:ℝ) * L - ∑ m ∈ Icc 1 M, w m) * g M
      ≤ L * ∑ m ∈ Icc 1 M, g m := by
    intro M
    induction M with
    | zero =>
      simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, Nat.cast_zero,
        zero_mul, sub_zero, add_zero, mul_zero, le_refl]
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 : g (M + 1) ≤ g M := hanti (Nat.le_succ M)
      have h2 : 0 ≤ (M:ℝ) * L - ∑ m ∈ Icc 1 M, w m := sub_nonneg.mpr (hW M)
      have h3 := hg (M + 1)
      have h4 := mul_le_mul_of_nonneg_left h1 h2
      push_cast
      nlinarith [h4, ih, h3, hL]
  have h := key M
  have h2 : 0 ≤ (M:ℝ) * L - ∑ m ∈ Icc 1 M, w m := sub_nonneg.mpr (hW M)
  have h3 := mul_nonneg h2 (hg M)
  linarith

/-- D0'. Tail version of D0 (start at `X`): the price of starting late is the single term
`(X+1) g (X+1)`. -/
theorem sum_mul_le_of_partial_sums_tail {w g : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) (hg : ∀ m, 0 ≤ g m) (hanti : Antitone g)
    (X M : ℕ) :
    ∑ m ∈ Ioc X M, w m * g m ≤ L * ((X + 1) * g (X + 1) + ∑ m ∈ Ioc X M, g m) := by
  have hLg : 0 ≤ L * (((X:ℝ) + 1) * g (X + 1)) :=
    mul_nonneg hL (mul_nonneg (by positivity) (hg _))
  rcases lt_or_ge M X with hMX | hXM
  · rw [Finset.Ioc_eq_empty_of_le hMX.le, Finset.sum_empty, Finset.sum_empty, add_zero]
    exact hLg
  · -- antitone majorant: constant `g (X+1)` up to `X`, then `g`
    set g' : ℕ → ℝ := fun m => if m ≤ X then g (X + 1) else g m with hg'_def
    have hg' : ∀ m, 0 ≤ g' m := by
      intro m
      simp only [hg'_def]
      split_ifs <;> exact hg _
    have hanti' : Antitone g' := by
      intro a b hab
      simp only [hg'_def]
      by_cases ha : a ≤ X
      · by_cases hb : b ≤ X
        · rw [if_pos ha, if_pos hb]
        · rw [if_pos ha, if_neg hb]
          exact hanti (by omega)
      · have hb : ¬ b ≤ X := by omega
        rw [if_neg ha, if_neg hb]
        exact hanti hab
    have h0 := sum_mul_le_of_partial_sums hw hL hW hg' hanti' M
    have eIcc : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => Finset.Icc_add_one_left_eq_Ioc 0 n
    have hsplit : ∀ f : ℕ → ℝ,
        ∑ m ∈ Icc 1 M, f m = ∑ m ∈ Icc 1 X, f m + ∑ m ∈ Ioc X M, f m := by
      intro f
      rw [eIcc M, eIcc X, Finset.sum_Ioc_consecutive f (Nat.zero_le X) hXM]
    have e1 : ∑ m ∈ Icc 1 M, w m * g' m
        = ∑ m ∈ Icc 1 X, w m * g (X + 1) + ∑ m ∈ Ioc X M, w m * g m := by
      rw [hsplit]
      congr 1
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_pos (Finset.mem_Icc.mp hm).2]
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_neg (not_le.mpr (Finset.mem_Ioc.mp hm).1)]
    have e2 : ∑ m ∈ Icc 1 M, g' m = (X:ℝ) * g (X + 1) + ∑ m ∈ Ioc X M, g m := by
      rw [hsplit]
      congr 1
      · calc ∑ m ∈ Icc 1 X, g' m = ∑ m ∈ Icc 1 X, g (X + 1) :=
              Finset.sum_congr rfl (fun m hm => by
                simp only [hg'_def, if_pos (Finset.mem_Icc.mp hm).2])
          _ = (X:ℝ) * g (X + 1) := by simp [Finset.sum_const, Nat.card_Icc]
      · refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [hg'_def, if_neg (not_le.mpr (Finset.mem_Ioc.mp hm).1)]
    have h3 : 0 ≤ ∑ m ∈ Icc 1 X, w m * g (X + 1) :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hw m) (hg _))
    rw [e1, e2] at h0
    have h4 : 0 ≤ L * g (X + 1) := mul_nonneg hL (hg _)
    nlinarith [h0, h3, h4]

/-! ### D1: the tail `∑_{m > X} w m m^{-2σ}` -/

/-- Integral comparison for the tail: `∑_{X < m ≤ M} m^{-2σ} ≤ X^{1-2σ}/(2σ-1)` for `σ > 1/2`,
`1 ≤ X ≤ M`. -/
theorem sum_Ioc_rpow_le {X M : ℕ} (hX : 1 ≤ X) (hXM : X ≤ M) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) ≤ (X:ℝ) ^ (1 - 2 * σ) / (2 * σ - 1) := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-2 * σ)) (Set.Icc (X:ℝ) (M:ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono ?_
    intro x hx
    exact Set.mem_Ioi.mpr (by linarith [hx.1])
  have hint := AntitoneOn.sum_le_integral_Ico hXM hanti
  have hsum : ∑ i ∈ Ico X M, (((i + 1 : ℕ) : ℝ)) ^ (-2 * σ)
      = ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) := by
    rw [Finset.sum_Ico_add' (fun x : ℕ => (x:ℝ) ^ (-2 * σ)) X M 1,
      Finset.Ico_add_one_add_one_eq_Ioc]
  rw [hsum] at hint
  refine le_trans hint ?_
  have hne : -2 * σ ≠ -1 := by intro h; linarith
  have hnot : (0:ℝ) ∉ Set.uIcc (X:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hXM)]
    intro h
    have := (Set.mem_Icc.mp h).1
    linarith
  rw [integral_rpow (Or.inr ⟨hne, hnot⟩)]
  rw [show (-2 * σ + 1) = -(2 * σ - 1) by ring, show (1 - 2 * σ) = -(2 * σ - 1) by ring,
    div_neg, ← neg_div, neg_sub]
  have hM0 : 0 ≤ (M:ℝ) ^ (-(2 * σ - 1)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- D1. Tail of the weighted sum against `m^{-2σ}`:
`∑_{X < m ≤ M} w m m^{-2σ} ≤ (2 + 1/(2σ-1)) L X^{1-2σ}`. -/
theorem tail_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) {X M : ℕ}
    (hX : 1 ≤ X) :
    ∑ m ∈ Ioc X M, w m * (m : ℝ) ^ (-2 * σ)
      ≤ (2 + 1 / (2 * σ - 1)) * L * (X : ℝ) ^ (1 - 2 * σ) := by
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hXpow : 0 ≤ (X:ℝ) ^ (1 - 2 * σ) := Real.rpow_nonneg hX0.le _
  have hC : 0 ≤ 2 + 1 / (2 * σ - 1) := by positivity
  rcases le_or_gt M X with hMX | hXM
  · rw [Finset.Ioc_eq_empty_of_le hMX, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hC hL) hXpow
  · -- `g m = m^{-2σ}`, patched to `1` at `m = 0` (Mathlib's `0 ^ (-2σ) = 0` would break
    -- antitonicity on `ℕ`); on `Ioc X M` and at `X + 1` it agrees with `m^{-2σ}` since `1 ≤ X`
    set g : ℕ → ℝ := fun m => if m = 0 then 1 else (m:ℝ) ^ (-2 * σ) with hg_def
    have hg : ∀ m, 0 ≤ g m := by
      intro m
      simp only [hg_def]
      split_ifs
      · norm_num
      · exact Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hanti : Antitone g := by
      intro a b hab
      simp only [hg_def]
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb
          exact le_rfl
        · rw [if_pos rfl, if_neg (by omega)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb) (by linarith)
      · have hb : 0 < b := lt_of_lt_of_le ha hab
        rw [if_neg (by omega), if_neg (by omega)]
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha) (by exact_mod_cast hab)
          (by linarith)
    have h0 := sum_mul_le_of_partial_sums_tail hw hL hW hg hanti X M
    have eg : ∀ m ∈ Ioc X M, g m = (m:ℝ) ^ (-2 * σ) := by
      intro m hm
      have : 0 < m := lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hm).1
      simp only [hg_def, if_neg (show m ≠ 0 by omega)]
    have eg1 : g (X + 1) = ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) := by
      simp only [hg_def, if_neg (show X + 1 ≠ 0 by omega)]
    have e1 : ∑ m ∈ Ioc X M, w m * g m = ∑ m ∈ Ioc X M, w m * (m:ℝ) ^ (-2 * σ) :=
      Finset.sum_congr rfl (fun m hm => by rw [eg m hm])
    have e2 : ∑ m ∈ Ioc X M, g m = ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ) :=
      Finset.sum_congr rfl (fun m hm => eg m hm)
    rw [e1, e2, eg1] at h0
    have h1 := sum_Ioc_rpow_le hX hXM.le hσ
    have h2 : ((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) ≤ (X:ℝ) ^ (1 - 2 * σ) := by
      have hX1 : (0:ℝ) < (X:ℝ) + 1 := by linarith
      have e : ((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ) = ((X:ℝ) + 1) ^ (1 - 2 * σ) := by
        push_cast
        rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add_one hX1.ne', mul_comm]
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos hX0 (by linarith) (by linarith)
    have hLP : 0 ≤ L * (X:ℝ) ^ (1 - 2 * σ) := mul_nonneg hL hXpow
    calc ∑ m ∈ Ioc X M, w m * (m:ℝ) ^ (-2 * σ)
        ≤ L * (((X:ℝ) + 1) * ((X + 1 : ℕ) : ℝ) ^ (-2 * σ)
            + ∑ m ∈ Ioc X M, (m:ℝ) ^ (-2 * σ)) := h0
      _ ≤ L * ((X:ℝ) ^ (1 - 2 * σ) + (X:ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h1) hL
      _ = (1 + 1 / (2 * σ - 1)) * L * (X:ℝ) ^ (1 - 2 * σ) := by ring
      _ ≤ (2 + 1 / (2 * σ - 1)) * L * (X:ℝ) ^ (1 - 2 * σ) := by nlinarith [hLP]

/-! ### D2: the off-diagonal weight `(m+1) m^{-2σ}` -/

/-- D2. Weighted off-diagonal sum:
`∑_{m ≤ M} (m+1) w m m^{-2σ} ≤ (2 + 2/(2-2σ)) L M^{2-2σ}` for `1/2 < σ < 1`, `1 ≤ M`. -/
theorem weight_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (w m * (m : ℝ) ^ (-2 * σ))
      ≤ (2 + 2 / (2 - 2 * σ)) * L * (M : ℝ) ^ (2 - 2 * σ) := by
  -- `g m = (m+1) m^{-2σ}`, patched at `m = 0` so that it is antitone on all of `ℕ`
  set g : ℕ → ℝ := fun m => if m = 0 then 2 else ((m:ℝ) + 1) * (m:ℝ) ^ (-2 * σ) with hg_def
  have hterm : ∀ m : ℕ, 0 < m →
      ((m:ℝ) + 1) * (m:ℝ) ^ (-2 * σ) = (m:ℝ) ^ (1 - 2 * σ) + (m:ℝ) ^ (-2 * σ) := by
    intro m hm
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add_one hm'.ne']
    ring
  have hg : ∀ m, 0 ≤ g m := by
    intro m
    simp only [hg_def]
    split_ifs
    · norm_num
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hanti : Antitone g := by
    intro a b hab
    simp only [hg_def]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        exact le_rfl
      · rw [if_pos rfl, if_neg (by omega), hterm b hb]
        have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
        have h1 := Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith : 1 - 2 * σ ≤ 0)
        have h2 := Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith : -2 * σ ≤ 0)
        linarith
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      rw [if_neg (by omega), if_neg (by omega), hterm a ha, hterm b hb]
      have ha' : (0:ℝ) < a := by exact_mod_cast ha
      have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
      have h1 := Real.rpow_le_rpow_of_nonpos ha' hab' (by linarith : 1 - 2 * σ ≤ 0)
      have h2 := Real.rpow_le_rpow_of_nonpos ha' hab' (by linarith : -2 * σ ≤ 0)
      linarith
  have h0 := sum_mul_le_of_partial_sums hw hL hW hg hanti M
  have e1 : ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (w m * (m : ℝ) ^ (-2 * σ))
      = ∑ m ∈ Icc 1 M, w m * g m := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [hg_def, if_neg (show m ≠ 0 by omega)]
    ring
  have e2 : ∑ m ∈ Icc 1 M, g m = ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (m : ℝ) ^ (-2 * σ) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [hg_def, if_neg (show m ≠ 0 by omega)]
  have h1 := M1.sum_weight_le_logfree σ hσ hσ1 M
  have hMpow : 1 ≤ (M:ℝ) ^ (2 - 2 * σ) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by linarith)
  have hd : 0 < 2 - 2 * σ := by linarith
  have hdiv : 0 ≤ 2 / (2 - 2 * σ) := by positivity
  have hkey : 2 * (1 + (M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))
      ≤ (2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ) := by
    have e : (2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ)
        = 2 * (M:ℝ) ^ (2 - 2 * σ) + 2 * ((M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ)) := by ring
    rw [e]
    linarith
  rw [e1]
  calc ∑ m ∈ Icc 1 M, w m * g m ≤ L * ∑ m ∈ Icc 1 M, g m := h0
    _ = L * ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (m : ℝ) ^ (-2 * σ) := by rw [e2]
    _ ≤ L * (2 * (1 + (M:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))) := mul_le_mul_of_nonneg_left h1 hL
    _ ≤ L * ((2 + 2 / (2 - 2 * σ)) * (M:ℝ) ^ (2 - 2 * σ)) := mul_le_mul_of_nonneg_left hkey hL
    _ = (2 + 2 / (2 - 2 * σ)) * L * (M : ℝ) ^ (2 - 2 * σ) := by ring

end Zeta23.Density

#print axioms Zeta23.Density.sum_mul_le_of_partial_sums
#print axioms Zeta23.Density.sum_mul_le_of_partial_sums_tail
#print axioms Zeta23.Density.sum_Ioc_rpow_le
#print axioms Zeta23.Density.tail_sum_le
#print axioms Zeta23.Density.weight_sum_le
