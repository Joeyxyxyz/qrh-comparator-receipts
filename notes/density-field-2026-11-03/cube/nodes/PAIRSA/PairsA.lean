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

/-! ## Node PAIRS-A: the marginals of the pair measure -/

/-! ### §A.1 `pairSum` as a double `Finset` sum over the finite window -/

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

/-- The same, with the window's finiteness proof `zerosIn_finite 0 T` (a proof term in the
statement: hence `aux_`). -/
theorem aux_pairSum_eq_finset_sum (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    pairSum T f = ∑ ρ ∈ (zerosIn_finite 0 T).toFinset, ∑ ρ' ∈ (zerosIn_finite 0 T).toFinset,
      (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im) :=
  pairSum_eq_sum (zerosIn_finite 0 T) f

/-! ### §A.2 The total mass: `pairSum T 1 = N(0,T)²` -/

/-- The pair measure of the constant `1` is `N(0,T)²`. -/
theorem pairSum_const (T : ℝ) : pairSum T (fun _ _ _ => 1) = (Ncount 0 T : ℝ) ^ 2 := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, Ncount_eq_sum hfin]
  push_cast
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  ring

/-! ### §A.3 The marginals: a test function of one coordinate only -/

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

/-! ### §A.4 The first marginal of the reservoir indicator: `N(0,T) · N_off(δ; 0, T)` -/

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

/-! ### §A.5 The first marginal of `|a|`: `N(0,T) · reservoirMass T`, and the double layer cake -/

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

/-! ### §A.6 The swap symmetry of ordered pairs -/

/-- Swapping the two zeros of each ordered pair: `pairSum T f = pairSum T (f ∘ swap)`, the
ordinate difference changing sign. -/
theorem pairSum_swap (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    pairSum T f = pairSum T (fun a b s => f b a (-s)) := by
  have hfin := zerosIn_finite 0 T
  rw [pairSum_eq_sum hfin, pairSum_eq_sum hfin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  rw [neg_sub, mul_comm (zeta_order ρ' : ℝ)]

/-! ### §A.7 Positivity and monotonicity -/

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

/-! ### §A.8 The diagonal mass `Σ m(ρ)²`: between `N(0,T)` and `N(0,T)²` -/

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

/-! ### Axiom audit -/

#print axioms MNF.RH.pairSum_eq_sum
#print axioms MNF.RH.aux_pairSum_eq_finset_sum
#print axioms MNF.RH.pairSum_const
#print axioms MNF.RH.pairSum_fst
#print axioms MNF.RH.pairSum_snd
#print axioms MNF.RH.pairSum_fst_indicator
#print axioms MNF.RH.pairSum_fst_abs
#print axioms MNF.RH.pairSum_fst_abs_eq_integral
#print axioms MNF.RH.pairSum_swap
#print axioms MNF.RH.pairSum_nonneg
#print axioms MNF.RH.pairSum_mono
#print axioms MNF.RH.diagonalMass_nonneg
#print axioms MNF.RH.diagonalMass_le_sq_Ncount
#print axioms MNF.RH.Ncount_le_diagonalMass

end MNF.RH
