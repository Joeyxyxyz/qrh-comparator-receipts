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

/-! ## Node PAIRS-B: the atom at s = 0 -/

/-! ### §B.0 A `∑ᶠ` over `s ∩ {x | p x}` as a `Finset` sum over the filtered finite set -/

/-- A finite sum over `s ∩ {x | p x}`, `s` finite, is the `Finset` sum over `hs.toFinset.filter p`. -/
lemma finsum_mem_inter_setOf_eq_sum_filter {M : Type*} [AddCommMonoid M] {s : Set ℂ}
    (hs : s.Finite) (p : ℂ → Prop) [DecidablePred p] (g : ℂ → M) :
    ∑ᶠ x ∈ s ∩ {x | p x}, g x = ∑ x ∈ hs.toFinset.filter p, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (hs.subset inter_subset_left)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finite.mem_toFinset, mem_inter_iff, mem_ofPred_eq]

/-! ### §B.0' `pairSum` as a double `Finset` sum (copied verbatim from node PAIRS-A; the merge
keeps one copy) -/

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

/-! ### §B.0'' The mirror (copied verbatim from node ZONES; the merge keeps one copy) -/

lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re := by simp [mirror]

lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im := by simp [mirror]

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

/-! ### §B.1 The atom at `s = 0` splits into the diagonal and the off-diagonal coincident mass -/

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

/-! ### §B.2 The off-diagonal coincident mass is nonnegative -/

theorem offDiagonalCoincidentMass_nonneg (T : ℝ) : 0 ≤ offDiagonalCoincidentMass T := by
  classical
  have hfin := zerosIn_finite 0 T
  unfold offDiagonalCoincidentMass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_nonneg fun ρ _ => ?_
  rw [finsum_mem_inter_setOf_eq_sum_filter hfin]
  exact Finset.sum_nonneg fun ρ' _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### §B.3 Every off-line zero contributes `m(ρ)²` through its mirror -/

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

/-! ### §B.4 The off-diagonal coincident mass against the off-line count -/

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

/-- **The off-diagonal coincident mass against the counts.**  An ordered pair of distinct zeros
with equal ordinates has at least one off-line member: for an off-line `ρ` the partners weigh at
most `N(0,T)`, and for an on-line `ρ` every partner is off-line (two on-line zeros with the same
ordinate coincide), so they weigh at most `NOffLine 0 T`.  Hence
`offDiag ≤ NOffLine · N + N0 · NOffLine`. -/
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

/-! ### §B.5 Under "all zeros on the line" the off-diagonal coincident mass vanishes -/

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

/-! ### §B.6 Conversely: a vanishing off-diagonal coincident mass forces the line -/

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

/-! ### §B.7 The off-diagonal coincident mass is eventually at most `(2/3 + ε) N(0,T)²` -/

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

/-! ### §B.7' The sharp eventual constant of the method: `(5/9 + ε) N(0,T)²` -/

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

/-- With `N0 = N − NOffLine`, `offDiagonalCoincidentMass_le` reads
`offDiag ≤ NOffLine · (2N − NOffLine) = N² − (N − NOffLine)²`; as `NOffLine ≤ (1/3 + ε') N`
eventually, this is at most `(1 − (2/3 − ε')²) N² ≤ (5/9 + ε) N²`.  (`5/9` is sharp for this
bookkeeping: it is attained by piling an on-line mass `2N/3` and an off-line mass `N/3` at one
ordinate.) -/
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

/-! ### Axiom audit -/

#print axioms MNF.RH.finsum_mem_inter_setOf_eq_sum_filter
#print axioms MNF.RH.pairSum_eq_sum
#print axioms MNF.RH.mirror_re
#print axioms MNF.RH.mirror_im
#print axioms MNF.RH.mirror_mem_zerosIn
#print axioms MNF.RH.zeta_order_mirror
#print axioms MNF.RH.mirror_eq_self_iff
#print axioms MNF.RH.coincidentMass_eq
#print axioms MNF.RH.offDiagonalCoincidentMass_nonneg
#print axioms MNF.RH.offLine_sq_le_offDiagonalCoincidentMass
#print axioms MNF.RH.NOffLine_real_eq_sum_filter
#print axioms MNF.RH.N0_real_eq_sum_filter
#print axioms MNF.RH.offDiagonalCoincidentMass_le
#print axioms MNF.RH.offDiagonalCoincidentMass_le_two_mul
#print axioms MNF.RH.offDiagonalCoincidentMass_eq_zero_of_onLine
#print axioms MNF.RH.onLine_of_offDiagonalCoincidentMass_eq_zero
#print axioms MNF.RH.offDiagonalCoincidentMass_le_two_thirds
#print axioms MNF.RH.Ncount_eq_N0_add_NOffLine
#print axioms MNF.RH.offDiagonalCoincidentMass_le_five_ninths

end MNF.RH
