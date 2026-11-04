/- LOCAL ONLY. Off-line zeros carry at most (1/3 + o(1)) of N(0,T), with multiplicity. -/
import Zeta23.FinalMult

open Set

namespace Zeta23

/-- On-line count with multiplicity. -/
noncomputable def NonMult (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ
/-- Off-line count with multiplicity (Re ρ ≠ 1/2). -/
noncomputable def NoffMult (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}, zeroMult ρ

theorem Ncount_eq_on_add_off (T₁ T₂ : ℝ) : Ncount T₁ T₂ = NonMult T₁ T₂ + NoffMult T₁ T₂ := by
  have hf := zerosIn_finite T₁ T₂
  unfold Ncount NonMult NoffMult
  have hd : Disjoint (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}) (zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}) :=
    disjoint_left.2 fun x h1 h2 => (show x.re ≠ 1 / 2 from h2.2) h1.2
  rw [← finsum_mem_union hd (hf.subset inter_subset_left) (hf.subset inter_subset_left)]
  rw [← inter_union_distrib_left,
    show {ρ : ℂ | ρ.re = 1 / 2} ∪ {ρ | ρ.re ≠ 1 / 2} = univ from by ext ρ; simp [em], inter_univ]

theorem N0simple_le_NonMult (T₁ T₂ : ℝ) : N0simple T₁ T₂ ≤ NonMult T₁ T₂ := by
  have hf := (zerosIn_finite T₁ T₂).subset (inter_subset_left (t := {ρ : ℂ | ρ.re = 1 / 2}))
  have hS := hf.subset (inter_subset_left (t := {ρ : ℂ | zeroMult ρ = 1}))
  unfold N0simple NonMult
  calc (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard
      = ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}, zeroMult ρ := by
        rw [ncard_eq_toFinset_card _ hS, finsum_mem_eq_finite_toFinset_sum _ hS]
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun x hx => ?_
        simp only [Finite.mem_toFinset] at hx; exact hx.2.symm
    _ ≤ _ := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hf]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finite.toFinset_subset_toFinset.2 inter_subset_left) (fun _ _ _ => Nat.zero_le _)

/-- **Off-line bound**: ∀ ε>0, eventually N_off(0,T) ≤ (1/3 + ε) N(0,T) (multiplicity-weighted). -/
theorem offLine_le_one_third :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NoffMult 0 T : ℝ) ≤ (1 / 3 + ε) * Ncount 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := thmB₀_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := h T hT
  have h2 : (N0simple 0 T : ℝ) ≤ NonMult 0 T := by exact_mod_cast N0simple_le_NonMult 0 T
  have h3 : (Ncount 0 T : ℝ) = NonMult 0 T + NoffMult 0 T := by exact_mod_cast Ncount_eq_on_add_off 0 T
  linarith

/-- dyadic form. -/
theorem offLine_le_one_third_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NoffMult T (2 * T) : ℝ) ≤ (1 / 3 + ε) * Ncount T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := thmB₀_mult ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := h T hT
  have h2 : (N0simple T (2*T) : ℝ) ≤ NonMult T (2*T) := by exact_mod_cast N0simple_le_NonMult _ _
  have h3 : (Ncount T (2*T) : ℝ) = NonMult T (2*T) + NoffMult T (2*T) := by
    exact_mod_cast Ncount_eq_on_add_off _ _
  linarith

end Zeta23
#print axioms Zeta23.offLine_le_one_third
#print axioms Zeta23.offLine_le_one_third_dyadic
