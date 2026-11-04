# Reservoir-mass workflow: node reports (2026-11-03/04)

Six nodes proved the pieces in parallel on the zeta23 dev tree; the merge produced `ReservoirMass.merged.lean`, installed as `MNF/RH/ReservoirMass.lean`. Each block below is the node's own structured report (status, file, imports, proved and unproved statements, notes), recorded verbatim.

## x1: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X1/X1.lean`
- imports: `Mathlib`, `Zeta23.BL.BohrLandauClosure`

### proved

- `noncomputable def Zeta23.BL.CG : ℝ := max (Classical.choose (BLClosure.zeta_approx_sharp (σ₀ := 1 / 2) one_half_pos')) 0`
- `lemma Zeta23.BL.CG_nonneg : 0 ≤ CG`
- `lemma Zeta23.BL.CG_spec : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N → (σ : ℂ) + t * I ≠ 1 → ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S N ((σ : ℂ) + t * I) - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖ ≤ CG * (N : ℝ) ^ (-σ)`
- `theorem Zeta23.BL.zeta_approx_segment_half : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∀ t ∈ Icc (1 : ℝ) T, ‖riemannZeta ((σ : ℂ) + t * I) - BLClosure.S ⌈T⌉₊ ((σ : ℂ) + t * I) - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖ ≤ CG`
- `theorem Zeta23.BL.meanSquare_sharp_param_half {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ (4 * (1 + 1 / (2 * σ₁ - 1)) + 112 + 416 / (2 - 2 * σ₁) + 4 * CG ^ 2) * T`
- `lemma Zeta23.BL.tsum_one_div_rpow_two_sq_le : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) ^ 2 ≤ 3`
- `noncomputable def Zeta23.BL.meanSquareB : ℝ := 951 + 4 * CG ^ 2`
- `lemma Zeta23.BL.meanSquareB_nonneg : 0 ≤ meanSquareB`
- `theorem Zeta23.BL.meanSquare_explicit_small_B : ∀ σ₁ : ℝ, 1 / 2 < σ₁ → σ₁ ≤ 3 / 4 → ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ (4 / (2 * σ₁ - 1) + meanSquareB) * T`
- `theorem Zeta23.BL.meanSquare_explicit_small : ∃ B : ℝ, 0 ≤ B ∧ ∀ σ₁ : ℝ, 1 / 2 < σ₁ → σ₁ ≤ 3 / 4 → ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * Complex.I)‖ ^ 2 ≤ (4 / (2 * σ₁ - 1) + B) * T`
- `theorem Zeta23.BL.meanSquareUnifFrom_explicit (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : ∀ σ : ℝ, 1 / 2 + δ / 2 ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * Complex.I)‖ ^ 2 ≤ (4 / δ + meanSquareB) * T`
- `theorem Zeta23.BL.meanSquareUnifFrom_explicit' (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : Zeta23.BL.M3.MeanSquareUnifFrom (1 / 2 + δ / 2)`

### unproved

(none)

### notes

Compiled with `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`: exit 0, no errors, no warnings, no sorry (the only textual "sorry" is in the header comment "No sorry."). `#print axioms` for CG_spec, zeta_approx_segment_half, meanSquare_sharp_param_half, tsum_one_div_rpow_two_sq_le, meanSquare_explicit_small_B, meanSquare_explicit_small, meanSquareUnifFrom_explicit, meanSquareUnifFrom_explicit' each report exactly [propext, Classical.choice, Quot.sound]. Nothing under the zeta23 tree was modified.

Route, as prescribed: the approximate-formula constant is taken once at σ₀ = 1/2 via `BLClosure.zeta_approx_sharp (σ₀ := 1/2)` and named `CG := max C₀ 0` (a noncomputable def by Classical.choose, so that "the same B" is literal across the two main theorems). `zeta_approx_segment_half` is the segment specialisation (copy of `zeta_approx_sharp_segment'` with hypothesis 1/2 ≤ σ); `meanSquare_sharp_param_half` is the proof text of `BLClosure.meanSquare_sharp_param` with the fixed CG (needs 1/2 < σ₁ < 1 for `M1.sum_weight_le_logfree`), giving the constant 4(1 + 1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4 CG². For σ₁ ≤ 3/4: 416/(2−2σ₁) ≤ 832. For σ > 2: `Zeta23.BL.meanSquare_of_gt_one (σ₂ := 2)` with constant (∑' 1/n^2)² = (π²/6)² ≤ 3 (proved via Mathlib's `hasSum_zeta_two`, `Real.rpow_two`, `Real.pi_lt_d2`). Hence the σ₁-independent part is explicit: meanSquareB = 951 + 4 CG² (951 = 4 + 112 + 832 + 3), and the bound is (4/(2σ₁−1) + meanSquareB) T. The δ-specialisation uses σ₁ = 1/2 + δ/2 (2σ₁ − 1 = δ by ring), 0 < δ ≤ 1/2 ⇒ 1/2 < σ₁ ≤ 3/4. The only non-explicit ingredient is CG, inherited from `tail_sharp` / `zeta_approx_sharp` at σ₀ = 1/2, which the tree states existentially. Side remark: the sharp approximate formula in the tree is proved only for σ ≤ 2, which is why the σ > 2 range uses the trivial ζ(2)² bound; the resulting constant is monotone-free in σ (uniform for all σ ≥ σ₁).

## x2: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X2/X2.lean`
- imports: `Mathlib`, `Zeta23.BL.BohrLandauClosure`

### proved

- `theorem Zeta23.BL.bohrLandau_explicit : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → ∀ T : ℝ, 2 ≤ T → (MNF.RH.NOff δ 0 T : ℝ) ≤ (A * δ ^ (-(5/2 : ℝ)) + B) * T`
- `theorem Zeta23.BL.NRight_explicit {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ (A₀ * δ ^ (-(5 / 2 : ℝ)) + (MNF.RH.Ncount 0 4 : ℝ) / 2) * T`
- `noncomputable def Zeta23.BL.A₀ : ℝ := 54 + 27 / 2 * meanSquareB + 12 * Real.log 3`
- `lemma Zeta23.BL.A₀_nonneg : 0 ≤ A₀`
- `lemma Zeta23.BL.log_three_nonneg : 0 ≤ Real.log 3`
- `theorem Zeta23.BL.NRight_le_Ncount (δ T : ℝ) : NRight δ T ≤ MNF.RH.Ncount 0 T`
- `lemma Zeta23.BL.Rout_half (δ : ℝ) : Rout (1 / 2 + δ / 2) = 3 / 2 - δ / 2`
- `lemma Zeta23.BL.rin_half (δ : ℝ) : rin (1 / 2 + δ / 2) δ = 3 / 2 - 3 * δ / 4`
- `lemma Zeta23.BL.hwin_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : Real.sqrt δ / 4 ≤ hwin (1 / 2 + δ / 2) δ`
- `lemma Zeta23.BL.log_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : δ / 6 ≤ Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ)`
- `lemma Zeta23.BL.K_half_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : δ * Real.sqrt δ / 12 ≤ 2 * hwin (1 / 2 + δ / 2) δ * Real.log (Rout (1 / 2 + δ / 2) / rin (1 / 2 + δ / 2) δ)`
- `lemma Zeta23.BL.rpow_neg_five_half_mul {δ : ℝ} (hδ : 0 < δ) : δ ^ (-(5 / 2 : ℝ)) * (δ ^ 2 * Real.sqrt δ) = 1`
- `(verbatim copy of X1, re-proved in this file:) noncomputable def Zeta23.BL.CG, lemma CG_nonneg, lemma CG_spec, theorem zeta_approx_segment_half, theorem meanSquare_sharp_param_half, lemma tsum_one_div_rpow_two_sq_le, noncomputable def meanSquareB := 951 + 4 * CG ^ 2, lemma meanSquareB_nonneg, theorem meanSquare_explicit_small_B, theorem meanSquare_explicit_small, theorem meanSquareUnifFrom_explicit, theorem meanSquareUnifFrom_explicit'`

### unproved

(none)

### notes

Compiled with `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`: exit 0, no errors, no warnings, no sorry (the only textual "sorry" is the header comment "No sorry."). `#print axioms` for meanSquareUnifFrom_explicit, NRight_le_Ncount, hwin_half_ge, log_half_ge, K_half_ge, rpow_neg_five_half_mul, A₀_nonneg, NRight_explicit and bohrLandau_explicit each report exactly [propext, Classical.choice, Quot.sound]. Nothing under the zeta23 tree was modified (the git-status entries lakefile.toml / MNF/ / MNFChallenges/ predate this run; `find -newer` shows no file touched).

Explicit constants: A = 2·A₀ with A₀ = 54 + (27/2)·meanSquareB + 12·log 3 (meanSquareB = 951 + 4·CG² from X1, CG the approximate-formula constant at σ₀ = 1/2, the only non-explicit ingredient, inherited from the tree's existential `BLClosure.zeta_approx_sharp`), and B = Ncount 0 4 (number of zeros with 0 < Im ρ ≤ 4, with multiplicity — a fixed natural number). The δ-dependence is A·δ^{-5/2}: the δ^{-3/2} term (from the (9/8)·meanSquareB + log 3 part of the mean-square constant) was absorbed into A via 1/δ ≥ 1.

Route, as prescribed: σ₁ := 1/2 + δ/2 (so 1/2 < σ₁ < 1, σ₁ − 1/2 = δ/2 < δ; since δ ≤ 1/2 is given, the δ ≥ 1/2 case split of rightHalf_of_meanSquareUnif is not needed), mean-square hypothesis = X1's meanSquareUnifFrom_explicit with C₀ = 4/δ + meanSquareB ≥ 0 (no max C₀ 0 needed). Geometry at this σ₁: Rout = 3/2 − δ/2, rin = 3/2 − 3δ/4, rin² − (3/2 − δ)² = (δ/4)(3 − 7δ/4) ≥ δ/4 (δ ≤ 8/7 suffices), so hwin ≥ √δ/4 via Real.le_sqrt + Real.sq_sqrt; log(Rout/rin) ≥ 1 − rin/Rout (Real.one_sub_inv_le_log_of_pos, inv_div) = (δ/4)/(3/2 − δ/2) ≥ δ/6 (div_le_iff₀ + nlinarith). Hence K ≥ δ√δ/12 (slightly better than the suggested c·δ^{3/2} with log ≥ δ/7). For T ≥ 4, count_le_meanSquare' gives K(NRight δ T − NRight δ 4) ≤ (1/2)C₀(T+5) + T log 3 ≤ ((9/8)C₀ + log 3)T ≤ (A₀/12)(1/δ)T ≤ K·A₀·δ^{-5/2}·T, using δ^{-5/2}·δ²√δ = 1 (Real.sqrt_eq_rpow, Real.rpow_two, Real.rpow_add, Real.rpow_neg) in the form δ√δ·δ^{-5/2} = 1/δ. NRight δ 4 ≤ Ncount 0 4 (NRight_le_Ncount, mirror of MNF.RH.NOff_le_Ncount) and Ncount 0 4 ≤ (Ncount 0 4 / 2)·T for T ≥ 2; for 2 ≤ T < 4 NRight_mono. Finally NOff δ 0 T = 2·NRight δ T by NOff_eq_right_add_left and NLeft_eq_NRight.

One compile iteration was needed: linarith treats `4/δ` and `1/δ` as unrelated atoms; fixed by adding `4/δ = 4 * (1/δ)` (by ring) as a hypothesis. Side remark on the exponent: with σ₁ = 1/2 + δ/2 the Jensen-window height hwin is only ≍ √δ and log(Rout/rin) ≍ δ, which is where δ^{-3/2} comes from; the diagonal mean-square term contributes 1/δ, giving δ^{-5/2} overall. A choice σ₁ = 1/2 + cδ with c closer to 1 would not change the exponent, only the constant.

## x3: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X3/X3.lean`
- imports: `MNF.RH.GapDensity`, `Zeta23.BL.BohrLandauClosure`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`

### proved

- `noncomputable def MNF.RH.reservoirMass (T : ℝ) : ℝ := ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * |ρ.re - 1 / 2|`
- `theorem MNF.RH.abs_re_sub_half_lt_half {ρ : ℂ} (h : is_nontrivial_zero ρ) : |ρ.re - 1 / 2| < 1 / 2`
- `theorem MNF.RH.abs_re_sub_half_le_half {ρ : ℂ} (h : is_nontrivial_zero ρ) : |ρ.re - 1 / 2| ≤ 1 / 2`
- `theorem MNF.RH.NOff_eq_sum_ite (δ T₁ T₂ : ℝ) : NOff δ T₁ T₂ = ∑ ρ ∈ (zerosIn_finite T₁ T₂).toFinset, if δ ≤ |ρ.re - 1 / 2| then zeta_order ρ else 0`
- `theorem MNF.RH.NOff_real_eq_sum_indicator (δ T₁ T₂ : ℝ) : (NOff δ T₁ T₂ : ℝ) = ∑ ρ ∈ (zerosIn_finite T₁ T₂).toFinset, (zeta_order ρ : ℝ) * Set.indicator {x : ℝ | x ≤ |ρ.re - 1 / 2|} (fun _ => (1 : ℝ)) δ`
- `theorem MNF.RH.NOff_anti {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) (T₁ T₂ : ℝ) : NOff δ₂ T₁ T₂ ≤ NOff δ₁ T₁ T₂`
- `theorem MNF.RH.NOff_antitone (T₁ T₂ : ℝ) : Antitone (fun δ => (NOff δ T₁ T₂ : ℝ))   -- item (4)`
- `theorem MNF.RH.NOff_intervalIntegrable (T₁ T₂ a b : ℝ) : IntervalIntegrable (fun δ => (NOff δ T₁ T₂ : ℝ)) volume a b   -- item (5), for every [a,b], in particular [0,1/2]`
- `theorem MNF.RH.indicator_le_antitone (a : ℝ) : Antitone (fun δ : ℝ => Set.indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ)`
- `theorem MNF.RH.term_intervalIntegrable (c a x y : ℝ) : IntervalIntegrable (fun δ : ℝ => c * Set.indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ) volume x y`
- `theorem MNF.RH.integral_indicator_le_eq {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1 / 2) : ∫ δ in (0 : ℝ)..(1 / 2), Set.indicator {x : ℝ | x ≤ a} (fun _ => (1 : ℝ)) δ = a`
- `theorem MNF.RH.reservoirMass_eq_integral (T : ℝ) : reservoirMass T = ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ)   -- item (1), the layer-cake identity`
- `theorem MNF.RH.reservoirMass_nonneg (T : ℝ) : 0 ≤ reservoirMass T   -- item (3)`
- `theorem MNF.RH.reservoirMass_le_half_Ncount (T : ℝ) : reservoirMass T ≤ (1 / 2) * Ncount 0 T   -- item (2)`
- `theorem MNF.RH.integral_NOff_split (T δ₀ : ℝ) : ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ) = (∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ)) + ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ)   -- item (6a), for every δ₀ (no hypothesis needed)`
- `theorem MNF.RH.integral_NOff_le_mul_Ncount (T : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) : ∫ δ in (0 : ℝ)..δ₀, (NOff δ 0 T : ℝ) ≤ δ₀ * Ncount 0 T   -- item (6b)`
- `theorem MNF.RH.integral_NOff_tail_le (T : ℝ) {δ₀ : ℝ} (h1 : δ₀ ≤ 1 / 2) : ∫ δ in δ₀..(1 / 2), (NOff δ 0 T : ℝ) ≤ (1 / 2 - δ₀) * NOff δ₀ 0 T`
- `theorem MNF.RH.reservoirMass_le_split (T : ℝ) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 1 / 2) : reservoirMass T ≤ δ₀ * Ncount 0 T + (1 / 2 - δ₀) * NOff δ₀ 0 T`
- `theorem MNF.RH.reservoirMass_le_eps_Ncount : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, reservoirMass T ≤ ε * Ncount 0 T   -- uses MNF.RH.reservoirDensityOne_unconditional from Zeta23.BL.BohrLandauClosure`

### unproved

(none)

### notes

Compiled with exactly `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`: zero errors, zero warnings (about 4.5 s wall since all imports are prebuilt oleans). No `sorry` anywhere (the only textual occurrence is in the header comment). `#print axioms` on all ten main results (reservoirMass_eq_integral, reservoirMass_le_half_Ncount, reservoirMass_nonneg, NOff_antitone, NOff_intervalIntegrable, integral_NOff_split, integral_NOff_le_mul_Ncount, integral_NOff_tail_le, reservoirMass_le_split, reservoirMass_le_eps_Ncount) reports only [propext, Classical.choice, Quot.sound].

Proof route for (1): NOff δ 0 T is rewritten as a Finset sum over (zerosIn_finite 0 T).toFinset of zeta_order ρ * indicator {x | x ≤ |ρ.re − 1/2|} 1 δ (via finsum_mem_eq_finite_toFinset_sum and Finset.sum_filter); the Finset sum and interval integral are interchanged with intervalIntegral.integral_finsetSum (note: `integral_finset_sum` is a deprecated alias on this Mathlib); each per-zero integral is evaluated with Mathlib's intervalIntegral.integral_indicator (h : a₂ ∈ Icc a₁ a₃) : ∫ x in a₁..a₃, indicator {x | x ≤ a₂} f x = ∫ x in a₁..a₂, f x, then integral_const, using |Re ρ − 1/2| ≤ 1/2 from 0 < Re ρ < 1. Interval integrability (5) comes for free from antitonicity (4) via Antitone.intervalIntegrable, on every [a,b], so the split (6a) needs no hypothesis on δ₀. (6b) and the tail bound integral_NOff_tail_le use intervalIntegral.integral_mono_on against a constant.

Two consequences beyond the brief, useful for the strip program: reservoirMass_le_split (mass ≤ δ₀·N(0,T) + (1/2 − δ₀)·N_off(δ₀;0,T)) and reservoirMass_le_eps_Ncount, i.e. Σ_ρ m(ρ)|Re ρ − 1/2| = o(N(0,T)) — the multiplicity-weighted mean distance of zeros from the critical line tends to 0 — obtained by taking δ₀ = min(ε/2, 1/2) and discharging N_off(δ₀) ≤ ε·N with the tree's unconditional ReservoirDensityOne (hence the second import, Zeta23.BL.BohrLandauClosure; everything else needs only MNF.RH.GapDensity). Items (1)–(6) do not depend on that import.

Helper names introduced in namespace MNF.RH (abs_re_sub_half_lt_half, NOff_eq_sum_ite, NOff_real_eq_sum_indicator, NOff_anti, indicator_le_antitone, term_intervalIntegrable, integral_indicator_le_eq) were checked not to collide with anything in the tree at compile time. Nothing under the zeta23 project was modified.

## x4: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X4/X4.lean`
- imports: `Zeta23.Superlinear`, `Zeta23.RvM.NcountWindow`, `MNF.RH.Counting`

### proved

- `theorem Zeta23.Ncount_self (a : ℝ) : Ncount a a = 0`
- `theorem Zeta23.Ncount_zero_nat (n : ℕ) : Ncount 0 (n : ℝ) = ∑ m ∈ Finset.range n, Ncount (m : ℝ) ((m : ℝ) + 1)`
- `theorem Zeta23.Ncount_unit_le {A₀ : ℝ} (hA : 1 ≤ A₀) (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (m : ℕ) {T : ℝ} (hmT : (m : ℝ) ≤ T) : (Ncount (m : ℝ) ((m : ℝ) + 1) : ℝ) ≤ A₀ * Real.log (T + 3)`
- `theorem Zeta23.Ncount_le_mul_log : ∃ C : ℝ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (Ncount 0 T : ℝ) ≤ C * T * Real.log T`
- `theorem Zeta23.ell1_half (T : ℝ) (hT : 0 < T) : ell1 (T / 2) = Real.log T - Real.log Real.pi - 1`
- `theorem Zeta23.mul_log_le_Ncount : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → c * T * Real.log T ≤ (Ncount 0 T : ℝ)`
- `theorem Zeta23.MNF_Ncount_eq (T₁ T₂ : ℝ) : MNF.RH.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂`
- `theorem Zeta23.MNF_Ncount_le_mul_log : ∃ C : ℝ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (MNF.RH.Ncount 0 T : ℝ) ≤ C * T * Real.log T`
- `theorem Zeta23.MNF_mul_log_le_Ncount : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → c * T * Real.log T ≤ (MNF.RH.Ncount 0 T : ℝ)`

### unproved

(none)

### notes

Compiled with `cd .../zeta23 && lake env lean X4.lean`: zero errors, zero warnings, no sorry. `#print axioms` on Ncount_le_mul_log, mul_log_le_Ncount, MNF_Ncount_le_mul_log, MNF_mul_log_le_Ncount each gives exactly [propext, Classical.choice, Quot.sound].

Upper bound (Ncount_le_mul_log) uses the simpler local_count route: N(0,T) ≤ N(0,⌈T⌉₊) (Ncount_mono) = Σ_{m<⌈T⌉₊} N(m,m+1) (Ncount_zero_nat, by induction on Ncount_add) ≤ ⌈T⌉₊·A₀·log(T+3) (Nat.lt_ceil gives m ≤ T) ≤ (T+1)·A₀·2 log T ≤ 4A₀·T·log T for T ≥ 3. Explicit witnesses: C = 4·A₀ (A₀ from riemannVonMangoldt_zeta.local_count), T₀ = 3.

Lower bound (mul_log_le_Ncount) uses riemannVonMangoldt_zeta.main at T/2 (window (T/2, T], rewritten via zetaZeroConfig_N and 2*(T/2)=T): ell1(T/2) = log T − log π − 1 (ell1_half, exact identity), ≥ (1/2) log T once log T ≥ 8 (using log π ≤ π − 1 ≤ 3); main term ≥ T log T/(8π); error C·log(T/2) ≤ |C|·log T ≤ T log T/(16π) once T ≥ 16π|C|; then N(0,T) ≥ N(T/2,T) by Ncount_mono. Explicit witnesses: c = 1/(16π), T₀ = 2 + 2|T₁| + exp 8 + 16π(|C|+1) where C, T₁ come from .main.

MNF.RH restatements are definitional (rfl), as stated in the task; MNF_Ncount_eq is the rfl bridge. Dyadic-decomposition route for the upper bound was not needed. Nothing under the zeta23 tree was modified.

## x5: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X5/X5.lean`
- imports: `Mathlib`, `Zeta23.BL.BohrLandauClosure`, `MNF.RH.GapDensity`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`, `Zeta23.Superlinear`, `Zeta23.RvM.NcountWindow`, `MNF.RH.Counting`

### proved

- `theorem MNF.RH.reservoirMass_le_rpow : ∃ A : ℝ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → reservoirMass T ≤ A * T * (Real.log T) ^ ((3:ℝ)/5)`
- `theorem MNF.RH.reservoirMass_le_Ncount_mul : ∃ A : ℝ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → reservoirMass T ≤ A * (Real.log T) ^ (-(2:ℝ)/5) * Ncount 0 T`
- `theorem MNF.RH.meanDisplacement_tendsto_zero : Filter.Tendsto (fun T : ℝ => reservoirMass T / (Ncount 0 T : ℝ)) Filter.atTop (nhds 0)`
- `theorem MNF.RH.rpow_tail_intervalIntegrable (A B T : ℝ) {δ₀ : ℝ} (h0 : 0 < δ₀) (h1 : δ₀ ≤ 1 / 2) : IntervalIntegrable (fun δ : ℝ => (A * δ ^ (-(5 / 2 : ℝ)) + B) * T) volume δ₀ (1 / 2)`
- `theorem MNF.RH.integral_rpow_tail_le (A B T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) {δ₀ : ℝ} (h0 : 0 < δ₀) (h1 : δ₀ ≤ 1 / 2) : ∫ δ in δ₀..(1 / 2), (A * δ ^ (-(5 / 2 : ℝ)) + B) * T ≤ (2 / 3 * A * δ₀ ^ (-(3 / 2 : ℝ)) + B / 2) * T`
- `(verbatim copies of X2, X3, X4, re-proved in this file inside named sections: all of Zeta23.BL.bohrLandau_explicit / NRight_explicit / A₀ / meanSquareB / CG etc. from X2 (which repeats X1); MNF.RH.reservoirMass and the layer-cake results reservoirMass_eq_integral, integral_NOff_split, integral_NOff_le_mul_Ncount, integral_NOff_tail_le, reservoirMass_le_split, reservoirMass_le_eps_Ncount etc. from X3; Zeta23.Ncount_le_mul_log, mul_log_le_Ncount, MNF_Ncount_le_mul_log, MNF_mul_log_le_Ncount etc. from X4)`

### unproved

(none)

### notes

Compiled with exactly `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`: exit 0, zero errors, zero warnings (about 23 s wall; log at .../reservoir/X5/compile2.log). No sorry anywhere (the only textual occurrences are header comments "No sorry"). `#print axioms` on all five new results (rpow_tail_intervalIntegrable, integral_rpow_tail_le, reservoirMass_le_rpow, reservoirMass_le_Ncount_mul, meanDisplacement_tendsto_zero) and on the re-proved upstream results each report exactly [propext, Classical.choice, Quot.sound]. Nothing under the zeta23 tree was created, modified or deleted (`find -newer` shows no file touched outside .lake).

File layout: union of the three upstream import lists at the top; then the X2, X3 and X4 texts verbatim (diff-verified identical to the originals minus their `import` lines), each wrapped in a named `section X?_verbatim ... end X?_verbatim` so that X2's top-level `open Complex Real ... Set Filter` and X4's `open Finset` do not leak into the other copies or into the new block; then the X5 block in namespace MNF.RH. No upstream node left a sorry, so none was inherited.

Route for (1), as prescribed: T₀ = max T₁ (exp 8) (T₁ from X4's upper bound), so log T ≥ 8 and δ₀ := (log T)^{-2/5} ≤ 1/2 via 2 = 2^1 ≤ 2^{3·(2/5)} = (2^3)^{2/5} = 8^{2/5} ≤ (log T)^{2/5} (Real.rpow_le_rpow_of_exponent_le, Real.rpow_mul, Real.rpow_le_rpow, then Real.rpow_neg + inv_anti₀). Layer cake (X3's reservoirMass_eq_integral) split at δ₀ (integral_NOff_split); head piece ≤ δ₀·N(0,T) (integral_NOff_le_mul_Ncount) ≤ δ₀·C T log T = C T (log T)^{3/5} (Real.rpow_add with exponent 1); tail piece ≤ ∫_{δ₀}^{1/2} (A₂ δ^{-5/2} + B₂) T dδ by intervalIntegral.integral_mono_on against X2's bohrLandau_explicit pointwise on [δ₀, 1/2] (integrability of the majorant from the root-namespace `intervalIntegrable_rpow` with 0 ∉ [[δ₀,1/2]]), evaluated exactly with the root-namespace `integral_rpow` (r = −5/2 ≠ −1, 0 ∉ [[δ₀,1/2]]): = (A₂((1/2)^{-3/2} − δ₀^{-3/2})/(−3/2) + B₂(1/2 − δ₀)) T ≤ ((2/3)A₂ δ₀^{-3/2} + B₂/2) T, and δ₀^{-3/2} = (log T)^{3/5} by ← Real.rpow_mul + norm_num. Finally (log T)^{3/5} ≥ 1 (Real.one_le_rpow) absorbs B₂/2·T. Explicit constant: A = C + (2/3)A₂ + B₂/2 with C = 4A₀ from X4 (A₀ the local_count constant), A₂ = 2·A₀(X2) = 2(54 + (27/2)meanSquareB + 12 log 3), B₂ = Ncount 0 4.

(2): A = |A₁|/c, T₀ = max T₁ T₂; T (log T)^{3/5} = (log T)^{-2/5}·(T log T) ≤ (log T)^{-2/5}·N(0,T)/c from X4's lower bound (c = 1/(16π)). (3): squeeze (tendsto_of_tendsto_of_tendsto_of_le_of_le') between 0 and A·(log T)^{-2/5} → 0, the latter from root-namespace `tendsto_rpow_neg_atTop` composed with Real.tendsto_log_atTop; N(0,T) > 0 for T ≥ T₂ from c T log T > 0.

Two compile iterations: the only failures were the namespaces of `integral_rpow` and `tendsto_rpow_neg_atTop`, which live in the root namespace on this Mathlib (not intervalIntegral.* / Real.*); fixed by grep. No hypothesis remains; all three target statements are proved unconditionally in the stated form.

## x6: proved

- file: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/X6/X6.lean`
- imports: `Zeta23.BohrLandau`

### proved

- `noncomputable def MNF.RH.reservoirMass (T : ℝ) : ℝ := ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * |ρ.re - 1 / 2|`
- `theorem MNF.RH.signedReservoir_eq_zero (T : ℝ) : ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) = 0`
- `theorem MNF.RH.sum_right_eq_sum_left (T : ℝ) : ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | 1 / 2 < ρ.re}, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2) = ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | ρ.re < 1 / 2}, (zeta_order ρ : ℝ) * (1 / 2 - ρ.re)`
- `theorem MNF.RH.reservoirMass_eq_two_right (T : ℝ) : reservoirMass T = 2 * ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | 1 / 2 < ρ.re}, (zeta_order ρ : ℝ) * (ρ.re - 1 / 2)`
- `lemma MNF.RH.reflect_re (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re`
- `lemma MNF.RH.reflect_im (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im`
- `lemma MNF.RH.reflect_reflect (ρ : ℂ) : Zeta23.reflect (Zeta23.reflect ρ) = ρ`
- `lemma MNF.RH.reflect_injective : Function.Injective Zeta23.reflect`
- `lemma MNF.RH.reflect_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) : Zeta23.reflect ρ ∈ zerosIn T₁ T₂`
- `lemma MNF.RH.zeta_order_reflectZ {ρ : ℂ} (hz : is_nontrivial_zero ρ) : zeta_order (Zeta23.reflect ρ) = zeta_order ρ`
- `lemma MNF.RH.reflect_bijOn (A B : Set ℂ) (hAB : MapsTo Zeta23.reflect A B) (hBA : MapsTo Zeta23.reflect B A) : BijOn Zeta23.reflect A B`
- `lemma MNF.RH.reflect_bijOn_zerosIn (T : ℝ) : BijOn Zeta23.reflect (zerosIn 0 T) (zerosIn 0 T)`

### unproved

(none)

### notes

Compiled with `lake env lean` on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e); `#print axioms` for signedReservoir_eq_zero, sum_right_eq_sum_left and reservoirMass_eq_two_right each report exactly [propext, Classical.choice, Quot.sound]. No sorries, no warnings. Route as specified: Zeta23.reflect (ρ ↦ 1 − conj ρ) is an involution of zerosIn 0 T (zetaZeroConfig.reflect_mem + reflect_im), preserves zeta_order (zetaZeroConfig.mult_reflect, usable by rfl since is_nontrivial_zero/zeta_order are definitionally IsNontrivialZero/zeroMult), and negates Re ρ − 1/2; finsum_mem_eq_of_bijOn + finsum_mem_neg_distrib give S = −S. reservoirMass_eq_two_right splits zerosIn 0 T into the two open half-strips via finsum_mem_inter_support_eq' (the summand vanishes on Re ρ = 1/2), finsum_mem_union, abs_of_pos/abs_of_neg, then sum_right_eq_sum_left. Two caveats for the integrator: (1) No X3 deliverable exists yet under density-work/reservoir (the directory did not exist before this node), so reservoirMass was defined as the natural reading, Σ_{ρ ∈ zerosIn 0 T} zeta_order ρ * |Re ρ − 1/2| (ℝ-valued); if X3's definition differs textually, only the `unfold reservoirMass` line of reservoirMass_eq_two_right needs re-checking. (2) The tree already has MNF.RH.zeta_order_reflect (Core.lean:281, stated for 1 − ρ), so the multiplicity lemma here is named zeta_order_reflectZ to avoid the clash. The lemma is in namespace MNF.RH but imports Zeta23.BohrLandau (for zetaZeroConfig and reflect); it is a scratch file, not part of the MNF.RH library proper.

## merge report

MERGED: proved; file /tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/reservoir/merged/ReservoirMass.lean (1234 lines; compile log compile3.log beside it); imports ["Mathlib","Zeta23.BL.BohrLandauClosure","Zeta23.BohrLandau","Zeta23.Superlinear","Zeta23.RvM.NcountWindow","MNF.RH.GapDensity","MNF.RH.Counting"]

Compiled with exactly `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>`: exit 0, zero errors, zero warnings (18 s wall). No `sorry` anywhere outside the header comment. 65 `#print axioms` lines (every theorem and lemma in the file; the four `noncomputable def`s CG, meanSquareB, A₀, reservoirMass have no proof term), each reporting exactly [propext, Classical.choice, Quot.sound]. No duplicate declaration names. Nothing under the zeta23 tree was created, modified or deleted (`find -newer` on the tree outside .lake is empty).

Structure: header comment in the DensityPartial.lean register ([PROVED | this tree]; what is proved; "What this is not", stating plainly that T (log T)^{3/5} is far weaker than Littlewood's O(T log log T) and Selberg's O(T) for the same sum, and that nothing bears on `SpectralGapHyp` or the 7/8 theorem); one import block; `set_option maxHeartbeats 400000` once; six content sections, each with its own `open`s scoped inside `section … end`: §1 MeanSquareExplicit (Zeta23.BL), §2 BohrLandauExplicit (Zeta23.BL), §3 RiemannVonMangoldtShape (Zeta23, `noncomputable section`, `open Finset`), §4 LayerCake (MNF.RH; inner headers renumbered §4.1–§4.7), §5 ReflectionSymmetry (MNF.RH; X6's duplicate `reservoirMass` def dropped, X3's kept), §6 ReservoirBound (MNF.RH); then the axiom audit. Each lemma appears once (X1's text taken from X1, not from its verbatim copies in X2/X5; X2/X3/X4 taken from their originals, not X5's copies). Node names removed from all docstrings and section headers (`grep "X[1-6]"` on the file is empty); cross-references now name the lemmas (`Ncount_le_mul_log`, `bohrLandau_explicit`, `mul_log_le_Ncount`).

sorry-free list (standard axioms [propext, Classical.choice, Quot.sound] only), 65 declarations:
§1 Zeta23.BL: one_half_pos', CG_nonneg, CG_spec, zeta_approx_segment_half, meanSquare_sharp_param_half, tsum_one_div_rpow_two_sq_le, meanSquareB_nonneg, meanSquare_explicit_small_B, meanSquare_explicit_small, meanSquareUnifFrom_explicit, meanSquareUnifFrom_explicit'
§2 Zeta23.BL: NRight_le_Ncount, Rout_half, rin_half, hwin_half_ge, log_half_ge, K_half_ge, rpow_neg_five_half_mul, log_three_nonneg, A₀_nonneg, NRight_explicit, bohrLandau_explicit
§3 Zeta23: Ncount_self, Ncount_zero_nat, Ncount_unit_le, Ncount_le_mul_log, ell1_half, mul_log_le_Ncount, MNF_Ncount_eq, MNF_Ncount_le_mul_log, MNF_mul_log_le_Ncount
§4 MNF.RH: abs_re_sub_half_lt_half, abs_re_sub_half_le_half, NOff_eq_sum_ite, NOff_real_eq_sum_indicator, NOff_anti, NOff_antitone, NOff_intervalIntegrable, indicator_le_antitone, term_intervalIntegrable, integral_indicator_le_eq, reservoirMass_eq_integral, reservoirMass_nonneg, reservoirMass_le_half_Ncount, integral_NOff_split, integral_NOff_le_mul_Ncount, integral_NOff_tail_le, reservoirMass_le_split, reservoirMass_le_eps_Ncount
§5 MNF.RH: reflect_re, reflect_im, reflect_reflect, reflect_injective, reflect_mem_zerosIn, zeta_order_reflectZ, reflect_bijOn, reflect_bijOn_zerosIn, signedReservoir_eq_zero, sum_right_eq_sum_left, reservoirMass_eq_two_right
§6 MNF.RH: rpow_tail_intervalIntegrable, integral_rpow_tail_le, reservoirMass_le_rpow, reservoirMass_le_Ncount_mul, meanDisplacement_tendsto_zero
Definitions (noncomputable, no axiom audit applicable): Zeta23.BL.CG, Zeta23.BL.meanSquareB, Zeta23.BL.A₀, MNF.RH.reservoirMass.

sorryAx list: empty. No upstream node left a sorry, so nothing in the merged module depends on sorryAx.

Summary: With reservoirMass T := Σ_{ρ ∈ zerosIn 0 T} zeta_order ρ · |Re ρ − 1/2| (the multiplicity-weighted total distance of the zeros with 0 < Im ρ ≤ T from the critical line), the module proves unconditionally on the tree: the layer-cake identity reservoirMass T = ∫₀^{1/2} NOff δ 0 T dδ with the split bounds mass ≤ δ₀·N(0,T) + (1/2 − δ₀)·N_off(δ₀); the reflection symmetry (signed sum Σ m(ρ)(Re ρ − 1/2) = 0, mass = 2 × right-half signed mass); an explicit mean square ∫₁ᵀ‖ζ(σ+it)‖² ≤ (4/(2σ₁−1) + 951 + 4CG²)·T for 1/2 < σ₁ ≤ 3/4, σ ≥ σ₁, T ≥ 2, where CG is the one non-numeral constant (the tree's existential approximate-formula constant at σ₀ = 1/2); an explicit Bohr–Landau bound NOff δ 0 T ≤ (2A₀·δ^{−5/2} + N(0,4))·T for 0 < δ ≤ 1/2, T ≥ 2, A₀ = 54 + (27/2)(951 + 4CG²) + 12 log 3; the Riemann–von Mangoldt shape T log T/(16π) ≤ N(0,T) ≤ 4A₀'·T log T for large T (from riemannVonMangoldt_zeta.main and .local_count); and, splitting the layer cake at δ₀ = (log T)^{−2/5}, the bound reservoirMass T ≤ A·T·(log T)^{3/5}, equivalently ≤ A·(log T)^{−2/5}·N(0,T), hence reservoirMass T / N(0,T) → 0: the mean distance of the zeros from the line tends to 0 at rate (log T)^{−2/5}, with A explicit up to CG. As the header says plainly, T (log T)^{3/5} is far weaker than Littlewood's T log log T and Selberg's O(T) for the same sum (the exponent 3/5 is forced by the δ^{−5/2} of the available Bohr–Landau route; the gain over the trivial (1/2)N(0,T) is only the factor (log T)^{−2/5}), and nothing here bears on the gap hypothesis, implies or is implied by a zero-free strip, or uses the 7/8 theorem.
