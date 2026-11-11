# The strip cube: zones, degeneracy, and the pair measure — plan

Module to produce: `MNF/RH/Cube.lean` on the zeta23 tree (namespace `MNF.RH`), importing
`MNF.RH.ReservoirMass`. The DEFINITIONS block is `CUBE_DEFS.lean` in this folder (frozen: copy it
verbatim, change no body; it compiles on the tree as it stands).

Conventions. Standard axioms only; compile after every lemma; no `sorry` reported as proved.
Statements must mention only Mathlib names and names of the `MNF.RH` namespace (`is_nontrivial_zero`,
`zeta_order`, `zerosIn`, `Ncount`, `NOff`, `NOffLine`, `N0`, `AllZerosSimple`, `SpectralGapHyp`,
`reservoirMass`, the block's names). A lemma whose STATEMENT needs a zeta23-internal name
(`Zeta23.reflect`, `Zeta23.zetaZeroConfig`, `Zeta23.Ncount`, `ell1`, ...) must be named `aux_…`
(such lemmas are kept out of the challenge). Proofs may use anything.

Tree facts available (all in `MNF.RH` unless said; verified by grep):
- `is_nontrivial_zero ρ := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1` (Core.lean:52);
  `zeta_order ρ := (analyticOrderAt riemannZeta ρ).toNat` (Core.lean:58);
  `analyticOrderAt_riemannZeta_ne_top {s} (hs : s.re < 1)` (Core.lean:95);
  `AllZerosSimple := ∀ ρ, is_nontrivial_zero ρ → zeta_order ρ = 1` (Core.lean:63);
  `nontrivial_zero_reflect (h) : is_nontrivial_zero (1 - ρ)` (Core.lean:167; note: 1 − ρ, not 1 − ρ̄).
- `zerosIn T₁ T₂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}` (Counting.lean:52);
  `Ncount T₁ T₂ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ`; `zerosIn_finite T₁ T₂` (Counting.lean:96);
  `Ncount_eq_sum`, `Ndist_le_Ncount` (Counting.lean).
- `NOff δ T₁ T₂ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1/2|}, zeta_order ρ` (GapDensity.lean:68);
  `N0` (line 64); `NOffLine T₁ T₂ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1/2}, zeta_order ρ`
  (Density.lean:72); `NOff_le_NOffLine`; `offLine_le_one_third` (Density.lean:188, read its exact form).
- `SpectralGapHyp Δ := SpectralGapProperty ShiftedZeroSpectrum Δ` with
  `SpectralGapProperty S Δ := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ` (Gap.lean:34) and
  `ShiftedZeroSpectrum := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}` (Core.lean:61);
  `spectralGapHyp_iff_zeroFree_strip : SpectralGapHyp Δ ↔ ∀ s, 1/2 < s.re → s.re < 1/2 + Δ → riemannZeta s ≠ 0`
  (Hypotheses.lean:85).
- Reflection, in `MNF/RH/ReservoirMass.lean` §5 (all stated with `Zeta23.reflect ρ := 1 - (starRingEnd ℂ) ρ`,
  which is definitionally `mirror ρ`): `reflect_re`, `reflect_im`, `reflect_reflect`, `reflect_injective`,
  `reflect_mem_zerosIn {T₁ T₂} {ρ} (h : ρ ∈ zerosIn T₁ T₂) : Zeta23.reflect ρ ∈ zerosIn T₁ T₂`,
  `zeta_order_reflectZ {ρ} (hz : is_nontrivial_zero ρ) : zeta_order (Zeta23.reflect ρ) = zeta_order ρ`,
  `reflect_bijOn_zerosIn`; the bare-zero form is `Zeta23.zetaZeroConfig.reflect_mem ρ hz : is_nontrivial_zero (Zeta23.reflect ρ)`.
  Also `abs_re_sub_half_le_half (h : is_nontrivial_zero ρ)` (ReservoirMass.lean:685),
  `reservoirMass`, `reservoirMass_eq_integral`, `NOff_real_eq_sum_indicator`, `NOff_eq_sum_ite`.
- Mathlib: `analyticOrderAt_eq_zero` / `analyticOrderAt_ne_zero` style lemmas (grep
  `.lake/packages/mathlib/Mathlib/Analysis/Analytic/Order.lean`) for "order ≥ 1 at a zero";
  `finsum_mem_eq_finite_toFinset_sum`, `finsum_mem_union`, `finsum_mem_inter_support`,
  `Finset.sum_product'`, `Finset.sum_comm`, `Finset.sum_le_sum`, `Finset.sum_nonneg`,
  `Finset.sum_mul`, `Finset.mul_sum`; `Complex.ext_iff`; `starRingEnd` lemmas (`Complex.conj_re`, `Complex.conj_im`).
  Whether Mathlib at this pin has conjugation symmetry of the zeros (a lemma giving
  `riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s)`) is NOT known: grep for it; if absent,
  state the positive-ordinate versions below and say so.

## Stage 1 (parallel)

### Node ZONES (`Cube/Zones`): the mirror, the zones, degeneracy
1. `mirror_re (ρ) : (mirror ρ).re = 1 - ρ.re`; `mirror_im (ρ) : (mirror ρ).im = ρ.im`;
   `mirror_mirror (ρ) : mirror (mirror ρ) = ρ`; `mirror_injective : Function.Injective mirror`.
2. `aux_mirror_eq_reflect (ρ) : mirror ρ = Zeta23.reflect ρ := rfl` (aux: statement names zeta23).
3. `is_nontrivial_zero_mirror {ρ} (hz : is_nontrivial_zero ρ) : is_nontrivial_zero (mirror ρ)`;
   `mirror_mem_zerosIn {T₁ T₂ ρ} (h : ρ ∈ zerosIn T₁ T₂) : mirror ρ ∈ zerosIn T₁ T₂`;
   `zeta_order_mirror {ρ} (hz : is_nontrivial_zero ρ) : zeta_order (mirror ρ) = zeta_order ρ`.
4. `mirror_eq_self_iff (ρ) : mirror ρ = ρ ↔ OnLine ρ`.
5. `one_le_zeta_order {ρ} (hz : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ`
   (order ≠ 0 since ζ ρ = 0 and ζ is analytic at ρ; order ≠ ⊤ by `analyticOrderAt_riemannZeta_ne_top`).
6. **`degenerate_of_not_onLine {ρ} (hz : is_nontrivial_zero ρ) (h : ¬ OnLine ρ) : Degenerate ρ`**
   (the projection-degeneracy lemma: the partner is `mirror ρ`).
7. `onLine_and_simple_of_not_degenerate {ρ} (hz) (h : ¬ Degenerate ρ) : OnLine ρ ∧ zeta_order ρ = 1`.
8. `not_degenerate_of_onLine_simple (hall : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) {ρ} (hz) (h1 : zeta_order ρ = 1) : ¬ Degenerate ρ`
   (two on-line zeros with the same imaginary part are equal: `Complex.ext`).
9. **`noDegenerate_iff : (∀ ρ, is_nontrivial_zero ρ → ¬ Degenerate ρ) ↔ (∀ ρ, is_nontrivial_zero ρ → OnLine ρ) ∧ AllZerosSimple`**.
10. Zone bookkeeping: `inBand_or_inReservoir_or_onLine {Δ} (hΔ : 0 < Δ) (ρ) : OnLine ρ ∨ InBand Δ ρ ∨ InReservoir Δ ρ`
    (exclusive is nice but not required); `inBand_mirror_iff (Δ ρ) : InBand Δ (mirror ρ) ↔ InBand Δ ρ`;
    `mem_bandZeros_mirror {Δ ρ} (h : ρ ∈ bandZeros Δ) : mirror ρ ∈ bandZeros Δ`.

### Node PAIRS-A (`Cube/PairsA`): the pair measure's marginals (no mirror needed)
1. `pairSum_eq_sum (T f) : pairSum T f = ∑ ρ ∈ (zerosIn_finite 0 T).toFinset, ∑ ρ' ∈ (zerosIn_finite 0 T).toFinset, …`
   — an internal rewriting lemma; name it `aux_pairSum_eq_finset_sum` if its statement must mention `.toFinset`
   of the finiteness proof (that is a proof term in a statement: keep such lemmas `aux_`).
2. `pairSum_const (T) : pairSum T (fun _ _ _ => 1) = (Ncount 0 T : ℝ) ^ 2`.
3. `pairSum_fst (T g) : pairSum T (fun a _ _ => g a) = (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2)`;
   `pairSum_snd (T g) : pairSum T (fun _ b _ => g b) = (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2)`.
4. `pairSum_fst_indicator (T δ) : pairSum T (fun a _ _ => if δ ≤ |a| then 1 else 0) = (Ncount 0 T : ℝ) * (NOff δ 0 T : ℝ)`.
5. **`pairSum_fst_abs (T) : pairSum T (fun a _ _ => |a|) = (Ncount 0 T : ℝ) * reservoirMass T`** and
   **`pairSum_fst_abs_eq_integral (T) : pairSum T (fun a _ _ => |a|) = (Ncount 0 T : ℝ) * ∫ δ in (0:ℝ)..(1/2), (NOff δ 0 T : ℝ)`**
   (the double layer cake, from `reservoirMass_eq_integral`).
6. `pairSum_swap (T f) : pairSum T f = pairSum T (fun a b s => f b a (-s))`.
7. `pairSum_nonneg (T) {f} (hf : ∀ a b s, 0 ≤ f a b s) : 0 ≤ pairSum T f`;
   `pairSum_mono (T) {f g} (h : ∀ a b s, f a b s ≤ g a b s) : pairSum T f ≤ pairSum T g`.
8. `diagonalMass_nonneg`, `diagonalMass_le_sq_Ncount (T) : diagonalMass T ≤ (Ncount 0 T : ℝ) ^ 2`,
   `Ncount_le_diagonalMass (T) : (Ncount 0 T : ℝ) ≤ diagonalMass T` (needs `1 ≤ zeta_order` on zeros:
   prove a local copy of `one_le_zeta_order` as in ZONES item 5; the merge keeps one).

## Stage 2 (parallel; each node receives the ZONES file text verbatim and copies what it needs)

### Node GAP (`Cube/Gap`): the band and the gap
1. `spectralGapHyp_iff_not_inBand (Δ) : SpectralGapHyp Δ ↔ ∀ ρ, is_nontrivial_zero ρ → ¬ InBand Δ ρ`
   (→: a zero with 1/2 − Δ < Re < 1/2 has its mirror in the right band; ←: `spectralGapHyp_iff_zeroFree_strip`).
2. **`spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros (Δ) : SpectralGapHyp Δ ↔ OrdinatesInjectiveOn (bandZeros Δ)`**.
3. `bandCoincidentMass_eq_zero_of_spectralGapHyp {Δ} (h : SpectralGapHyp Δ) (T) : bandCoincidentMass Δ T = 0`.
4. `not_inBand_of_bandCoincidentMass_eq_zero {Δ} (h : ∀ T, bandCoincidentMass Δ T = 0) {ρ} (hz : is_nontrivial_zero ρ) (hpos : 0 < ρ.im) : ¬ InBand Δ ρ`
   (take T := ρ.im; the ordered pair (ρ, mirror ρ) contributes (zeta_order ρ)² ≥ 1 to a sum of nonnegative terms).
5. If conjugation symmetry of the zeros is available (Mathlib lemma, or provable from
   `riemannZeta` being real on the real axis — check `riemannZeta_conj` / `riemannZeta_ofReal` and whether the
   tree has anything), and zeros with Im ρ = 0 can be excluded (ζ(σ) ≠ 0 for real 0 < σ < 1 — check Mathlib;
   if not available, skip): **`spectralGapHyp_iff_bandCoincidentMass (Δ) : SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0`**.
   Otherwise deliver 3 and 4 and say so in notes.
6. `bandCoincidentMass_nonneg`, `bandCoincidentMass_le_offDiagonalCoincidentMass (Δ T)`.

### Node PAIRS-B (`Cube/PairsB`): the atom at s = 0
1. **`coincidentMass_eq (T) : coincidentMass T = diagonalMass T + offDiagonalCoincidentMass T`**.
2. `offDiagonalCoincidentMass_nonneg (T)`.
3. **`offLine_sq_le_offDiagonalCoincidentMass (T) : ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | ρ.re ≠ 1 / 2}, (zeta_order ρ : ℝ) ^ 2 ≤ offDiagonalCoincidentMass T`**
   (each off-line ρ pairs with `mirror ρ`, which is in the window, distinct, with the same ordinate and the same multiplicity).
4. `offDiagonalCoincidentMass_le (T) : offDiagonalCoincidentMass T ≤ (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ)`
   (the inner sum is ≤ Ncount; the outer sum over ρ with a nonempty inner set is over off-line zeros only — an
   on-line zero has no distinct partner with the same ordinate — so bound by Σ_{off-line} m(ρ)·Ncount).
5. `offDiagonalCoincidentMass_eq_zero_of_onLine (h : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) (T) : offDiagonalCoincidentMass T = 0`.
6. `onLine_of_offDiagonalCoincidentMass_eq_zero (h : ∀ T, offDiagonalCoincidentMass T = 0) {ρ} (hz) (hpos : 0 < ρ.im) : OnLine ρ`.
7. **`offDiagonalCoincidentMass_le_third : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, offDiagonalCoincidentMass T ≤ (1 / 3 + ε) * (Ncount 0 T : ℝ) ^ 2`**
   (from 4 and `offLine_le_one_third`).

## Merge
One module `Cube.lean`: header in the style of `MNF/RH/DensityPartial.lean` (what is proved; that
every statement is bookkeeping over finite sums of zeros; that the equivalences RELOCATE the gap and
RH, they do not prove them; that the cubic small-distance law is the GUE prediction and is not a
theorem; no node names), the frozen block once, sections by content, each lemma once, `#print axioms`
for every theorem and lemma at the end.
