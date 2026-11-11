# Strip-cube workflow: node reports (2026-11-04)

## zones: proved

- file: `Zones.lean`

### proved

- `lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re`
- `lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im`
- `lemma mirror_mirror (ρ : ℂ) : mirror (mirror ρ) = ρ`
- `lemma mirror_injective : Function.Injective mirror`
- `lemma aux_mirror_eq_reflect (ρ : ℂ) : mirror ρ = Zeta23.reflect ρ := rfl`
- `lemma is_nontrivial_zero_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) : is_nontrivial_zero (mirror ρ)`
- `lemma mirror_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) : mirror ρ ∈ zerosIn T₁ T₂`
- `lemma zeta_order_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) : zeta_order (mirror ρ) = zeta_order ρ`
- `lemma mirror_eq_self_iff (ρ : ℂ) : mirror ρ = ρ ↔ OnLine ρ`
- `lemma one_le_zeta_order {ρ : ℂ} (hz : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ`
- `theorem degenerate_of_not_onLine {ρ : ℂ} (hz : is_nontrivial_zero ρ) (h : ¬ OnLine ρ) : Degenerate ρ`
- `lemma onLine_and_simple_of_not_degenerate {ρ : ℂ} (hz : is_nontrivial_zero ρ) (h : ¬ Degenerate ρ) : OnLine ρ ∧ zeta_order ρ = 1`
- `lemma not_degenerate_of_onLine_simple (hall : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) {ρ : ℂ} (hz : is_nontrivial_zero ρ) (h1 : zeta_order ρ = 1) : ¬ Degenerate ρ`
- `theorem noDegenerate_iff : (∀ ρ, is_nontrivial_zero ρ → ¬ Degenerate ρ) ↔ (∀ ρ, is_nontrivial_zero ρ → OnLine ρ) ∧ AllZerosSimple`
- `lemma inBand_or_inReservoir_or_onLine {Δ : ℝ} (hΔ : 0 < Δ) (ρ : ℂ) : OnLine ρ ∨ InBand Δ ρ ∨ InReservoir Δ ρ`
- `lemma inBand_mirror_iff (Δ : ℝ) (ρ : ℂ) : InBand Δ (mirror ρ) ↔ InBand Δ ρ`
- `lemma mem_bandZeros_mirror {Δ : ℝ} {ρ : ℂ} (h : ρ ∈ bandZeros Δ) : mirror ρ ∈ bandZeros Δ`

### unproved

(none)

### notes

Node ZONES, items 1-10 all proved. The file compiles on the zeta23 tree with the exact command (exit 0, no errors, no warnings, no sorry); the file ends with a `#print axioms` block for all 17 declarations and every one prints exactly [propext, Classical.choice, Quot.sound]. The DEFINITIONS block is copied verbatim (verified by diff against CUBE_DEFS.lean); no definition body changed; nothing under the zeta23 tree was touched.

Statement shapes: all 17 statements match the plan's hypothesis order and names; no deviations. One remark: in `inBand_or_inReservoir_or_onLine` the hypothesis `hΔ : 0 < Δ` is not used (the trichotomy holds for every Δ); I kept the plan's shape and silenced the unused-variable linter locally with `set_option linter.unusedVariables false in` immediately before that lemma (statement unchanged). The merge may drop `hΔ` if a cleaner statement is preferred.

Proof dependencies (proofs only, statements stay in MNF.RH + Mathlib): `is_nontrivial_zero_mirror` is `Zeta23.zetaZeroConfig.reflect_mem ρ hz` (definitional since mirror = Zeta23.reflect); `mirror_mem_zerosIn` is the tree's `reflect_mem_zerosIn`; `zeta_order_mirror` is the tree's `zeta_order_reflectZ` (which delegates to `zetaZeroConfig.mult_reflect`); `one_le_zeta_order` is the tree's existing `zeta_order_ge_one` (Core.lean:116) — the merge could simply use that name instead of a duplicate. `aux_mirror_eq_reflect` is `rfl` and is the only aux_ lemma (its statement names Zeta23.reflect). The degeneracy lemmas 6-9 use only mirror_* , Complex.ext, omega and the plan's logic; `degenerate_of_not_onLine` and `noDegenerate_iff` are declared `theorem`, the rest `lemma`.

Exclusivity of the three zones (not required by the plan) was not stated. No Mathlib conjugation-symmetry lemma was needed for this node.

## pairsA: proved

- file: `PairsA.lean`

### proved

- `theorem pairSum_eq_sum {T : ℝ} (hfin : (zerosIn 0 T).Finite) (f : ℝ → ℝ → ℝ → ℝ) : pairSum T f = ∑ ρ ∈ hfin.toFinset, ∑ ρ' ∈ hfin.toFinset, (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im)`
- `theorem aux_pairSum_eq_finset_sum (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : pairSum T f = ∑ ρ ∈ (zerosIn_finite 0 T).toFinset, ∑ ρ' ∈ (zerosIn_finite 0 T).toFinset, (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im)`
- `theorem pairSum_const (T : ℝ) : pairSum T (fun _ _ _ => 1) = (Ncount 0 T : ℝ) ^ 2`
- `theorem pairSum_fst (T : ℝ) (g : ℝ → ℝ) : pairSum T (fun a _ _ => g a) = (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2)`
- `theorem pairSum_snd (T : ℝ) (g : ℝ → ℝ) : pairSum T (fun _ b _ => g b) = (Ncount 0 T : ℝ) * ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * g (ρ.re - 1 / 2)`
- `theorem pairSum_fst_indicator (T δ : ℝ) : pairSum T (fun a _ _ => if δ ≤ |a| then 1 else 0) = (Ncount 0 T : ℝ) * (NOff δ 0 T : ℝ)`
- `theorem pairSum_fst_abs (T : ℝ) : pairSum T (fun a _ _ => |a|) = (Ncount 0 T : ℝ) * reservoirMass T`
- `theorem pairSum_fst_abs_eq_integral (T : ℝ) : pairSum T (fun a _ _ => |a|) = (Ncount 0 T : ℝ) * ∫ δ in (0 : ℝ)..(1 / 2), (NOff δ 0 T : ℝ)`
- `theorem pairSum_swap (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : pairSum T f = pairSum T (fun a b s => f b a (-s))`
- `theorem pairSum_nonneg (T : ℝ) {f : ℝ → ℝ → ℝ → ℝ} (hf : ∀ a b s, 0 ≤ f a b s) : 0 ≤ pairSum T f`
- `theorem pairSum_mono (T : ℝ) {f g : ℝ → ℝ → ℝ → ℝ} (h : ∀ a b s, f a b s ≤ g a b s) : pairSum T f ≤ pairSum T g`
- `theorem diagonalMass_nonneg (T : ℝ) : 0 ≤ diagonalMass T`
- `theorem diagonalMass_le_sq_Ncount (T : ℝ) : diagonalMass T ≤ (Ncount 0 T : ℝ) ^ 2`
- `theorem Ncount_le_diagonalMass (T : ℝ) : (Ncount 0 T : ℝ) ≤ diagonalMass T`

### unproved

(none)

### notes

Node PAIRS-A, items 1-8, all delivered. The file compiles with `cd /home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>` with exit 0, no errors, no warnings, no sorry; `#print axioms` for all 14 lemmas (at the end of the file) reports only [propext, Classical.choice, Quot.sound]. The DEFINITIONS block (CUBE_DEFS.lean lines 1-60) is copied verbatim (checked by diff); the lemmas sit inside `namespace MNF.RH` before the final `end MNF.RH`; nothing under the zeta23 tree was modified.

Deviations from the plan's statement shapes:
(1) Item 1 is delivered twice: `pairSum_eq_sum {T : ℝ} (hfin : (zerosIn 0 T).Finite) (f)` takes the finiteness proof as a HYPOTHESIS (same convention as the tree's `Ncount_eq_sum`), so its statement contains no proof term and it needs no `aux_` prefix; `aux_pairSum_eq_finset_sum (T f)` is the plan's literal form with `(zerosIn_finite 0 T).toFinset` in the statement, hence `aux_` as the plan prescribes. The merge may keep either or both (all later proofs use `pairSum_eq_sum (zerosIn_finite 0 T)`).
(2) Item 8: no local copy of `one_le_zeta_order` was needed. The tree already has `MNF.RH.zeta_order_ge_one {ρ} (h : is_nontrivial_zero ρ) : 1 ≤ zeta_order ρ` (Core.lean:116, standard axioms), which `Ncount_le_diagonalMass` uses directly; ZONES item 5 (`one_le_zeta_order`) can likewise be an alias of it.
(3) All other statements follow the plan's shapes exactly (hypothesis order, names, implicit/explicit binders as written in the plan). In `pairSum_fst_indicator` the branches `1`/`0` are elaborated as ℝ through `pairSum`'s type; decidability of `δ ≤ |a|` is Real's classical instance.

Mathlib names used (all verified by grep in .lake/packages/mathlib): finsum_mem_eq_finite_toFinset_sum, Finset.sum_congr, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_comm, Finset.sum_nonneg, Finset.sum_le_sum, Finset.single_le_sum, le_self_pow₀, mul_le_mul_of_nonneg_left, mul_nonneg, sq_nonneg, Nat.cast_nonneg, neg_sub, sq, Set.Finite.mem_toFinset. Tree names used: zerosIn_finite, Ncount_eq_sum, zeta_order_ge_one, NOff_eq_sum_ite, reservoirMass (unfolded by rfl in pairSum_fst_abs), reservoirMass_eq_integral.

Proof sketches: pairSum_const/fst/snd rewrite both sides to Finset double sums and apply Finset.sum_mul_sum then `ring` termwise (pairSum_fst needs a `mul_comm` first so the g-dependent factor sits on the outer index); pairSum_fst_indicator reduces via pairSum_fst to NOff_eq_sum_ite with `split_ifs <;> simp`; pairSum_fst_abs is pairSum_fst followed by `rfl` (reservoirMass's body is literally that finsum); pairSum_swap is Finset.sum_comm plus neg_sub and mul_comm; diagonalMass_le_sq_Ncount uses m(ρ)·m(ρ) ≤ m(ρ)·Σm via Finset.single_le_sum; Ncount_le_diagonalMass uses 1 ≤ m(ρ) ⇒ m(ρ) ≤ m(ρ)^2 (le_self_pow₀). Compile time ~11 s per run on this machine (Mathlib oleans cached).

## gap: partial

- file: `Gap.lean`

### proved

- `theorem spectralGapHyp_iff_not_inBand (Δ : ℝ) : SpectralGapHyp Δ ↔ ∀ ρ, is_nontrivial_zero ρ → ¬ InBand Δ ρ`
- `theorem spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros (Δ : ℝ) : SpectralGapHyp Δ ↔ OrdinatesInjectiveOn (bandZeros Δ)`
- `theorem bandCoincidentMass_eq_zero_of_spectralGapHyp {Δ : ℝ} (h : SpectralGapHyp Δ) (T : ℝ) : bandCoincidentMass Δ T = 0`
- `theorem not_inBand_of_bandCoincidentMass_eq_zero {Δ : ℝ} (h : ∀ T, bandCoincidentMass Δ T = 0) {ρ : ℂ} (hz : is_nontrivial_zero ρ) (hpos : 0 < ρ.im) : ¬ InBand Δ ρ`
- `lemma is_nontrivial_zero_conj {ρ : ℂ} (hz : is_nontrivial_zero ρ) : is_nontrivial_zero ((starRingEnd ℂ) ρ)   [extra, not in the plan]`
- `theorem spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero (hreal : ∀ ρ, is_nontrivial_zero ρ → ρ.im ≠ 0) (Δ : ℝ) : SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0   [extra: item 5 under an explicit no-real-zero hypothesis]`
- `theorem bandCoincidentMass_nonneg (Δ T : ℝ) : 0 ≤ bandCoincidentMass Δ T`
- `theorem bandCoincidentMass_le_offDiagonalCoincidentMass (Δ T : ℝ) : bandCoincidentMass Δ T ≤ offDiagonalCoincidentMass T`

### unproved

- theorem spectralGapHyp_iff_bandCoincidentMass (Δ : ℝ) : SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0   [plan item 5, unconditional form: not delivered — see notes]

### notes

Node GAP: items 1, 2, 3, 4, 6 proved in the plan's exact statement shapes (hypothesis order and names unchanged). Item 5 is delivered as the plan's fallback (items 3 and 4) plus an explicitly conditional variant. The file compiles on the zeta23 tree with the exact command (exit 0, no errors, no warnings, no sorry) and ends with a `#print axioms` block: all 8 declarations print exactly [propext, Classical.choice, Quot.sound]. The DEFINITIONS block is byte-identical to CUBE_DEFS.lean (verified by diff); no definition body changed; nothing under the zeta23 tree was touched. No aux_ lemma is needed in this node (no statement mentions a zeta23-internal name or a finiteness proof term).

Item 5 (why unconditional form is not delivered): Mathlib at this pin HAS the conjugation symmetry `riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s)` (Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458, reachable through the tree's imports, used in `is_nontrivial_zero_conj`), but NEITHER Mathlib nor the tree has a lemma excluding real zeros, i.e. `riemannZeta σ ≠ 0` for real `0 < σ < 1` (grepped Mathlib/NumberTheory for sign/nonvanishing results on the real axis: only `riemannZeta_pos_of_one_lt`, `riemannZeta_ne_zero_of_one_lt_re`, `riemannZeta_one_ne_zero`; no Dirichlet-eta/alternating-series representation on 0 < Re s < 1). A real nontrivial zero has ordinate 0, lies in no window (0, T], and is therefore invisible to `bandCoincidentMass`, so the ← direction of item 5 cannot be closed without that fact. Delivered instead: `spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero (hreal : ∀ ρ, is_nontrivial_zero ρ → ρ.im ≠ 0) (Δ)`; its proof handles negative ordinates by conjugation (`is_nontrivial_zero_conj`, `Complex.conj_re`, `Complex.conj_im`) and positive ones by item 4. If a real-zero exclusion ever becomes available, the unconditional item 5 is `spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero (fun ρ hz => <that lemma>) Δ`.

Proof-route deviation (statement unchanged): item 1 is proved directly from the definition `SpectralGapProperty S Δ := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ` with `x = ρ.re - 1/2 ∈ ShiftedZeroSpectrum` (both directions), not via `spectralGapHyp_iff_zeroFree_strip` and the mirror as the plan sketched; the mirror enters in item 2 (←) and item 4 instead.

Upstream copied verbatim from ZONES/Zones.lean (8 lemmas): mirror_re, mirror_im, is_nontrivial_zero_mirror, mirror_mem_zerosIn, zeta_order_mirror, mirror_eq_self_iff, one_le_zeta_order, mem_bandZeros_mirror. The merge should keep ZONES's copies and drop these.

Mathlib names used (all verified by grep at the pin): finsum_mem_eq_zero_of_forall_eq_zero, finsum_mem_eq_finite_toFinset_sum, finsum_nonneg, Finset.sum_nonneg, Finset.single_le_sum, Finset.sum_le_sum, Finset.sum_le_sum_of_subset_of_nonneg, Set.Finite.inter_of_left, Set.Finite.mem_toFinset, Complex.conj_re, Complex.conj_im, riemannZeta_conj, abs_pos, sub_ne_zero, lt_or_gt_of_ne; tree names: zerosIn_finite, zeta_order_ge_one, reflect_mem_zerosIn, zeta_order_reflectZ, Zeta23.zetaZeroConfig.reflect_mem (proofs only). Items 4 and 6 convert finsums over subsets of a window to Finset sums via `zerosIn_finite` and `Set.Finite.inter_of_left`; item 3 and `bandCoincidentMass_nonneg` work on the finsums directly.

## pairsB: partial

- file: `PairsB.lean`

### proved

- `theorem coincidentMass_eq (T : ℝ) : coincidentMass T = diagonalMass T + offDiagonalCoincidentMass T`
- `theorem offDiagonalCoincidentMass_nonneg (T : ℝ) : 0 ≤ offDiagonalCoincidentMass T`
- `theorem offLine_sq_le_offDiagonalCoincidentMass (T : ℝ) : ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | ρ.re ≠ 1 / 2}, (zeta_order ρ : ℝ) ^ 2 ≤ offDiagonalCoincidentMass T`
- `theorem offDiagonalCoincidentMass_le (T : ℝ) : offDiagonalCoincidentMass T ≤ (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ) + (N0 0 T : ℝ) * (NOffLine 0 T : ℝ)   [CORRECTED item 4; see notes]`
- `theorem offDiagonalCoincidentMass_le_two_mul (T : ℝ) : offDiagonalCoincidentMass T ≤ 2 * (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ)`
- `theorem offDiagonalCoincidentMass_eq_zero_of_onLine (h : ∀ ρ, is_nontrivial_zero ρ → OnLine ρ) (T : ℝ) : offDiagonalCoincidentMass T = 0`
- `theorem onLine_of_offDiagonalCoincidentMass_eq_zero (h : ∀ T, offDiagonalCoincidentMass T = 0) {ρ : ℂ} (hz : is_nontrivial_zero ρ) (hpos : 0 < ρ.im) : OnLine ρ`
- `theorem offDiagonalCoincidentMass_le_two_thirds : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, offDiagonalCoincidentMass T ≤ (2 / 3 + ε) * (Ncount 0 T : ℝ) ^ 2   [item 7 with the constant the corrected item 4 gives]`
- `theorem offDiagonalCoincidentMass_le_five_ninths : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, offDiagonalCoincidentMass T ≤ (5 / 9 + ε) * (Ncount 0 T : ℝ) ^ 2   [sharp constant of this bookkeeping]`
- `theorem Ncount_eq_N0_add_NOffLine (T₁ T₂ : ℝ) : Ncount T₁ T₂ = N0 T₁ T₂ + NOffLine T₁ T₂`
- `lemma finsum_mem_inter_setOf_eq_sum_filter {M : Type*} [AddCommMonoid M] {s : Set ℂ} (hs : s.Finite) (p : ℂ → Prop) [DecidablePred p] (g : ℂ → M) : ∑ᶠ x ∈ s ∩ {x | p x}, g x = ∑ x ∈ hs.toFinset.filter p, g x`
- `lemma NOffLine_real_eq_sum_filter {T : ℝ} (hfin : (zerosIn 0 T).Finite) : (NOffLine 0 T : ℝ) = ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.re ≠ 1 / 2), (zeta_order ρ : ℝ)`
- `lemma N0_real_eq_sum_filter {T : ℝ} (hfin : (zerosIn 0 T).Finite) : (N0 0 T : ℝ) = ∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.re = 1 / 2), (zeta_order ρ : ℝ)`
- `theorem pairSum_eq_sum {T : ℝ} (hfin : (zerosIn 0 T).Finite) (f : ℝ → ℝ → ℝ → ℝ) : pairSum T f = ∑ ρ ∈ hfin.toFinset, ∑ ρ' ∈ hfin.toFinset, (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im)   [copied verbatim from PAIRS-A]`
- `lemma mirror_re (ρ : ℂ) : (mirror ρ).re = 1 - ρ.re   [copied verbatim from ZONES]`
- `lemma mirror_im (ρ : ℂ) : (mirror ρ).im = ρ.im   [copied verbatim from ZONES]`
- `lemma mirror_mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} (h : ρ ∈ zerosIn T₁ T₂) : mirror ρ ∈ zerosIn T₁ T₂   [copied verbatim from ZONES]`
- `lemma zeta_order_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) : zeta_order (mirror ρ) = zeta_order ρ   [copied verbatim from ZONES]`
- `lemma mirror_eq_self_iff (ρ : ℂ) : mirror ρ = ρ ↔ OnLine ρ   [copied verbatim from ZONES]`

### unproved

- PLAN item 4 as literally stated: offDiagonalCoincidentMass T ≤ (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ) — not provable from the tree's facts (it would follow from RH); a corrected bound is delivered under the same name, see notes
- PLAN item 7 as literally stated (constant 1/3 + ε): offDiagonalCoincidentMass_le_third — not available since it rests on the unprovable item 4; the constants 2/3 + ε and 5/9 + ε are delivered instead (offDiagonalCoincidentMass_le_two_thirds, offDiagonalCoincidentMass_le_five_ninths)

### notes

Node PAIRS-B. The file compiles with the exact command (cd .../zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean <file>) with exit 0, no errors, no warnings, no sorry (grep count 0); `#print axioms` for all 19 declarations (end of file) prints exactly [propext, Classical.choice, Quot.sound]. The DEFINITIONS block is CUBE_DEFS.lean lines 1-60 copied verbatim (checked by diff: IDENTICAL); no definition body changed; the lemmas sit inside `namespace MNF.RH` before the final `end MNF.RH`. Nothing under the zeta23 tree was touched (find -mmin on the tree shows no file modified during this run; the git-status entries are the pre-existing stage-B setup). Compile log: .../PAIRSB/compile.log.

DEVIATION, item 4 (mathematical, not a Lean issue): the plan's statement `offDiag ≤ NOffLine · Ncount` cannot be proved. Its justification ("an on-line zero has no distinct partner with the same ordinate") is false unless every zero is on the line: an off-line zero may share its ordinate with an on-line zero, and nothing in the tree excludes it (it would follow from RH). Weighted counterexample to the inequality itself: an on-line zero of multiplicity 2 and a mirror pair of simple off-line zeros at one ordinate give offDiag = 2+2+2+1+2+1 = 10 while NOffLine·Ncount = 2·4 = 8. What the plan's argument does prove, delivered under the plan's name `offDiagonalCoincidentMass_le`: offDiag ≤ NOffLine·Ncount + N0·NOffLine (for an off-line ρ the partners weigh ≤ Ncount; for an on-line ρ every partner is off-line — two on-line zeros with one ordinate coincide by Complex.ext — so they weigh ≤ NOffLine). Corollary `offDiagonalCoincidentMass_le_two_mul`: offDiag ≤ 2·NOffLine·Ncount (via N0_le_Ncount). N0 is the tree's on-line count with multiplicity (GapDensity.lean:64), a name the plan allows.

DEVIATION, item 7: consequently the constant 1/3 is not available; the plan's name `offDiagonalCoincidentMass_le_third` is deliberately not used. Delivered: `offDiagonalCoincidentMass_le_two_thirds` (2/3 + ε, plan's binder shape, from the 2× bound and offLine_le_one_third at ε/2) and `offDiagonalCoincidentMass_le_five_ninths` (5/9 + ε, the sharp constant of this bookkeeping: with the exact split Ncount = N0 + NOffLine, the bound reads NOffLine·(2N − NOffLine) = N² − (N − NOffLine)² ≤ (1 − (2/3 − ε')²)N²; ε' := min(3ε/4, 2/3) keeps 1/3 + ε' ≤ 1). The split `Ncount_eq_N0_add_NOffLine (T₁ T₂)` (ℕ-valued, general window) is not in the tree and is proved here; the merge may want it in Density/GapDensity.

Items 1, 2, 3, 5, 6 have exactly the plan's statement shapes (hypothesis order, names, binders). Item 1 is `theorem`, items 2-6 as in the plan; none needs `aux_` (no zeta23 name, no proof term in any statement: the Finset-sum helpers take the finiteness proof as a hypothesis, the PAIRS-A convention).

Copied verbatim (scratch files cannot be imported; the merge keeps one copy each): `pairSum_eq_sum` from PAIRS-A (§B.0'); `mirror_re`, `mirror_im`, `mirror_mem_zerosIn`, `zeta_order_mirror`, `mirror_eq_self_iff` from ZONES (§B.0''). Local helpers: `finsum_mem_inter_setOf_eq_sum_filter` (generic ∑ᶠ over s ∩ {x | p x} → Finset.filter sum; used everywhere the inner partner set appears), `NOffLine_real_eq_sum_filter`, `N0_real_eq_sum_filter`.

Proof sketches: coincidentMass_eq rewrites both sides to Finset double sums, pulls the diagonal term with Finset.sum_ite_eq', and matches termwise by cases (ρ' = ρ / ρ'.im = ρ.im / neither). offLine_sq_le_offDiagonalCoincidentMass: restrict the outer sum to off-line zeros (sum_le_sum_of_subset_of_nonneg over filter_subset, inner sums nonnegative), then m(ρ)² = m(ρ)·m(mirror ρ) ≤ inner sum by Finset.single_le_sum with mirror ρ in the partner set (mirror_mem_zerosIn, mirror_eq_self_iff, mirror_im, zeta_order_mirror). offDiagonalCoincidentMass_le: write NOffLine, N0 as `if`-sums over the window (Finset.sum_filter), distribute (Finset.sum_mul, sum_add_distrib) and bound termwise by cases on ρ.re ≠ 1/2. _eq_zero_of_onLine: each partner set is empty (Complex.ext), finsum_mem_empty. onLine_of_..._eq_zero: take T := ρ.im, apply item 3, single_le_sum, one_le_pow₀ with zeta_order_ge_one.

Lean pitfalls met: `Finset.filter_subset _ _` leaves DecidablePred stuck — give the predicate explicitly; `Finset.single_le_sum` needs `(f := fun ρ' => m ρ * m ρ')` or the unifier picks a := ρ; `classical` at the top of every proof using Finset.filter. Mathlib names used (all verified by grep in .lake/packages/mathlib): finsum_mem_eq_finite_toFinset_sum, finsum_mem_empty, Finset.sum_filter, Finset.sum_ite_eq', Finset.sum_add_distrib, Finset.sum_congr, Finset.sum_nonneg, Finset.sum_le_sum, Finset.sum_le_sum_of_subset_of_nonneg, Finset.single_le_sum, Finset.filter_subset, Finset.mem_filter, Finset.sum_mul, Finset.mul_sum, Finset.sum_eq_zero, Set.Finite.subset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, one_le_pow₀, mul_self_le_mul_self, mul_le_mul_of_nonneg_left/right, mul_nonneg, Nat.cast_nonneg, sq_nonneg, sub_eq_zero, not_not, lt_min, min_le_left/right, Complex.ext. Tree names used: zerosIn_finite, Ncount_eq_sum, zeta_order_ge_one, reflect_mem_zerosIn, zeta_order_reflectZ, offLine_le_one_third, N0_le_Ncount, N0, NOffLine. Compile time about 12 s per run.

## merge report

MERGE: done; file /tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/cube/merged/Cube.lean (compile log beside it: .../cube/merged/compile.log)

Compile: `cd .../zeta23 && PATH=$HOME/.elan/bin:$PATH lake env lean .../merged/Cube.lean` → exit 0, no errors; the only warning is `Cube.lean:398:8: warning: declaration uses sorry` (the one declared sorry below). `#print axioms` for all 54 theorems/lemmas is at the end of the file; 52 print exactly [propext, Classical.choice, Quot.sound]. The DEFINITIONS block (CUBE_DEFS.lean lines 1-59) sits once, byte-identical (diff-checked) after the header; no definition body changed; nothing under the zeta23 tree was modified (find -mmin on the tree is empty). No node names anywhere (the three hits on "zones" are the English word in prose).

sorry-free, standard axioms only (52):
§1 The mirror and the zones: mirror_re, mirror_im, mirror_mirror, mirror_injective, aux_mirror_eq_reflect, is_nontrivial_zero_mirror, mirror_mem_zerosIn, zeta_order_mirror, is_nontrivial_zero_conj, mirror_eq_self_iff, one_le_zeta_order, inBand_or_inReservoir_or_onLine, inBand_mirror_iff, mem_bandZeros_mirror
§2 Degeneracy: degenerate_of_not_onLine, onLine_and_simple_of_not_degenerate, not_degenerate_of_onLine_simple, noDegenerate_iff
§3 The gap as ordinate injectivity: spectralGapHyp_iff_not_inBand, spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros, bandCoincidentMass_eq_zero_of_spectralGapHyp, not_inBand_of_bandCoincidentMass_eq_zero, spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero, bandCoincidentMass_nonneg, bandCoincidentMass_le_offDiagonalCoincidentMass
§4 The pair measure and its marginals: finsum_mem_inter_setOf_eq_sum_filter, NOffLine_real_eq_sum_filter, N0_real_eq_sum_filter, Ncount_eq_N0_add_NOffLine, pairSum_eq_sum, aux_pairSum_eq_finset_sum, pairSum_const, pairSum_fst, pairSum_snd, pairSum_fst_indicator, pairSum_fst_abs, pairSum_fst_abs_eq_integral, pairSum_swap, pairSum_nonneg, pairSum_mono, diagonalMass_nonneg, diagonalMass_le_sq_Ncount, Ncount_le_diagonalMass
§5 The atom at s = 0: coincidentMass_eq, offDiagonalCoincidentMass_nonneg, offLine_sq_le_offDiagonalCoincidentMass, offDiagonalCoincidentMass_le (the corrected form offDiag ≤ NOffLine·N + N0·NOffLine), offDiagonalCoincidentMass_le_two_mul, offDiagonalCoincidentMass_eq_zero_of_onLine, onLine_of_offDiagonalCoincidentMass_eq_zero, offDiagonalCoincidentMass_le_two_thirds, offDiagonalCoincidentMass_le_five_ninths

sorried (2, both print [propext, sorryAx, Classical.choice, Quot.sound], clearly marked in docstrings and header):
- theorem nontrivial_zero_im_ne_zero : ∀ ρ, is_nontrivial_zero ρ → ρ.im ≠ 0 — the file's only `sorry` (line 398): "no nontrivial zero is real", classical but absent from Mathlib at this pin and from the tree; no node proved it.
- theorem spectralGapHyp_iff_bandCoincidentMass (Δ) : SpectralGapHyp Δ ↔ ∀ T, bandCoincidentMass Δ T = 0 — the plan's unconditional gap item 5, defined as spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero nontrivial_zero_im_ne_zero Δ, so it inherits sorryAx only through that one fact.

Deliberately NOT included (no sorry placed): the plan's literal offDiagonalCoincidentMass T ≤ NOffLine·Ncount and the 1/3+ε constant (offDiagonalCoincidentMass_le_third). The upstream counterexample (an on-line zero of multiplicity 2 sharing its ordinate with an off-line mirror pair gives 10 > 8) shows the bare inequality is not bookkeeping and holds only under configurations RH would exclude; sorrying it would misrepresent its status. This is recorded in the header and in the docstring of offDiagonalCoincidentMass_le.

Merge decisions: duplicates dropped (the mirror lemmas and pairSum_eq_sum appeared in three files; one copy each kept, the first-node variant); both pairSum_eq_sum (hypothesis form) and aux_pairSum_eq_finset_sum (plan's literal form) kept; one_le_zeta_order kept as an alias of the tree's zeta_order_ge_one; the unused hΔ in inBand_or_inReservoir_or_onLine kept with the local linter silence (plan's shape); is_nontrivial_zero_conj placed in §1 with the mirror; the Finset-sum helpers and Ncount_eq_N0_add_NOffLine placed in §4 ahead of the pair measure. Header is in the DensityPartial style with a "[BOOKKEEPING] + one [SORRY]" register line, a "What is proved" list, and a "What this is and is not" paragraph stating that every statement is bookkeeping over finite sums of zeros, that the equivalences relocate the gap and RH and do not prove them, and that the cubic small-distance law is the GUE/Montgomery prediction, not a theorem.

Summary: The merged module proves, with standard axioms, every statement the four nodes delivered: the mirror ρ ↦ 1 − ρ̄ preserves zeros, windows, multiplicities and the band and fixes exactly the line; an off-line zero is degenerate via its mirror, so "no degenerate zero" is exactly "RH and all zeros simple"; the gap hypothesis is exactly "no zero in the punctured band", equivalently injectivity of the ordinate on the band zeros, and it forces the band's coincident mass to vanish while a vanishing band coincident mass excludes band zeros of positive ordinate; the pair measure has total mass N², one-coordinate marginals N·(one-zero sum) giving N·NOff and N·reservoirMass = N·∫₀^{1/2} NOff, swap symmetry, positivity, monotonicity, and the diagonal mass Σm² is between N and N²; the atom at s = 0 is Σm² plus the off-diagonal coincident mass, which dominates Σ_{off-line} m², is ≤ NOffLine·N + N0·NOffLine ≤ 2·NOffLine·N, vanishes iff all positive-ordinate zeros are on the line, and is eventually ≤ (5/9 + ε)N² by the tree's one-third bound. All of it is finite-sum bookkeeping; none of it proves the gap, RH, simplicity, or any pair-correlation law — the two-sided "gap ↔ vanishing band coincident mass" rests on one isolated sorry (ζ has no real zeros in (0,1)), and the plan's sharper NOffLine·N bound with its 1/3 constant was found not to be bookkeeping and is omitted rather than sorried.
