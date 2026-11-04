# Strip scoping reports (2026-11-04)

The scoping workflow's reports, verbatim: the inventory of the zeta23 tree and Mathlib for a zero-density estimate, the route memo, and the landscape memo. The plan they fed is `STRIP_PLAN.md`.



---

## Report 1

**Inventory: tree + Mathlib for a zero-density estimate** (pin: Lean `leanprover/lean4:v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`; tree `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23`, read-only; Mathlib paths below are relative to `.lake/packages/mathlib/`).

Every name quoted below was resolved by compiling a `#check`/`#print axioms` scratch file against the tree: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/strip/inventory/Inventory.lean` (output in `Inventory.out` beside it; `lake env lean` exit 0). Axiom lines from that run: `Zeta23.MV.mvDiag_thirteen`, `M1.dirichlet_meanSquare_le`, `Zeta23.BL.count_le_meanSquare'`, `Zeta23.BL.bohrLandau_full`, `BLClosure.meanSquareUnif_all`, `BLClosure.zeta_approx_sharp` all `[propext, Classical.choice, Quot.sound]`; `Zeta23.BL.bohrLandau` (the scoping theorem of `Zeta23/BohrLandau.lean:110`) depends on `sorryAx` (its two sorries: `meanSquare_strip` :98–100 and `rightHalfBound_of_meanSquare` :107–108; neither is in the Comparator list). The Comparator config for the density layer is `MNFChallengesD/Density.json` (challenge `MNFChallengesD.All`, solution `MNF.RH.DensityAll`, `definition_names: []`, NanoDa on); its `theorem_names` contain every M1/M2/M3a/M3/J0–J9/M45 declaration of `BohrLandauPartial.lean`, every `BLClosure.*` and `Zeta23.BL.rightHalf_all`/`rightHalfBound`/`bohrLandau_full`, `MNF.RH.reservoirDensityOne_unconditional`, `MNF.RH.onLineDensityOne_of_gap_only`, all of `DPMV.*`, `DPMV2.*` and the five `JensenDisc.lean` theorems (the main `comparator.json` at the root is the Alpöge–Furman layer: 17 names, `two_thirds_on_critical_line` etc.).

---

## (1) Zeta23.MV — MVDiag, mvDiag_thirteen, and what the integral form actually is

`Zeta23/MV.lean:52-56`
```lean
def MVDiag (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * ∑ r, ‖x r‖ ^ 2 / δ r
```
`Zeta23/Hypotheses.lean:107-111` (the bilinear form consumed by the paper):
```lean
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)
```
`Zeta23/MV/Final.lean:23-31`
```lean
theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig
/-- **`MVDiag 13`** — the weighted Hilbert inequality, literature (diagonal) form. -/
theorem mvDiag_thirteen : MVDiag 13 := mvDiag_of_eigenBound eigenBound_thirteen
/-- **H-MV:** `∃ C > 0, MVHilbert C` (the field `PaperInputs.MV`). -/
theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C :=
  mvHilbert_of_eigenBound (by norm_num) eigenBound_thirteen
```
`Zeta23/MV.lean:224` `theorem MVHilbert_of_diag {C : ℝ} (hC : 0 ≤ C) (h : MVDiag C) : MVHilbert (2 * C)`; `:235` `theorem exists_MVHilbert_of_diag (h : ∃ C : ℝ, 0 < C ∧ MVDiag C) : ∃ C : ℝ, 0 < C ∧ MVHilbert C`. Supporting structure, `Zeta23/MV/Spacing.lean:36-39`:
```lean
structure Adm (freq δ : ι → ℝ) : Prop where
  inj : Function.Injective freq
  pos : ∀ r, 0 < δ r
  le : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|
```
`Zeta23/MV/Duality.lean:34-39` `def EigenBound (C : ℝ) : Prop := ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ), Adm freq δ → ∀ (u : ι → ℂ), ∑ n, ‖u n‖ ^ 2 = 1 → ∀ (μ : ℝ), (∀ m, ∑ n ∈ Finset.univ.erase m, ((Real.sqrt (δ m) * Real.sqrt (δ n) / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m) → |μ| ≤ C`; `:158` `theorem mvDiag_of_eigenBound {C : ℝ} (hb : EigenBound C) : MVDiag C`. The 13 comes from `Zeta23/MV/Quadratic.lean:54-55` `theorem Uform_le (h : Adm freq δ) (t : ι → ℝ) (ht : ∀ r, 0 ≤ t r) : Uform freq δ t ≤ 73 * ∑ n, t n ^ 2` plus the spacing lemmas (`spacing_sq` ≤ 9/δ, `spacing_four` ≤ 27/δ³, `two_point`, `Spacing.lean:17-20`) and `Zeta23/MV/Eigen.lean` `eigen_bound`.

**Answer to "is it T Σ|a_n|² + 13 Σ n|a_n|²?": no.** `MVDiag` is the *bilinear-sum* inequality, not an integral. The integral mean value with arbitrary complex coefficients is `M1.dirichlet_meanSquare_le` (`Zeta23/BL/BohrLandauPartial.lean:172-174`):
```lean
theorem dirichlet_meanSquare_le (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * I)‖ ^ 2
      ≤ T * ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 + 26 * ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * ‖a n‖ ^ 2
```
i.e. `T Σ‖a_n‖² + 26 Σ (n+1)‖a_n‖²` (≤ `T Σ‖a_n‖² + 52 Σ n‖a_n‖²` for n ≥ 1): 26 = 2·13 because the real part of the two MV-shaped sums in `Z_eq` is bounded by ‖Sx‖+‖Sa‖, each ≤ 13·Σ(n+1)‖a_n‖²; the weight `n+1` (not `n`) is the admissible gap `δ_n = 1/(n+1)` from `M1.log_nat_gap`. Note: no hypothesis on `T` at all, and the integral is over `[0, T]`. Route: `:46-47`
```lean
theorem log_nat_gap {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    1 / ((n : ℝ) + 1) ≤ |Real.log n - Real.log m|
```
`:80-83` (the instantiation of `mvDiag_thirteen` at `ι := ↥(Icc 1 N)`, `freq := log`, `δ := 1/(n+1)`):
```lean
theorem mv_Icc (N : ℕ) (x : ℕ → ℂ) :
    ‖∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m = n then (0:ℂ) else x m * conj (x n) / ((Real.log m - Real.log n : ℝ) : ℂ))‖
      ≤ 13 * ∑ n ∈ Icc 1 N, ((n : ℝ) + 1) * ‖x n‖ ^ 2
```
`:126-133` `term_eq` (`a m * conj (a n) * DPMV.J T m n` = diagonal `T·a m conj(a m)` + `I·(MV term with x n := a n * n^{-iT})` − `I·(MV term with a)`), `:150-157` `Z_eq` (the double sum of `DPMV.integral_normSq_sum` rearranged into those three pieces).

## (2) The Jensen-disc chain in BohrLandauPartial.lean: ζ-specific vs generic

**Generic in an analytic f** (nothing about ζ):
- `Zeta23/BL/JensenDisc.lean:8-11`
```lean
theorem sum_divisor_mul_log_le (c : ℂ) (r R : ℝ) (f : ℂ → ℂ) (hr : 0 < r) (hrR : r < R)
    (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) :
    (∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c r)) u : ℝ) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
```
- `:63-68` `circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae (c : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.sphere c R)) (hint : CircleIntegrable (fun z => Real.log ‖f z‖) c R) (hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))), f (circleMap c R θ) ≠ 0) : circleAverage (fun z => Real.log ‖f z‖) c R ≤ (1/2) * Real.log (circleAverage (fun z => ‖f z‖ ^ 2) c R)`; `:110-116` the same with a redundant `hpos`; `:121-123` `AnalyticOnNhd.ae_circleMap_ne_zero (c : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))), f (circleMap c R θ) ≠ 0`; `:159-162` `AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq (c : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) : circleAverage (fun z => Real.log ‖f z‖) c R ≤ (1/2) * Real.log (circleAverage (fun z => ‖f z‖ ^ 2) c R)`. Underlying Mathlib: `Mathlib/Analysis/Complex/JensenFormula.lean:376-380` `theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|)) (h₂f : f c ≠ 0) : circleAverage (Real.log ‖f ·‖) c R = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖` (and `:308-312` the `MeromorphicOn` version).
- Geometry, generic (`BohrLandauPartial.lean`): `Rout/rin/hwin` `:1238-1240` (`Rout σ₁ := 2 - σ₁`, `rin σ₁ δ := (Rout σ₁ + (3/2 - δ))/2`, `hwin σ₁ δ := √(rin² − (3/2−δ)²)/2`), `mem_closedBall_iff_sq :1243`, `abs_re_im_sub_le_of_mem_closedBall :1249`, `bounds_of_mem_closedBall_two :1257`, `one_notMem_closedBall_two :1266`, `re_ge_of_mem_closedBall_Rout :1274`, `outer_disc_facts :1281`, `geom_facts :1290-1293`:
```lean
theorem geom_facts {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧
    ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ →
      ρ ∈ closedBall (2 + t * I) (rin σ₁ δ)
```
`one_notMem_closedBall_two_add :1342`, `one_notMem_sphere_two_add :1351`, `closedBall_Rout_subset :1530`, `circleMap_two_add :1592`, `circleMap_two_add_ne_one :1600`, `segment_mapsTo_ne_one :1669`, `log_le_half_log_one_add_sq :1435`, `concaveOn_half_log_one_add :1472`; the `NRight` bookkeeping J0 (`NRight_eq_zero_of_half_le :1093`, `MNF_zerosIn_union :1103`, `NRight_add :1117`, `NRight_sub_eq :1129`, `NRight_mono :1137`) is about `MNF.RH.zerosIn`/`zeta_order`, not about analytic properties of ζ.

**ζ-specific** (each uses one of: `Zeta23.RvM.analyticOnNhd_riemannZeta`, `Zeta23.RvM.zeta_lower_bound_two`, `Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re`, `Zeta23.analyticOrderAt_riemannZeta_ne_top`, `MNF.RH.analyticAt_riemannZeta`, Mathlib `riemannZeta_ne_zero_of_one_le_re`, or the definition `Lz` which hard-codes `riemannZeta`):
- `Zeta23/RvM/ZetaGrowth.lean:43-44` `theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) : AnalyticOnNhd ℂ riemannZeta S`; `:216` `theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖`; `:223` `theorem riemannZeta_ne_zero_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : riemannZeta s ≠ 0`; `:198-199` `norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖`; `:227-228` `norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6`. `Zeta23/Statement/Seam.lean:40-41` `lemma analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤`. `MNF/RH/Core.lean:80` `theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s`; `:52` `def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`; `:54` `def ZetaZeros : Set ℂ := {ρ | is_nontrivial_zero ρ}`; `:58` `noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat`.
- J2 `:1149` `zeta_order_eq_zero_of_ne_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (h : riemannZeta ρ ≠ 0) : zeta_order ρ = 0`; `:1156-1158` `divisor_riemannZeta_eq_int {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ closedBall c r) {ρ : ℂ} (hρ : ρ ∈ closedBall c r) : MeromorphicOn.divisor riemannZeta (closedBall c r) ρ = (zeta_order ρ : ℤ)`; `:1167-1169` the ℝ form `divisor_riemannZeta_eq`; `:1176-1179` `sum_zeta_order_le_finsum_divisor (h1 : (1:ℂ) ∉ closedBall c r) (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ closedBall c r) : ∑ ρ ∈ S, (zeta_order ρ : ℝ) ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)`; `:1200-1203` `finsum_divisor_riemannZeta_eq (h1 : (1 : ℂ) ∉ closedBall c r) (hre : ∀ s ∈ closedBall c r, 0 < s.re) : ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ) = ∑ᶠ ρ ∈ ZetaZeros ∩ closedBall c r, (zeta_order ρ : ℝ)`; `:1223-1227` `finsum_divisor_riemannZeta_eq_zerosIn`.
- J4 `:1358-1359` `neg_log_norm_riemannZeta_two_add_le (t : ℝ) : -Real.log ‖riemannZeta (2 + t * I)‖ ≤ Real.log 3`; `:1367-1371`
```lean
theorem count_disc_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3) :
    (∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall (2 + t * I) r) u : ℝ))
        * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
          - Real.log ‖riemannZeta (2 + t * I)‖
```
(proof: `sum_divisor_mul_log_le (2 + t * I) r R riemannZeta hr hrR (Zeta23.RvM.analyticOnNhd_riemannZeta (one_notMem_closedBall_two_add ht hR)) (Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re (by simp))`); `:1377-1380` `finset_sum_zeta_order_le_finsum_divisor (h1 : (1 : ℂ) ∉ closedBall c r) (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall c r) : (∑ ρ ∈ S, (zeta_order ρ : ℝ)) ≤ ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c r) u : ℝ)`; `:1406-1409`
```lean
theorem count_finset_le {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R + Real.log 3
```
- J5 `:1426` `noncomputable def Lz (z : ℂ) : ℝ := (1 / 2) * Real.log (1 + ‖riemannZeta z‖ ^ 2)`; `Lz_nonneg :1428`, `log_norm_le_Lz :1447`, `:1450` `continuousOn_Lz {U : Set ℂ} (hU : (1 : ℂ) ∉ U) : ContinuousOn Lz U`, `circleIntegrable_Lz :1459`, `:1464-1465` `circleAverage_log_norm_le_Lz {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h1 : (1 : ℂ) ∉ sphere c R) : circleAverage (fun z => Real.log ‖riemannZeta z‖) c R ≤ circleAverage Lz c R`; `:1484-1486`
```lean
theorem circleAverage_Lz_le {c : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ sphere c R) :
    circleAverage Lz c R
      ≤ (1 / 2) * Real.log (1 + circleAverage (fun z => ‖riemannZeta z‖ ^ 2) c R)
```
`:1517-1522` `count_finset_le_log_meanSq` (count·log(R/r) ≤ (1/2) log(1 + circleAverage ‖ζ‖² (2+tI) R) + log 3); `:1543-1548`
```lean
theorem count_window_le {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) (Rout σ₁)
          + Real.log 3
```
`count_window_le_log_meanSq :1556-1561`, `circleAverage_log_le_Lz :1568-1570`.
- J7 `continuousOn_Lz_circleMap :1605`, `integrableOn_Lz_circleMap_prod :1616`, `integrable_Lz_circleMap_prod_restrict :1626`, `intervalIntegrable_circleAverage_Lz :1634`, `:1649-1652` `integral_circleAverage_Lz_eq_swap {R T : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (hT : 0 ≤ T) : ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) R = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) R θ)`; `:1663` `Lz_le_half_sq (z : ℂ) : Lz z ≤ (1 / 2) * ‖riemannZeta z‖ ^ 2`; `intervalIntegrable_Lz_segment :1676`, `intervalIntegrable_normSq_zeta_segment :1682`; `:1692-1695`
```lean
theorem integral_Lz_circle_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ} (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) (θ : ℝ) :
    ∫ t in (3:ℝ)..(T + 3), Lz (circleMap (2 + t * I) (Rout σ₁) θ) ≤ (1 / 2) * (C * (T + 5))
```
`:1733-1737`
```lean
theorem integral_circleAverage_Lz_le {σ₁ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ}
    (hT : 0 ≤ T)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T) :
    ∫ t in (3:ℝ)..(T + 3), circleAverage Lz (2 + t * I) (Rout σ₁) ≤ (1 / 2) * (C * (T + 5))
```
- J6 `:1767-1770`
```lean
theorem count_le_integral {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3)
```
(ζ enters only through `count_window_le` and `Lz`; the step-function/indicator integration is generic.)
- J6+J7 `:1843-1849`
```lean
theorem count_le_meanSquare {σ₁ δ C : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hδσ : σ₁ - 1 / 2 < δ)
    (hδ : δ ≤ 1 / 2)
    (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 + Rout σ₁ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ (1 / 2) * (C * (T + 5)) + T * Real.log 3
```
`:1862-1868` `count_le_meanSquare'` identical except `(hMS : ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T)` (no upper bound on σ). `:1874` `tsum_one_div_rpow_anti`, `:1885-1886` `meanSquare_of_gt_one {σ₂ σ : ℝ} (h2 : 1 < σ₂) (hσ : σ₂ ≤ σ) {T : ℝ} (hT : 1 ≤ T) : ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ σ₂) ^ 2 * T` (uses `norm_zeta_le_tsum`, `Zeta23/BohrLandau.lean:69`), `:1900-1905` `meanSquare_hyp_extend`. J8 `:1933-1935` `rightHalf_of_meanSquareUnif {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hms : M3.MeanSquareUnifFrom σ₁) : ∀ δ : ℝ, σ₁ - 1 / 2 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T`, with `M3.MeanSquareUnifFrom` (`:1060-1061`) `def MeanSquareUnifFrom (σ₁ : ℝ) : Prop := ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T`.

**What has to change for f = ζ·M, M a Dirichlet polynomial with ‖f(2+it)‖ ≥ 1/2:**
(a) `count_disc_le`: replace `riemannZeta` by `fun z => riemannZeta z * M z`, analyticity by `(Zeta23.RvM.analyticOnNhd_riemannZeta h).mul hM` (M entire; the tree has only `Zeta23.BL.M3.continuous_Dpoly :801`, no `AnalyticOnNhd` lemma for `Dpoly`/`BLClosure.S` yet), and `riemannZeta_ne_zero_of_two_le_re` by `f (2+tI) ≠ 0` from the hypothesis. (b) `neg_log_norm_riemannZeta_two_add_le`: `log 3` becomes `log 2` from `‖f(2+it)‖ ≥ 1/2`. (c) The equality `divisor_riemannZeta_eq` must become an inequality `zeta_order ρ ≤ divisor f ρ`: Mathlib `Mathlib/Analysis/Meromorphic/Divisor.lean:310-313` `theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z ∈ U, meromorphicOrderAt f₁ z ≠ ⊤) (h₂f₂ : ∀ z ∈ U, meromorphicOrderAt f₂ z ≠ ⊤) : divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U` (`:319-323` `divisor_fun_mul` for `fun z ↦ f₁ z * f₂ z`), `:177` `AnalyticOnNhd.divisor_nonneg`, `:71` `AnalyticOnNhd.divisor_apply : AnalyticOnNhd 𝕜 f U → z ∈ U → (MeromorphicOn.divisor f U) z = (ENat.map Nat.cast (analyticOrderAt f z)).untop₀`, and `Mathlib/Analysis/Analytic/Order.lean:497-499` `theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀`. `finset_sum_zeta_order_le_finsum_divisor` and `count_finset_le` only need the ≤, so J4 survives. (d) `Lz` hard-codes `riemannZeta`; a majorant `(1/2) log(1 + ‖ζ z * M z‖²)` needs `continuousOn_Lz`, `circleIntegrable_Lz`, `circleAverage_log_norm_le_Lz`, `circleAverage_Lz_le`, `continuousOn_Lz_circleMap`, the two integrability lemmas, `integral_circleAverage_Lz_eq_swap`, `Lz_le_half_sq`, `intervalIntegrable_Lz_segment`/`normSq_zeta_segment` redone with `ζ·M` (all proofs are "continuity on {z ≠ 1}" plus generic concavity; `concaveOn_half_log_one_add` and `log_le_half_log_one_add_sq` are already generic). (e) `hMS` becomes the mollified mean square `∫₁ᵀ ‖ζ(σ+it) M(σ+it)‖² ≤ C T` on `σ₁ ≤ σ ≤ 2 + Rout σ₁`; the trivial extension to σ > 1 (`meanSquare_hyp_extend`) would need a bound `‖M(σ+it)‖ ≤ Σ|a_n| n^{-σ}` too. (f) J0/J6 bookkeeping and the geometry are unchanged. (g) One structural fact relevant to a *density* (as opposed to O(T)) estimate: J5 keeps the logarithm on each circle (`circleAverage_Lz_le` gives `(1/2) log(1 + circleAverage ‖ζ‖²)`), but J7 then discards it at `:1718-1723` via `Lz_le_half_sq` (`Lz ≤ (1/2)‖ζ‖²`) before integrating in t; that is the exact step where a mollified/Littlewood-style argument (the `1 − (1 − ζM)²` remark at `Zeta23/BohrLandau.lean:105-106`) would have to keep `log` and use concavity of `log` over the t-integral instead.

## (3) Mathlib: Möbius, convolution, divisors, divisor-count bounds, harmonic

Möbius (`Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`): `:51-52` `def moebius : ArithmeticFunction ℤ := ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩` (notation `μ`, scoped `ArithmeticFunction.Moebius`); `:60` `moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n`; `:64` `moebius_eq_zero_of_not_squarefree`; `:69` `moebius_ne_zero_iff_squarefree`; `:75` `moebius_eq_or (n : ℕ) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1`; `:93` `moebius_sq`; `:99` `abs_moebius`; `:105` `abs_moebius_le_one {n : ℕ} : |μ n| ≤ 1`; `:109` `moebius_apply_prime`; `:112` `moebius_apply_prime_pow`; `:128` `isMultiplicative_moebius : IsMultiplicative μ`; `:144-146` `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R] (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) : ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d`.
**The identity Σ_{d ∣ n} μ(d) = [n = 1]**: there is no pointwise-named lemma; it is the arithmetic-function identity `:158` `theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1`, `:172` `coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1`, `:176` `coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1`, `:180` `coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1`, combined with `Zeta.lean:84-86` `coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} : (ζ * f) x = ∑ i ∈ divisors x, f i` and `Defs.lean:101` `one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0`. Verified in the scratch file: `example (n : ℕ) : (∑ d ∈ n.divisors, μ d) = if n = 1 then 1 else 0 := by rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply]` compiles.
Möbius inversion: `:208-210` `sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} : (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔ ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd = f n`; `:238-240` `sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : ℕ → R} : (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔ ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n`; `:247-249` `prod_eq_iff_prod_pow_moebius_eq`; `:253` `_of_nonzero`; `_on` variants on divisor-closed sets `:277, :302, :314-318, :327, :335`.
Convolution/multiplicativity (`Defs.lean`): `:235-237` `mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} : (f * g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst * g x.snd`; `:223-225` `smul_apply`; `:242` `natCoe_mul`; `:131` `natCoe_apply`, `:150` `intCoe_apply`; `:421-422` `def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop := f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n`; `:488-489` `IsMultiplicative.mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMultiplicative (f * g)`. `Zeta.lean`: `:38-39` `def zeta : ArithmeticFunction ℕ := ⟨fun x => ite (x = 0) 0 1, rfl⟩`; `:49` `zeta_apply`; `:79` `coe_zeta_mul_comm`; `:84` `coe_zeta_mul_apply`; `:89-90` `coe_mul_zeta_apply [Semiring R] {f : ArithmeticFunction R} {x : ℕ} : (f * ζ) x = ∑ i ∈ divisors x, f i`; `:93` `zeta_mul_apply`, `:96` `mul_zeta_apply` (ℕ-valued); `:107` `pmul`; `:194` `isMultiplicative_zeta`. `Misc.lean`: `:143-144` `def sigma (k : ℕ) : ArithmeticFunction ℕ := ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩`; `:151` `sigma_apply`; `:178` `sigma_zero_apply (n : ℕ) : σ 0 n = #n.divisors`; `:180` `sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1`; `:195` `zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k`; `:202` `isMultiplicative_sigma`; `:258` `cardFactors` (Ω), `:323` `cardDistinctFactors` (ω); `:222-223` `theorem _root_.Nat.card_divisors {n : ℕ} (hn : n ≠ 0) : #n.divisors = n.primeFactors.prod (n.factorization · + 1)`; `:443-444` (namespace `Nat.Coprime`) `card_divisors_mul {m n : ℕ} (hmn : m.Coprime n) : #(m * n).divisors = #m.divisors * #n.divisors`. LSeries/Dirichlet: `Dirichlet.lean:293` `LSeries_zeta_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1`; `:280` `LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s`; `:71` `LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re`; `:79` `abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1`; `Convolution.lean:64-65` `LSeries.convolution` (`⍟`), `:84-85` `convolution_def (f g : ℕ → R) : f ⍟ g = fun n ↦ ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2`, `:151-154` `LSeries_convolution' (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) s = LSeries f s * LSeries g s`, `:192-195` `LSeries_mul'`, `:199-202` `LSeries_mul`. Also `VonMangoldt.lean:102` `vonMangoldt_sum {n : ℕ} : ∑ i ∈ n.divisors, Λ i = Real.log n`, `:133` `sum_moebius_mul_log_eq {n : ℕ} : (∑ d ∈ n.divisors, (μ d : ℝ) * log d) = -Λ n`.
`Nat.divisors` (`Mathlib/NumberTheory/Divisors.lean`): `:52` `def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n}`; `:64` `divisorsAntidiagonal`; `:108` `mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0`; `:124-125` `mem_divisorsAntidiagonal {x : ℕ × ℕ} : x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0`; `:210` `divisor_le`; `:220` `theorem card_divisors_le_self (n : ℕ) : #n.divisors ≤ n`; `:387` `sum_divisors_eq_sum_properDivisors_add_self`; `:412` `Prime.divisors`; `:420` `divisors_prime_pow`; `:522-524` (`@[to_additive]`, giving `Nat.sum_divisorsAntidiagonal`) `prod_divisorsAntidiagonal (f : ℕ → ℕ → M) {n : ℕ} : ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f i (n / i)`; `:528-530` the `'` version `= ∏ i ∈ n.divisors, f (n / i) i`. `Mathlib/Data/Finset/NatDivisors.lean:33-49`: `Nat.divisorsHom : ℕ →* Finset ℕ` (`divisors_mul`, `Finset.nat_divisors_prod : (∏ i ∈ s, f i).divisors = ∏ i ∈ s, (f i).divisors`).
**Divisor-counting growth bounds: none in Mathlib at this pin.** Exhaustive greps (`card_divisors`, `sigma_zero`, `σ 0`, `#…divisors`, `divisors` × `rpow|Real.log|IsBigO|isLittleO|sqrt`, "hyperbola") found only: `Nat.card_divisors_le_self` (d(n) ≤ n), the formula `Nat.card_divisors`, `Nat.Coprime.card_divisors_mul`, `sigma_zero_apply_prime_pow`, and `Nat.card_divisors_le_self` used once in `TsumDivisorsAntidiagonal.lean:98`. No `d(n) ≤ C n^ε`, no `Σ_{n≤x} d(n) ≤ x log x`, no `Σ d(n)² ≤ x log³ x`, no `d(n) ≤ 2√n`. The tools for proving `Σ_{n≤x} d(n) ≤ x(1 + log x)` from scratch are present (`Nat.sum_divisorsAntidiagonal`, `Finset.sum_comm`, harmonic bound) and partial summation is `Mathlib/NumberTheory/AbelSummation.lean:129-133` `sum_mul_eq_sub_sub_integral_mul (ha : 0 ≤ a) (hab : a ≤ b) (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k = f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) - …` (plus `:189, :211, :239` variants). Cauchy–Schwarz: `Finset.sum_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2`.
Harmonic (`Mathlib/NumberTheory/Harmonic/`): `Defs.lean:23` `def harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹`; `Bounds.lean:20` `harmonic_eq_sum_Icc {n : ℕ} : harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹`; `:24-25` `log_add_one_le_harmonic (n : ℕ) : Real.log ↑(n + 1) ≤ harmonic n`; `:33-34` `theorem harmonic_le_one_add_log (n : ℕ) : harmonic n ≤ 1 + Real.log n`; `:59-60` `log_le_harmonic_floor (y : ℝ) (hy : 0 ≤ y) : Real.log y ≤ harmonic ⌊y⌋₊`; `:71-72` `harmonic_floor_le_one_add_log (y : ℝ) (hy : 1 ≤ y) : harmonic ⌊y⌋₊ ≤ 1 + Real.log y`. Already wrapped in the tree: `BohrLandauPartial.lean:226` `theorem sum_inv_le (N : ℕ) : ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ ≤ 1 + Real.log N` (namespace `M1`). Prime-side sums already in the tree: `Zeta23/Chebyshev.lean:50-52` `sum_vonMangoldt_le {x : ℝ} (hx : 0 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x` (via Mathlib `Chebyshev.psi_le_const_mul_self`), `:474-475` `sum_vonMangoldt_sq_le`, `:509-511` `mertensFirst {x : ℝ} (hx : 1 ≤ x) : |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ Real.log 4 + 4`; `Zeta23/FromPNTPlus/Mertens.lean:79-80` `sum_log_le`, `:195-196` `sum_mangoldt_div_eq_log`. No `moebius`/`ArithmeticFunction.moebius` use anywhere under `Zeta23/` or `MNF/` (the only hit is the prose remark `Zeta23/BohrLandau.lean:106`).

## (4) M1's mean-value lemmas for a_n = n^{−σ}, exact shapes

`Zeta23/BL/BohrLandauPartial.lean` (namespace `M1`; all Comparator-listed): `:210-211` `cpow_neg_add_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) : (n:ℂ) ^ (-((σ:ℂ) + t * I)) = (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I)`; `:219-220` `norm_sq_rpow (n : ℕ) (σ : ℝ) : ‖(((n:ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2 = (n:ℝ) ^ (-2 * σ)`; `:233-235` `sum_weight_le (σ : ℝ) (hσ1 : σ ≤ 1) (N : ℕ) : ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ) ≤ 2 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1)`; `:262-265`
```lean
theorem meanValue_pow_raw (σ : ℝ) (N : ℕ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ)
        + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)
```
`:279-282` `meanValue_pow (σ : ℝ) (_hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) (T : ℝ) (_hT : 0 < T) : ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ) ^ (-((σ:ℂ) + t * Complex.I))‖ ^ 2 ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) + 52 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1)`; `:291-292` `sum_Icc_rpow_le_integral {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : a ≤ 0) (ha' : a ≠ -1) : ∑ n ∈ Icc 1 N, (n:ℝ) ^ a ≤ 1 + ((N:ℝ) ^ (a + 1) - 1) / (a + 1)`; `:314-315` `sum_rpow_neg_le (σ : ℝ) (hσ : 1/2 < σ) (N : ℕ) : ∑ n ∈ Icc 1 N, (n:ℝ) ^ (-2 * σ) ≤ 1 + 1 / (2 * σ - 1)`; `:329-330` `sum_Icc_rpow_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) : ∑ n ∈ Icc 1 N, (n:ℝ) ^ a ≤ 1 + (N:ℝ) ^ (a + 1) / (a + 1)`; `:343-345` `sum_weight_le_logfree (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (N : ℕ) : ∑ n ∈ Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ) ≤ 2 * (1 + (N:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))`; `:365-368` `meanValue_pow_logfree (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (N : ℕ) (T : ℝ) : ∫ … ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) + 52 * (1 + (N:ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ))`; `:375-378` `meanValue_pow_explicit (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) : ∫ … ≤ T * (1 + 1 / (2 * σ - 1)) + 52 * (N:ℝ) ^ (2 - 2 * σ) * (Real.log N + 1)`. M3: `:798-799` `noncomputable def Dpoly (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (((n:ℝ) ^ (-σ) : ℝ) : ℂ) * (n:ℂ) ^ (-(t:ℂ) * I)`; `:810-813` `meanValue_Dpoly (σ : ℝ) (N : ℕ) (T : ℝ) : ∫ t in (0:ℝ)..T, ‖Dpoly σ N t‖ ^ 2 ≤ T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)`; `:885-891` `integral_bound_abstract {σ : ℝ} {N : ℕ} {T : ℝ} (hT : 1 ≤ T) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hpt : ∀ t ∈ Icc (1:ℝ) T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤ 4 * ‖Dpoly σ N t‖ ^ 2 + 4 * A * (t ^ 2)⁻¹ + K) : ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ:ℂ) + t * I)‖ ^ 2 ≤ 4 * (T * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ^ (-2 * σ) + 26 * ∑ n ∈ Finset.Icc 1 N, ((n:ℝ) + 1) * (n:ℝ) ^ (-2 * σ)) + 4 * A + K * T`; M3a `:739-741` `sum_Icc_rpow_mul_log_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) (hN : 1 ≤ N) : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a * (Real.log n + 1) ≤ (1 + 1 / (a + 1)) * (N : ℝ) ^ (a + 1) * (Real.log N + 1)`, `:720-721` `sum_Icc_rpow_le_tsum {a : ℝ} (ha : a < -1) (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a ≤ ∑' n : ℕ, (n : ℝ) ^ a`.
The trivial (2/|log(n/m)|) forms: `Zeta23/BL/DPMV.lean:117-121`
```lean
theorem dirichlet_mean_value (a : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n:ℂ) ^ (-(t:ℂ) * Complex.I)‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (n / m)|))
```
and `Zeta23/BL/DPMVexp.lean:131-136` `DPMV2.dirichlet_mean_value` (same with `Complex.exp (-(t:ℂ) * I * Real.log n)` and `2 / |Real.log n - Real.log m|`; separate module `Zeta23.BL.DPMVexp`, not imported by `BohrLandauClosure`). **So: yes, the general-coefficient Montgomery–Vaughan-type bound is already proved and receipted — `M1.dirichlet_meanSquare_le` — with error `26 Σ (n+1)‖a_n‖²`, not `13 Σ n‖a_n‖²`.**

## Other receipted inputs you will use (verbatim statements)

`Zeta23/BL/BohrLandauClosure.lean:72` `noncomputable def S (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)`; `:434-442`
```lean
theorem first_derivative_test_amp_smooth {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc a b, HasDerivAt F' (F'' x) x)
    (hconv : ∀ x ∈ Set.Icc a b, 0 ≤ F'' x) (hlow : ∀ x ∈ Set.Icc a b, lam ≤ F' x)
    (hcont : ContinuousOn F'' (Set.Icc a b))
    (G G' : ℝ → ℝ) (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Set.Icc a b, G' x ≤ 0) (hG0 : ∀ x ∈ Set.Icc a b, 0 ≤ G x)
    (hGc : ContinuousOn G' (Set.Icc a b)) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (Complex.I * (F x : ℂ))‖ ≤ 4 * G a / lam
```
(`:302-311` the primed version with only `G' x * F' x - G x * F'' x ≤ 0`); `:912-914` `zeta_eq_euler_maclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) : riemannZeta s = S N s + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2 - s * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1)` (`psi u := Int.fract u - 1/2`, `:63`); `:811-814` `tail_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) : ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N → ‖((σ : ℂ) + t * I) * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)‖ ≤ C * (N : ℝ) ^ (-σ)`; `:954-959`
```lean
theorem zeta_approx_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C * (N : ℝ) ^ (-σ)
```
`:990-994` `zeta_approx_sharp_segment {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) : ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∀ t ∈ Icc (1 : ℝ) T, ‖riemannZeta ((σ : ℂ) + t * I) - S ⌈T⌉₊ ((σ : ℂ) + t * I) - (⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖ ≤ C * (⌈T⌉₊ : ℝ) ^ (-σ)`; `:1041-1042` `S_eq_Dpoly (σ : ℝ) (N : ℕ) (t : ℝ) : S N ((σ : ℂ) + t * I) = Zeta23.BL.M3.Dpoly σ N t`; `:1058-1064` `norm_zeta_sq_le_sharp {σ₁ σ t C : ℝ} (hσ : σ₁ ≤ σ) (ht : 1 ≤ t) {N : ℕ} (hN : 1 ≤ N) (hE : ‖riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I) - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖ ≤ C) : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ 4 * ‖Zeta23.BL.M3.Dpoly σ N t‖ ^ 2 + 4 * (N : ℝ) ^ (2 - 2 * σ₁) * (t ^ 2)⁻¹ + 4 * C ^ 2`; `:1090-1092` `meanSquare_sharp_param {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) : ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T` (explicit `C = 4(1 + 1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4 C_G²`); `:1165-1167` `meanSquareUnif_all {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) : ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T`; `:1212` `Zeta23.BL.rightHalf_all : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T`; `:1226` `theorem bohrLandau_full : MNF.RH.BohrLandau := bohrLandau_of_right rightHalfBound`; `:1281-1283` `MNF.RH.onLineDensityOne_of_gap_only {Δ : ℝ} (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) : OnLineDensityOne`.
`Zeta23/FromPNTPlus/ZetaBounds.lean:520-523` `noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ := (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) + (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2 + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)`; `:1150-1151` `lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) : ζ₀ N s = riemannZeta s`; `:815-817` `ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) : ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖ ≤ N ^ (-σ) / σ`; `:1402-1404` `ZetaUpperBnd : ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t|`; `:1799-1802` `ZetaDerivUpperBnd` (same hypotheses, `‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2`); `:1936-1937` `ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1`. `Zeta23/RvM/ZetaGrowth.lean:56-57` `norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re`; `:78-79` `riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re) (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im|`; `:102-103` `zeta_growth`; `:109-111` `zeta_growth_quarter`; `:143-145` `zeta_growth_right : ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ → ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A`. `Zeta23/RvM/LocalCount.lean:266-267` `zeta_local_zero_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)`, `:96-97` `half_count_large : ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3)`; `Zeta23/RvM/Statement.lean:20` `riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig`.
MNF target definitions: `MNF/RH/Counting.lean:52` `def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}`, `:57` `Ncount`, `:96` `zerosIn_finite`; `MNF/RH/GapDensity.lean:64` `N0`, `:68` `noncomputable def NOff (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}, zeta_order ρ`, `:73` `def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T`, `:80` `NcountSuperlinear`; `MNF/RH/Density.lean:76` `NRight` (= `Zeta23/BohrLandau.lean:16`), `:207-208` `ReservoirDensityOne`, `:211-212` `OnLineDensityOne`; `MNF/RH/Hypotheses.lean:47` `def SpectralGapHyp (Δ : ℝ) : Prop := SpectralGapProperty ShiftedZeroSpectrum Δ`, `:85-86` `theorem spectralGapHyp_iff_zeroFree_strip {Δ : ℝ} : SpectralGapHyp Δ ↔ ∀ s : ℂ, 1/2 < s.re → s.re < 1/2 + Δ → riemannZeta s ≠ 0`; `MNF/RH/Gap.lean:66` `def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0`.

Comparator note (from the receipts record): rc2 compares, in full, any theorem referenced as a term inside a listed statement, so a new challenge must pass finiteness etc. as hypotheses, not cite theorems in statements; with `definition_names: []` definition bodies are compared, so the challenge must mirror the solution module by module.


---

## Report 2

**Zero-density with a power saving on the zeta23/MNF tree — proof route (disc-average method, mollified)**

Sources read (receipted copies on the drive, byte-identical to the dev tree `~/mnf-stageB/z23work2/formal-math/zeta23`): `/run/media/joeyxyxyz/Seagate Portable Drive/math/qrh-zeta23-addon-v4/Zeta23/BL/{BohrLandauClosure,BohrLandauPartial,DPMV,DPMVexp,JensenDisc}.lean`, `.../Zeta23/BohrLandau.lean`, `.../MNF/RH/{Counting,GapDensity,Density}.lean`; on the dev tree `Zeta23/MV.lean` (`MVDiag`), `Zeta23/MV/Final.lean`, `Zeta23/RvM/{ZetaGrowth,LocalCount}.lean`, `Zeta23/FromPNTPlus/ZetaBounds.lean`; the pinned Mathlib under `.../zeta23/.lake/packages/mathlib`. Receipt status per `math/notes/density-field-2026-11-03/DENSITY_LEDGER.md`: everything in `Zeta23/BL/*` is covered by the cold v4 run (label `zeta23-density-v4`, 2026-11-04 00:52–00:58Z, 334 theorems, both kernels).

## 0. Verdict in one paragraph

Carlson's exponent θ(σ) = 4σ(1−σ) = 1 − (2σ−1)² is reachable with exactly the receipted tools, provided the sharp approximate formula is used **with N ≈ t on dyadic windows (U, 2U]** (N := ⌈2U+3⌉), not with one N ≈ T on [1, T]. With a single N = ⌈T⌉ on [1, T] (the shape of the receipted `zeta_approx_sharp_segment`) the term N^{1−s}/(s−1)·M_X is large for small t and the Cauchy–Schwarz cross term costs a square root: one gets the weaker but still power-saving θ_A(σ) = 1 − (2σ−1)²/(2σ). The disc-average method loses only (log T)^{1/2} and absolute constants against Littlewood's lemma, never an exponent, because the geometric factor 2h·log(R/r) is ≥ (2/3)(σ−σ₁)^{3/2} while Littlewood's weight is (σ−σ₁). The one thing that must change relative to the receipted Bohr–Landau proof is the majorant: the tree's `Lz = ½log(1+‖ζ‖²)` gives ½log(2+E), which is O(1) and kills every saving; it must be replaced by L_ε = ½log(ε²+‖f‖²) with ε² = 1/X, and the centre term log 3 by π²/(3X). The only genuinely new mathematics is one elementary estimate, Σ_{m≤Y} d_X(m)² ≤ Y(1+log X)³ (no divisor-function asymptotics needed). Nothing here touches a zero-free strip: the result is a quantitative Bohr–Landau, N(1/2+δ, T) ≪ T^{1−4δ²+ε}, strictly weaker than the gap hypothesis and not known to imply anything about it.

## 1. Notation, and what the tree gives (exact shapes)

- σ fixed, 1/2 < σ < 1; σ₁ with 1/2 < σ₁ < σ; Δ := σ − σ₁ ≤ 1/2. X ∈ ℕ, X ≥ 4. M_X(s) := Σ_{n ∈ Icc 1 X} μ(n) n^{−s} (Mathlib `ArithmeticFunction.moebius`). f := ζ·M_X, analytic on ℂ∖{1} (`Zeta23.RvM.analyticOnNhd_riemannZeta` + `AnalyticOnNhd.mul`).
- Target count, in the tree's vocabulary (multiplicity = `zeta_order` = `(analyticOrderAt riemannZeta ρ).toNat`, nontrivial = 0 < Re ρ < 1): `NSigma σ T₁ T₂ := ∑ᶠ ρ ∈ MNF.RH.zerosIn T₁ T₂ ∩ {ρ | σ ≤ ρ.re}, zeta_order ρ`. Note `Zeta23.BL.NRight δ T` is `NSigma (1/2+δ) 0 T` up to `linarith` in the set-builder (`δ ≤ ρ.re − 1/2`); Bohr–Landau (`bohrLandau_full`) is the exponent-1 case.
- Approximate formula (`BLClosure.zeta_approx_sharp`, receipted): ∃ C_G, ∀ σ₀ ≤ σ' ≤ 2, 0 ≤ t ≤ N, N ≥ 1, s = σ'+it ≠ 1: ‖ζ(s) − S_N(s) − N^{1−s}/(s−1)‖ ≤ C_G·N^{−σ'}, S_N(s) = Σ_{n∈Icc 1 N} n^{−s}. The witness in the proof of `tail_sharp` is C₀ = 48ζ(3)/π³ + 1/4 and `zeta_approx_sharp` returns C_G = C₀ + 1/2 ≈ 2.6; this value does not mention σ₀ (the docstring says C(σ₀); I read the witness, so treat "absolute" as read-off, not re-derived).
- Main-term bound (`Zeta23.BL.M2.norm_P_le`): ‖N^{1−s}/(s−1)‖ ≤ N^{1−σ₁}/t for σ' ≥ σ₁, t > 0, N ≥ 1.
- Dirichlet-polynomial mean value, general coefficients (`M1.dirichlet_meanSquare_le a N T`): ∫₀ᵀ ‖Σ_{n∈Icc 1 N} a_n n^{−it}‖² ≤ T·Σ‖a_n‖² + 26·Σ (n+1)‖a_n‖², any a : ℕ → ℂ, any real T. It is proved from `Zeta23.MV.mvDiag_thirteen : MVDiag 13`, whose exact statement is: for a finite index type, injective frequencies λ_r, gaps δ_r > 0 with δ_r ≤ |λ_r − λ_s| (r ≠ s), ‖Σ_{r≠s} x_r x̄_s/(λ_r−λ_s)‖ ≤ 13·Σ_r ‖x_r‖²/δ_r; specialised in `M1.mv_Icc` to λ_n = log n, δ_n = 1/(n+1). The two DPMV files give the same with the un-summed off-diagonal 2/|log(n/m)| (no MV).
- Jensen on discs, general f (`sum_divisor_mul_log_le c r R f hr hrR h₁f h₂f`, JensenDisc.lean): (Σᶠ_u divisor f (closedBall c r) u)·log(R/r) ≤ circleAverage(log‖f‖) c R − log‖f c‖, for f analytic on a neighbourhood of closedBall c R, f c ≠ 0. Concavity on circles (`AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq`), and the a.e. nonvanishing on circles (`AnalyticOnNhd.ae_circleMap_ne_zero`).
- For ζ, receipted: centre lower bound ‖ζ(2+it)‖ ≥ 1/3 (`zeta_lower_bound_two`), upper bound ‖ζ(s)‖ ≤ π²/6 on Re s ≥ 2 (`norm_riemannZeta_le_of_two_le_re`), pole avoidance (`one_notMem_closedBall_two_add`: t ≥ 3, R < 3), geometry (`geom_facts`: Rout = 2−σ₁, rin = (Rout + (3/2−δ))/2, hwin), per-t count (`count_finset_le`, `count_window_le_log_meanSq`), Fubini swap (`integral_circleAverage_Lz_eq_swap`), window bookkeeping (`count_le_integral`: 2·hwin·log(Rout/rin)·(NRight δ T − NRight δ 4) ≤ ∫₃^{T+3}(circleAverage Lz (2+it) Rout + log 3)dt), assembly `rightHalf_of_meanSquareUnif`, and the ζ mean square `meanSquareUnif_all`: ∫₁ᵀ‖ζ(σ'+it)‖² ≤ C(σ₁)T, C = 4(1+1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4C_G² for σ₁ < 1 (`meanSquare_sharp_param`).
- Partial sums (`M1.sum_Icc_rpow_le`: Σ_{n≤N} n^a ≤ 1 + N^{a+1}/(a+1) for −1 < a ≤ 0; `M1.sum_inv_le`: Σ_{n≤N} 1/n ≤ 1 + log N).
- Mathlib at the pin: `ArithmeticFunction.moebius_mul_coe_zeta : μ * ζ = 1` (so Σ_{d|m} μ(d) = [m=1] via `mul_apply`/`one_apply`), `abs_moebius_le_one`, `sigma_zero_apply`, `Nat.card_divisors_le_self`, `Nat.Ioc_filter_dvd_card_eq_div` (#{x ∈ Ioc 0 n | p ∣ x} = n/p), `LSeries_zeta_mul_Lseries_moebius` (L ζ s · L μ s = 1, Re s > 1), `LSeries_zeta_eq_riemannZeta`, `LSeriesSummable_moebius_iff`, `analyticOrderAt_mul`, `MeromorphicOn.divisor_mul` (orders ≠ ⊤ required), `AnalyticOnNhd.divisor_nonneg`, `MeromorphicOn.circleIntegrable_log_norm_of_nonneg`, `ConcaveOn.le_map_average`, `ConvexOn.map_average_le`, `intervalIntegral.integral_comp_add_right`, `Complex.cpow_add`, `Finset.sum_Ioc_by_parts`.

## (a) The centre bound

For Re s > 1: ζ(s)·Σ_{n≤X} μ(n)n^{−s} − 1 = −ζ(s)·Σ_{n>X} μ(n)n^{−s} (from L ζ · L μ = 1, i.e. `LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta`, summability `LSeriesSummable_moebius_iff`). Hence for Re s ≥ 2:

  |f(s) − 1| ≤ (π²/6)·Σ_{n>X} n^{−2} ≤ (π²/6)·(1/X)   (X ∈ ℕ: Σ_{n≥X+1} n^{−2} ≤ ∫_X^∞ u^{−2}du = 1/X).

- X ≥ 4 ⟹ π²/(6X) ≤ π²/24 < 0.412 ⟹ |f(2+it)| ≥ 1/2 (indeed ≥ 0.588). So X₀ = 4. (The task's ζ(2)/X is this; it is the version that uses 1/ζ = Σμ n^{−s}. The alternative via the product Dirichlet series, |f−1| ≤ Σ_{m>X} d(m)/m², needs no inversion but loses a log X; not needed.)
- The ≥ 1/2 bound is what Bohr–Landau needs; a power saving needs the sharper **−log|f(2+it)| ≤ −log(1 − π²/(6X)) ≤ π²/(3X)** (−log(1−x) ≤ 2x on [0,1/2]). This replaces the tree's `log 3` in `count_finset_le`. Also, on the part of each circle with Re s ≥ 2, log|f(s)| ≤ log(1 + π²/(6X)) ≤ π²/(6X) pointwise — no mean square needed there.
- Uniformity: in t, absolute; the only parameter is X.

## (b) The mean square of f on a line, over a window

Fix σ' ∈ [σ₁, 2], a window [a, a+ℓ] with a > 0, and N ≥ a + ℓ (so `zeta_approx_sharp` applies at every t of the window). Write s = σ'+it, ζ = S_N + P + E, P = N^{1−s}/(s−1), |P| ≤ N^{1−σ'}/a, |E| ≤ C_G N^{−σ'}.

**The polynomial.** A := S_N·M_X = Σ_{m ∈ Icc 1 (NX)} c_m m^{−s}, c_m := Σ_{d ≤ X, n ≤ N, dn = m} μ(d). Facts:
- m ≤ min(N, X) ⟹ c_m = Σ_{d|m} μ(d) = [m = 1] (`moebius_mul_coe_zeta`). In the scheme below X ≤ N always, so the diagonal is 1 + Σ_{X<m≤NX} c_m² m^{−2σ'}.
- all m: |c_m| ≤ d_X(m) := #{d | m : d ≤ X} ≤ d(m) (`abs_moebius_le_one`).
- **(E1), the one new elementary estimate**: for every real Y ≥ 0, Σ_{m≤Y} d_X(m)² ≤ Y·L³, L := 1 + log X. Proof: Σ_{m≤Y} d_X(m)² = Σ_{d₁,d₂≤X} #{m ≤ Y : d₁|m, d₂|m} = Σ_{d₁,d₂≤X} ⌊Y/lcm(d₁,d₂)⌋ ≤ Y·Σ_{d₁,d₂≤X} gcd(d₁,d₂)/(d₁d₂); with g = gcd, d_i = g e_i, e_i ≤ X/g: ≤ Y·Σ_{g≤X}(1/g)·(Σ_{e≤X} 1/e)² ≤ Y(1+log X)³ (`Nat.Ioc_filter_dvd_card_eq_div`, `Nat.gcd_mul_lcm`, `M1.sum_inv_le`; dropping coprimality only enlarges). This avoids Σ d(m)² ~ Y log³Y entirely and gives the same L³, with L in X, not in NX — the saving in the diagonal depends only on the mollifier length.
- **(D1)** diagonal tail, dyadic blocks (2^kX, 2^{k+1}X]: Σ_{X<m≤M} d_X(m)² m^{−2σ'} ≤ Σ_k (2^kX)^{−2σ'}·2^{k+1}X L³ = 2L³X^{1−2σ'}/(1−2^{1−2σ'}) ≤ K₁L³X^{1−2σ₁}, K₁ := 2/(1 − 2^{1−2σ₁}), for every M and every σ' ≥ σ₁ (both factors monotone in σ'). No Abel summation needed.
- **(D2)** off-diagonal weight, blocks (2^k, 2^{k+1}], 2^K ≤ M: Σ_{m≤M}(m+1)d_X(m)² m^{−2σ'} ≤ 2 + Σ_{k≤K} 2·2^{k(1−2σ')}·2^{k+1}L³ ≤ K₂L³M^{2−2σ₁}, K₂ := 4·2^{2−2σ₁}/(2^{2−2σ₁}−1) + 2 ≤ 11.6/(1−σ₁) + 2, uniformly for σ' ∈ [σ₁, 2].
- **Mean value on the window** (translation t = a + u, coefficients a_m := c_m m^{−σ'} m^{−ia}, same moduli; `integral_comp_add_right`, `cpow_add`; then `M1.dirichlet_meanSquare_le` with N := NX, T := ℓ):
  ∫_a^{a+ℓ} |A(σ'+it)|² dt ≤ ℓ(1 + K₁L³X^{1−2σ₁}) + 26K₂L³(NX)^{2−2σ₁}.
  Sanity check: for f = ζ (no mollifier) the diagonal is Σ_{n≤N} n^{−2σ'} ≈ ζ(2σ') − 1 + 1, so the relative excess is ζ(2σ')−1 > 0, a constant — that is exactly why Bohr–Landau's method gives O(T) and nothing better for ζ itself.

**The cross terms.** B := (P+E)M_X, |M_X(σ'+it)| ≤ Σ_{n≤X} n^{−σ₁} ≤ M̄ := 1 + X^{1−σ₁}/(1−σ₁) ≤ ((2−σ₁)/(1−σ₁))X^{1−σ₁} (`M1.sum_Icc_rpow_le`, a = −σ₁; crude pointwise bound, uniform in σ' ≥ σ₁). So |B| ≤ N^{−σ'}(N/a + C_G)M̄ ≤ q := N^{−σ₁}(N/a + C_G)M̄ pointwise. Using |A+B|² ≤ (1+η)|A|² + (1+1/η)|B|² (pointwise, two lines of `nlinarith`, the tree's `M2.norm_add4_sq_le` style) with η := q (when q ≤ 1):

  **(MS)** (1/ℓ)∫_a^{a+ℓ} |f(σ'+it)|² dt ≤ 1 + E, E ≤ Q + 3q + qQ, Q := K₁L³X^{1−2σ₁} + 26K₂L³(NX)^{2−2σ₁}/ℓ.

Using the mean square of M_X itself (M1 with a_n = μ(n)n^{−σ'}, dyadic in t with weight 1/t²) instead of the crude |M_X| ≤ M̄ gives (1/ℓ)∫|B|² ≪ N^{2−2σ₁}(1+X^{2−2σ₁})/(a²·ℓ)+…, the same size; it does not remove the square-root loss of the single-window route (the loss is real: P is large where t is small), so the crude bound is the right choice.

## (c) Disc geometry, the count, and the exponents

**Geometry** (fixed σ, σ₁; centre c_t = 2+it). R := 2 − σ₁ = (2−σ) + Δ ∈ (1, 3/2); r := (2−σ) + Δ/2; h := √(r² − (2−σ)²) = √((Δ/2)(2(2−σ)+Δ/2)). Then √Δ ≤ h ≤ 1 (Δ ≤ 1/2), and log(R/r) = log(1 + (Δ/2)/r) ≥ (Δ/2)/R ≥ Δ/3, so **2h·log(R/r) ≥ (2/3)Δ^{3/2}**. Every nontrivial zero ρ with Re ρ ≥ σ and |t − Im ρ| ≤ h lies in closedBall(c_t, r) ((2−Re ρ)² + (t−Im ρ)² ≤ (2−σ)² + h² = r²); this is `geom_facts` with δ = σ − 1/2, Rout = R, rin = r (the tree's hwin is h/2). The outer disc reaches Re s = σ₁ exactly, so one needs the mean square on every line σ' ∈ [σ₁, 2+R]; the lines σ' > 2 are handled pointwise by (a).

**Per t** (t ≥ 3, so the closed disc of radius R < 3/2 avoids s = 1; f(c_t) ≠ 0 by (a)): with n_f(t) := Σᶠ_u divisor f (closedBall c_t r) u ≥ Σ_{ρ ∈ S} zeta_order ρ for any finite set S of ζ-zeros in the small ball (divisor f = divisor ζ + divisor M_X ≥ divisor ζ: `MeromorphicOn.divisor_mul` + `AnalyticOnNhd.divisor_nonneg`, or pointwise `analyticOrderAt_mul`; then the tree's `finset_sum_zeta_order_le_finsum_divisor` pattern):

  n_f(t)·log(R/r) ≤ circleAverage(log‖f‖) c_t R − log‖f(c_t)‖ ≤ circleAverage(L_ε f) c_t R + π²/(3X),

where **L_ε f(z) := ½ log(ε² + ‖f z‖²)**, ε := X^{−1/2}. This is the step where the receipted proof must change: with `Lz = ½log(1+‖ζ‖²)` the next line would read ½log(1 + (1/ℓ)∫|f|²) ≈ ½log(2+E) = O(1), i.e. O(T) and no saving whatever E is. With L_ε, concavity of x ↦ ½log(ε²+x) on [0,∞) gives, on each vertical segment of length ℓ (`ConcaveOn.le_map_average`, the proof of `circleAverage_Lz_le` with the interval measure in place of the circle),

  (1/ℓ)∫ L_ε f(σ'+it) dt ≤ ½ log(ε² + (1/ℓ)∫|f|²) ≤ ½ log(1 + ε² + E) ≤ ½(ε² + E).

Two Lean details: log‖f‖ ≤ L_ε f fails at zeros of f on the circle (Mathlib's `Real.log 0 = 0` while L_ε = log ε < 0), so the comparison is a.e. on the circle (`ae_circleMap_ne_zero`, `integral_mono_ae`), exactly as JensenDisc already handles its `_of_ae` version; and L_ε f is continuous where f is, so the tree's joint-continuity/Fubini machinery (`continuousOn_Lz_circleMap`, `integrableOn_Lz_circleMap_prod`, `integral_circleAverage_Lz_eq_swap`) goes through with L_ε f in place of Lz.

**The count bound.** Window W := [U−h, 2U+h] (U ≥ 5 so W ⊂ [3, ∞) and so that every line-window below has a ≥ U/2), ℓ := |W| = U + 2h ≤ U + 2. Integrating the per-t bound over W and swapping (Fubini): for each angle θ the inner integral runs along Re s = σ'_θ = 2 + R cos θ over Im s ∈ [a_θ, a_θ+ℓ], a_θ = U − h + R sin θ ≥ U − 5/2 ≥ U/2, a_θ + ℓ ≤ 2U + 5/2 ≤ N := ⌈2U+3⌉ ≤ 3U. The left side, by the step-function bookkeeping of `count_le_integral`, is ≥ 2h·log(R/r)·NSigma σ U 2U (each zero's window [Im ρ − h, Im ρ + h] ⊆ W). Hence

  **NSigma σ U 2U ≤ ℓ·[½(ε² + E_max) + π²/(3X)] / (2h·log(R/r)) ≤ (3/(2Δ^{3/2}))·(U+2)·[½E_max + 9/X]**,

E_max := sup over σ' ∈ [σ₁, 2] of the E of (MS) on the windows [a_θ, a_θ+ℓ] (the σ' > 2 part contributes ≤ ε²/2 + π²/(2X) ≤ 6/X). This is the task's formula "[T·½log(1+E_max) + T log 2]/log(R/r)" with log 2 → π²/(3X) and the extra 1/(2h) made explicit; the power saving exists iff E_max and 1/X are powers of U^{−1}.

**Exponents, N ≈ T and X = T^a (single window [1,T], the receipted segment shape).** Here a = 1, ℓ ≈ T, N = ⌈T⌉: Q ≈ L³(T^{a(1−2σ₁)} + T^{1−2σ₁+a(2−2σ₁)}), but q ≈ T^{1−σ₁}X^{1−σ₁} > 1, so (MS) must be used in Cauchy–Schwarz form, (1/T)∫|f|² ≤ (√(1+Q) + √((1/T)∫|B|²))², with (1/T)∫|B|² ≈ T^{1−2σ₁}X^{2−2σ₁}: the cross term is 2·T^{(1−2σ₁)/2}X^{1−σ₁}. Balancing X^{1−2σ₁} = T^{(1−2σ₁)/2}X^{1−σ₁} gives a = (2σ₁−1)/(2σ₁) and

  θ_A(σ) = 1 − (2σ−1)²/(2σ)   (σ=3/4: 5/6; σ=0.9: 0.644; σ→1: 1/2; near 1/2: 1 − 4δ²/(1+2δ)).

A genuine power saving, strictly weaker than Carlson except asymptotically as σ → 1/2.

**Exponents, dyadic windows (N ≈ t).** With N = ⌈2U+3⌉ ≤ 3U, a ≥ U/2: N/a ≤ 6, N^{−σ₁} ≤ U^{−σ₁}, so q ≤ (6+C_G)((2−σ₁)/(1−σ₁))·X^{1−σ₁}U^{−σ₁}. Choose **X := ⌊U^{2σ₁−1}⌋** (then X ≤ U ≤ N, and X ≥ U^{2σ₁−1}/2). Then
- X^{1−2σ₁} ≤ 2U^{−(2σ₁−1)²}; (NX)^{2−2σ₁}/ℓ ≤ 3U^{2σ₁(2−2σ₁)−1} = 3U^{−(2σ₁−1)²};
- q ≤ (6+C_G)((2−σ₁)/(1−σ₁))·U^{−(2σ₁−1)² − 2σ₁(1−σ₁)}, i.e. smaller than the diagonal by U^{−2σ₁(1−σ₁)}: the cross term is negligible, no square root is lost.
So E_max ≤ K₃(σ₁)·L³·U^{−(2σ₁−1)²} for U ≥ U₀(σ₁), with K₃ := 2(2K₁ + 78K₂) + 3(6+C_G)(2−σ₁)/(1−σ₁), L ≤ 1 + log U, and U₀ chosen so that q ≤ 1, X ≥ 4, U ≥ 5. Since 1/X ≤ 2U^{−(2σ₁−1)} ≤ 2U^{−(2σ₁−1)²}:

  NSigma σ U 2U ≤ K₄·Δ^{−3/2}·(1+log U)³·U^{4σ₁(1−σ₁)},   K₄ := 2K₃ + 40 (generous), U ≥ U₀(σ₁),

because 1 − (2σ₁−1)² = 4σ₁(1−σ₁). Tiling (2U₀, T] by (T2^{−k−1}, T2^{−k}] and bounding the rest by the finite count NSigma σ 0 (2U₀) (`zerosIn_finite`):

  **NSigma σ 0 T ≤ C₀(σ₁) + 2K₄·Δ^{−3/2}·(4σ₁(1−σ₁))^{−1}·(1+log T)³·T^{4σ₁(1−σ₁)}**.

The balance is the classical one: diagonal T·X^{1−2σ}, off-diagonal (TX)^{2−2σ}, centre T/X, all equal to T^{4σ(1−σ)} at X = T^{2σ−1}; the dyadic X(U) is needed (not a convenience) for σ > (1+√5)/4 ≈ 0.809, where X = T^{2σ−1} alone exceeds the target T^{4σ(1−σ)} and the small-t blocks would dominate.

**Disc method versus Littlewood's lemma.** Littlewood on [σ₁, 2] × (U, 2U] weights each zero by (Re ρ − σ₁) ≥ Δ, so its geometric factor is Δ (and it needs: Littlewood's lemma itself — not in Mathlib, not on the tree — the horizontal-side bounds |arg f| ≪ log U via a Jensen count of the zeros of Re f, for which the tree has the `symZeta`/`reZeroSet_card_le_at` pattern for ζ but not for ζM_X, the growth bound `riemannZeta_linear_growth`, and a choice of U avoiding boundary zeros). The disc method's factor is (2/3)Δ^{3/2}. Same exponent in both; with Δ = 1/log T the disc method pays (log T)^{3/2} where Littlewood pays log T — a loss of (log T)^{1/2} and absolute constants, nothing more, in exchange for needing none of Littlewood's machinery. Both need the same worst line σ' = σ₁; the disc method additionally needs the mean square uniformly on σ' ∈ [σ₁, 2], which (MS) gives for free (every bound is monotone in σ'). On this tree the disc method is the cheaper route by a wide margin.

## (d) What exponent to expect, and the clean targets

With the receipted `zeta_approx_sharp` (error C_G N^{−σ'}, valid for 0 ≤ t ≤ N, σ' ≤ 2) Carlson's exponent is reachable; what the formula's range forces is only that N be chosen per window (N ≈ t), which costs bookkeeping, not mathematics. Ordered milestones, each a theorem with a power saving:

- **M1 (single window, minimal machinery)**: for 1/2 < σ₁ < σ < 1, ∃C, ∀T ≥ 2: NSigma σ 0 T ≤ C·T^{1−(2σ₁−1)²/(2σ₁)}·(1+log T)³. Uses one X = ⌊T^{(2σ₁−1)/(2σ₁)}⌋, N = ⌈T+5⌉ exactly in the shape of `zeta_approx_sharp_segment'`/`meanSquare_sharp_param`, and the Cauchy–Schwarz form of (MS). Near the line this is 1 − 4δ²/(1+2δ) — almost Carlson, which is the MNF-relevant regime.
- **M2 (one window plus a trivial cut)**: restrict to t ∈ [T^{1−κ}, T] with κ ∈ [(2σ₁−1)², 2σ₁(1−σ₁)] (nonempty iff σ₁ ≤ (3+√3)/6 ≈ 0.789), bound the zeros with Im ρ ≤ T^{1−κ} by `zeta_local_zero_count` (N(0,Y) ≤ A₀·Y·log(Y+3)), X = ⌊T^{2σ₁−1}⌋: then q ≈ T^{κ−σ₁}X^{1−σ₁} ≤ X^{1−2σ₁} and Carlson's T^{4σ₁(1−σ₁)}(log T)³ follows for all 1/2 < σ ≤ 0.789, in particular **N(3/4, T) ≪_ε T^{3/4+ε}**.
- **M3 (dyadic, full range)**: as in (c): ∀σ ∈ (1/2,1), ∀σ₁ ∈ (1/2,σ), ∃C, ∀T ≥ 2: NSigma σ 0 T ≤ C·T^{4σ₁(1−σ₁)}·(1+log T)³ — i.e. N(σ,T) ≪_{σ,ε} T^{4σ(1−σ)+ε}, Carlson's theorem. With σ₁ = σ − 1/log T (T ≥ T₀(σ), all σ₁-constants bounded on [σ − (σ−1/2)/2, σ]) and T^{4σ₁(1−σ₁)} ≤ e⁴T^{4σ(1−σ)}: N(σ,T) ≪_σ T^{4σ(1−σ)}(log T)^{9/2}. I believe the 9/2 but have not tracked every σ₁-dependence; the ε-form is safe.

Not reachable with these tools: a saving linear in σ − 1/2, "N(σ,T) ≪ T^{1−c(σ−1/2)}". Carlson's saving is (2σ−1)² = 4(σ−1/2)², quadratic; Ingham's 3(1−σ)/(2−σ) = 1 − (2σ−1)/(2−σ) is the first linear one and needs the fourth moment of ζ on the half-line (or the two-sum approximate functional equation), neither on the tree. So the honest "simplest clean target with a power saving" is N(σ,T) ≪_σ T^{1−c(σ)} with c(σ) = (2σ−1)²/(2σ) (M1) or 4(σ−1/2)² (M3), e.g. N(3/4,T) ≪ T^{3/4+ε}.

What it means for the strip: NSigma (1/2+δ) 0 T ≪ T^{1−4δ²+ε} is Bohr–Landau's O(T) sharpened to a power; it says nothing about zeros being absent (the gap), and `SpectralGapHyp Δ` is untouched. It would be, to my knowledge, the first kernel-checked zero-density estimate with a power saving at any pin, subject to the caveat already in the notes (Lewko's registered Palomar entry at v4.35.0-rc2 for σ > 3/4, reported and not verified).

## (e) Ingredient table

| ingredient | classical reference | Lean-shaped statement | on tree / Mathlib |
|---|---|---|---|
| Jensen's disc inequality, general f | Titchmarsh §3.6 (Jensen) | `sum_divisor_mul_log_le c r R f …` | yes (JensenDisc; Mathlib `AnalyticOnNhd.circleAverage_log_norm`) |
| concavity of log on circles | Jensen's inequality | `AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq` | yes (JensenDisc) |
| ε-majorant L_ε, a.e. comparison with log‖f‖, concavity on vertical segments | — | `segment_average_Leps_le : (1/ℓ)∫ L_ε f(σ'+it) ≤ ½log(ε² + (1/ℓ)∫‖f‖²)` | no; routine (Mathlib `ConcaveOn.le_map_average`, tree `ae_circleMap_ne_zero`, pattern `circleAverage_Lz_le`) |
| integrability of log‖f‖ on circles | — | `MeromorphicOn.circleIntegrable_log_norm_of_nonneg` | yes (Mathlib) |
| analyticity of ζM_X off 1; pole avoidance for t ≥ 3, R < 3 | — | `analyticOnNhd_riemannZeta`, `one_notMem_closedBall_two_add`, `AnalyticOnNhd.mul` | yes |
| divisor f ≥ divisor ζ on the ball (ζ-multiplicities counted by f) | — | `MeromorphicOn.divisor_mul`, `AnalyticOnNhd.divisor_nonneg`, `analyticOrderAt_mul`; tree `finset_sum_zeta_order_le_finsum_divisor` for ζ | yes (Mathlib) + adaptation |
| 1/ζ = Σμ(n)n^{−s} on Re s > 1 | Titchmarsh (1.1.6) | `LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta`, `LSeriesSummable_moebius_iff` | yes (Mathlib) |
| ‖ζ(s)‖ ≤ π²/6 on Re s ≥ 2; Σ_{n>X}n^{−2} ≤ 1/X | — | `norm_riemannZeta_le_of_two_le_re`; tail bound | yes; routine |
| centre bound ‖f(2+it)−1‖ ≤ π²/(6X), −log‖f(2+it)‖ ≤ π²/(3X), log‖f‖ ≤ π²/(6X) on Re s ≥ 2 | — | `centre_bound (X ≥ 4)` | no; routine from the two rows above |
| sharp approximate formula, error O(N^{−σ'}), N ≥ t, σ' ≤ 2 | Titchmarsh Thm 4.11 (x = N) | `BLClosure.zeta_approx_sharp` | yes (receipted v4), C_G ≈ 2.6 |
| ‖N^{1−s}/(s−1)‖ ≤ N^{1−σ₁}/t | — | `M2.norm_P_le` | yes |
| Σ_{d\|m}μ(d) = [m=1]; \|μ\| ≤ 1; d(m) = σ₀(m) | — | `moebius_mul_coe_zeta`, `abs_moebius_le_one`, `sigma_zero_apply` | yes (Mathlib) |
| S_N·M_X = Σ_{m≤NX} c_m m^{−s}, c_m = [m=1] for m ≤ X ≤ N, \|c_m\| ≤ d_X(m) | — | `prod_poly_eq`, `coeff_small`, `coeff_abs_le` | no; routine Finset regrouping (`Complex.mul_cpow_ofReal_nonneg`, `sum_product`) |
| (E1) Σ_{m≤Y} d_X(m)² ≤ Y(1+log X)³ | classical (Σ 1/lcm ≪ log³X; e.g. Ivić ch. 11 mollifier lemmas) | `sum_dX_sq_le` | no; the one new elementary estimate (`Nat.Ioc_filter_dvd_card_eq_div`, `M1.sum_inv_le`) |
| (D1), (D2) dyadic sums | partial summation | `tail_sum_le`, `weight_sum_le` with K₁, K₂ | no; routine (pattern `M3a.*`; or `Finset.sum_Ioc_by_parts`) |
| Dirichlet-polynomial mean value, general coefficients, constant 26, weight n+1 | Montgomery–Vaughan 1974, Cor. 3; Titchmarsh §7.? (weaker) | `M1.dirichlet_meanSquare_le` | yes |
| weighted Hilbert inequality, constant 13 | Montgomery–Vaughan 1974 | `Zeta23.MV.mvDiag_thirteen : MVDiag 13` (statement in §1) | yes (zeta23) |
| window translation ∫_a^{a+ℓ} = ∫_0^ℓ with twisted coefficients | — | `meanSquare_window` | no; routine (`integral_comp_add_right`, `cpow_add`) |
| ‖M_X(σ'+it)‖ ≤ 1 + X^{1−σ₁}/(1−σ₁) | — | `M1.sum_Icc_rpow_le` | yes |
| \|a+b\|² ≤ (1+η)\|a\|² + (1+1/η)\|b\|² | — | — | routine (pattern `M2.norm_add4_sq_le`) |
| (MS) window mean square of ζM_X | Titchmarsh §9.15–9.17 computation | `meanSquare_mollified_window` | no; assembly of the rows above |
| Fubini swap for circle averages over a t-window | — | `integral_circleAverage_Lz_eq_swap` (for Lz) | yes for ζ/Lz; re-prove with L_ε f |
| per-t count on window, step functions, Σ zero windows ⊆ W | — | `count_le_integral` (for ζ, [3,T+3], Lz, log 3) | yes; re-parametrize (f, W = [U−h, 2U+h], L_ε, π²/(3X)) |
| geometry: R = 2−σ₁, r, h, 2h log(R/r) ≥ (2/3)Δ^{3/2} | — | `geom_facts` (Rout, rin, hwin) + explicit lower bound | yes + routine |
| finiteness of zeros in a window; window additivity; NRight/NSigma | — | `zerosIn_finite`, `Ncount_add`, `NRight_add` | yes |
| dyadic tiling and sum over windows | — | `density_dyadic_sum` | no; routine |
| local count N(t,t+1) ≤ A₀log(\|t\|+3) (for M2's cut, and for Littlewood) | Titchmarsh Thm 9.2 | `zeta_local_zero_count` | yes |
| Riemann–von Mangoldt, N(T)/T → ∞ | Titchmarsh Thm 9.4 | `Zeta23.RvM.riemannVonMangoldt`, `ncountSuperlinear` | yes (not needed here) |
| Littlewood's lemma on rectangles; arg f on horizontal sides for ζM_X | Titchmarsh §9.9, §9.4 | — | no (rectangle integrals from PNT+ and `symZeta` for ζ exist; not needed on the disc route) |
| fourth moment / Ingham-strength input | Titchmarsh §7.6, §9.17 | — | no (hence no linear saving) |
| the target `carlson_density` (M3), `density_single_window` (M1) | Carlson 1920; Titchmarsh §9.15–9.17; Ivić ch. 11 | ∃C, ∀T ≥ 2, NSigma σ 0 T ≤ C·T^{4σ₁(1−σ₁)}·(1+log T)³ | no (the goal) |

Execution shape, in the project's node style: C1 centre bound → P1 product polynomial and coefficients → E1 → D1/D2 → MS (window mean square, parametric in a, ℓ, N, X, σ' ≥ σ₁) → J-ε (majorant, a.e. comparison, segment concavity) → F (Fubini with L_ε f) → K (window count bookkeeping for general f) → G (geometric constant) → A1 (M1 assembly) → A2 (M2) → A3 (M3 dyadic). Rough size: comparable to `BohrLandauPartial.lean` (~2000 lines), since J-ε/F/K are re-instantiations and only E1 and MS are new.

## Where I am not sure

1. Theorem numbering in Titchmarsh (which of 9.15/9.16 is Carlson) — not checked; the exponent 4σ(1−σ) for Carlson's theorem is standard.
2. C_G's independence of σ₀: read off the witness `12·(4/π³·ζ(3)) + 1/4` in `tail_sharp`; the docstrings say C(σ₀). Harmless either way (σ₀ := σ₁ is fixed).
3. Whether `MeromorphicOn.divisor_mul`'s order-≠-⊤ hypotheses are the convenient route or pointwise `analyticOrderAt_mul` is; both exist at the pin.
4. The log power 9/2 in the σ₁ = σ − 1/log T form (uniformity of K₁…K₄, U₀, C₀ in σ₁ near σ is clear in principle, not tracked constant by constant). The ε-form (M1–M3 as stated) carries no such risk.
5. M2's range σ ≤ (3+√3)/6 comes from κ ∈ [(2σ₁−1)², 2σ₁(1−σ₁)]; I did not optimise the cut (a second cut would extend it), since M3 covers the full range anyway.
6. The claim "first kernel-checked zero-density estimate with a power saving" is subject to Lewko's unverified Palomar entry noted in `math/notes/MNF_PUSH_FURTHER_2026-10-28.md`.


---

## Report 3

# What "tackling the strip" can mean today

Memo for the MNF / zeta23 formalization project, 2026-11-03. Written against the kernel-checked record on the zeta23 tree (`/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23`, receipts v2–v4 of `DEPOSIT_MAP.md` §10) and the OpenAI tree (7/8 half-plane, receipt `d8670539…`). Statements of the record were read from the Lean sources, not from the notes; literature claims are cited at the end.

## 0. Bottom line

1. The target, `SpectralGapHyp Δ` for some `0 < Δ < 1/2`, is kernel-checked to be exactly "no zero with `1/2 < Re ρ < 1/2 + Δ`" (`MNF.RH.gap_iff_zeroFreeBand`, `spectralGapHyp_iff_zeroFree_strip`). It follows from RH, it is RH for `Δ > 3/8` (given the 7/8 theorem), and for `0 < Δ ≤ 3/8` it is an open statement that no published method addresses. Nobody has claimed it for any `Δ > 0`; it is not even a named conjecture.
2. No known technique produces a zero-free band of fixed width anywhere in `1/2 < σ < 1` except the half-plane method behind the 7/8 theorem (and its parameter refinements). Everything else known beside the line is a *count*: Bohr–Landau `O(T)`, Littlewood/Selberg uniform bounds, Carlson–Ingham–Guth–Maynard power savings, proportions on the line. Counts cannot become zero.
3. Honest formal progress "toward the strip" therefore means one of three things: (a) sharpen the count beside the line from `O(T)` to a power saving — Carlson's `T^{4σ(1−σ)+ε}` is within reach of the tools now on the tree, Ingham's `T^{3(1−σ)/(2−σ)}` is the next rung and is not; (b) make the count uniform as `σ → 1/2` (Littlewood 1924); (c) shrink the *remaining* strip `(1/2, θ]` from the right by receipting a smaller half-plane constant `θ` when one is available, which is operations, not mathematics.
4. The `↔` layer (gap ⇔ band ⇔ mechanism ⇔ RH for large `Δ`) is complete and should stay frozen; adding restatements is not progress.
5. Section 5 gives a five-question test that any proposed "strip argument" must pass; the record already contains the kernel-checked refutations of the MNF-internal ones.

## 1. The zero-free strip beside the line

**Definition in the record.** `SpectralGapHyp Δ := ∀ x ∈ ShiftedZeroSpectrum, x = 0 ∨ |x| ≥ Δ` with `ShiftedZeroSpectrum = {Re ρ − 1/2 : ρ nontrivial zero}` (`MNF/RH/Gap.lean`, `Core.lean`). `gap_iff_zeroFreeBand` and `gap_of_right_side` (`Reduction.lean`) show it is the right-hand band alone; the left band follows from `ρ ↦ 1 − ρ`.

**Logical position (all kernel-checked except where marked).**

| statement | relation to the strip | where |
|---|---|---|
| RH | RH ⟹ strip for every Δ (`gap_of_rh`); strip ⟹ RH iff Δ ≥ 1/2 unconditionally (`riemannHypothesis_iff_gap_half`) | `Hypotheses.lean`, `Core.lean` |
| zero-free half-plane `Re s > θ` | strip(Δ) ∧ half-plane(θ) ⟹ RH whenever Δ > θ − 1/2 (`riemannHypothesis_iff_gap_of_zeroFree`); RH ⟺ no zero in `1/2 < Re s ≤ θ` (`riemannHypothesis_iff_remaining_strip`); at θ = 7/8 the threshold is Δ > 3/8, and a gap at exactly 3/8 says every zero has Re ∈ {1/2, 1/8, 7/8} (`spectralGapHyp_three_eighths_iff_of`) | `Gap.lean`, `Hypotheses.lean`, OpenAI tree |
| Lindelöf (LH) | neither implies the other. Backlund (1918/19): LH ⟺ for every σ > 1/2, `N(σ,T+1) − N(σ,T) = o(log T)` — "few zeros per unit height", never zero. A strip gives 0 per unit height below 1/2+Δ and says nothing above it | literature |
| Density Hypothesis (DH: `N(σ,T) ≪ T^{2(1−σ)+ε}`) | neither implies the other; LH ⟹ DH (Ingham 1937) | literature |
| GRH | GRH for ζ is RH; GRH for other L-functions says nothing about ζ's strip | — |
| Bohr–Landau | strip(Δ) + BL ⟹ density one on the line, now with no literature hypothesis: `MNF.RH.onLineDensityOne_of_gap_only` (receipt v4). Density one on the line does not imply a strip | `BohrLandauClosure.lean` |
| "narrow box" hypotheses (all zeros within `b/log T` of the line) | the opposite kind of near-line hypothesis; box ∧ strip ⟹ RH for large T trivially. Used by Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh (2025): box with b = 0.3185 ⟹ 2/3 of zeros simple and on the line | literature |

**What a strip would imply.** With the known inputs: all off-line zeros have `|β − 1/2| ≥ Δ`, so `N_off(T) ≤ N(1/2+Δ, T)`, which is `O(T)` (Bohr–Landau, formalized), `≪ T^{1 − 2Δ/(3/2−Δ)} log^5 T` (Ingham, literature), `≪ T^{1−2Δ+ε}` under DH. Hence density one on the line (formalized). It would *not* improve the prime number theorem error term (that is governed by zeros near `Re s = 1`), would not give LH, DH, or simplicity, and for `Δ ≤ 3/8` is not known to give RH. Its only "structural" content is the one the record already states: the shifted spectrum has 0 as an isolated point.

**Has anyone claimed it?** Not in the peer-reviewed literature, and the hypothesis has no standard name; the named neighbours are the quasi-Riemann hypothesis (a zero-free half-plane, which the OpenAI tree now gives at 7/8), LH, DH and the box hypotheses above. The numerical record is consistent with any strip: all 12,363,153,437,138 zeros up to height 3,000,175,332,800 are on the line and simple (Platt–Trudgian 2021), so the strip holds vacuously below that height; this is not a theorem about large `t` and is not formalizable without importing the interval-arithmetic computation.

**Why it is "strictly weaker" only in the one-directional sense.** The reviewer's wording in the ledger is the right one: the strip follows from RH and is not known to imply it. Nothing kernel-checkable separates them for `Δ ≤ 3/8`.

## 2. State of the art on zeros in the strip

### 2a. Zero-free regions near `Re s = 1` (the other edge)

| region | source |
|---|---|
| `σ ≥ 1 − c/log t` | de la Vallée Poussin 1899 |
| `σ ≥ 1 − c/((log t)^{2/3}(log log t)^{1/3})` | Vinogradov–Korobov 1958 |
| explicit classical: `σ ≥ 1 − 1/(5.558691 log|t|)`, `|t| ≥ 2`; explicit VK: `σ ≥ 1 − 1/(55.241 (log|t|)^{2/3}(log log|t|)^{1/3})`, `|t| ≥ 3` | Mossinghoff–Trudgian–Yang 2022 |
| explicit VK constant 54.004 (`|t| ≥ 3`), 48.0718 asymptotically, from `|ζ(σ+it)| ≤ 70.7 |t|^{4.438(1−σ)^{3/2}} log^{2/3}|t|` | Bellotti 2023 |
| Littlewood-type: `σ > 1 − log log t/(21.233 log t)` | Yang 2023 |
| classical constant 4.896: `ζ(σ+it) ≠ 0` for `t ≥ 3`, `σ ≥ 1 − 1/(4.896 log t)` | Bellotti–Trudgian–Yang, March 2026 |
| on the tree, kernel-checked: `ZetaZeroFree`: `ζ(σ+it) ≠ 0` for `|t| > 3`, `1 − A/(log|t|)^9 ≤ σ < 1` (PNT+ port, `Zeta23/FromPNTPlus/ZetaBounds.lean`); plus `ZetaUpperBnd`, `ZetaInvBnd`, `LogDerivZetaBndUnif` in the same region | record |
| on the OpenAI tree, receipted: `ZeroFreeRightOf (7/8)` | record |

Every region in the first six rows has width tending to 0 as `t → ∞`; none is a band. The 7/8 theorem is the only fixed band, and for `|t|` large it contains all of them. For the strip *beside 1/2* this whole family is irrelevant: it concerns the other edge of the critical strip. (The 3-4-1 inequality behind it, `norm_zeta_product_ge_one`/`ZetaLowerBound1` on the tree, needs the Euler product in a region where it converges; it has no analogue near `σ = 1/2`.)

### 2b. Zero-density estimates `N(σ,T) ≪ T^{A(σ)(1−σ)+ε}` beside the line

| bound | exponent, correctly stated | where it is the record (ANTEDB Table 11.1) |
|---|---|---|
| Bohr–Landau 1914 | `N(σ,T) = O_σ(T)` for each fixed σ > 1/2 | formalized: `Zeta23.BL.bohrLandau_full` |
| Littlewood 1924 | `Σ_{0<γ≤T}(β−1/2)^+ ≪ T log log T`, equivalently `N(σ,T) ≪ T log log T/(σ−1/2)` uniformly in σ > 1/2 (Littlewood's lemma + Hardy–Littlewood mean square + Jensen's inequality) | the only classical bound uniform down to `σ − 1/2 ≍ log log T/log T` |
| Carlson 1920 | `N(σ,T) ≪ T^{4σ(1−σ)+ε}`; explicit: `≤ 0.78 T^{4σ(1−σ)}(log T)^{5−2σ}` (Chourasiya 2024) | superseded everywhere by Ingham, but it is the first power saving and the one the record's tools reach |
| Selberg 1946 | `N(σ,T) ≪ T^{1−(σ−1/2)/4} log T` uniformly for 1/2 ≤ σ ≤ 1; Jutila and Conrey: `T^{1−θ(2σ−1)} log T` with any θ < 1/2, resp. θ < 4/7; Selberg also sharpened Littlewood's displacement sum to `Σ(β−1/2)^+ = O(T)` (attributed to his 1946 paper in the notes to Titchmarsh Ch. IX; not re-verified in the original here) | the log-free family near 1/2; an improvement of Ingham near 1/2 would need θ > 2/3 |
| Ingham 1940 | `N(σ,T) ≪ T^{3(1−σ)/(2−σ)} log^5 T`, i.e. `A(σ) ≤ 3/(2−σ)`; explicit log exponent `(7−5σ)/(2−σ)` (Chourasiya–Simonič 2025) | **best known for 1/2 ≤ σ ≤ 7/10, hence beside the line**: `N(1/2+Δ,T) ≪ T^{1 − 2Δ/(3/2−Δ)+ε}` |
| Huxley 1972 | `N(σ,T) ≪ T^{3(1−σ)/(3σ−1)+ε}` for σ ≥ 3/4, giving the uniform `A(σ) ≤ 12/5` | superseded in every range |
| Jutila 1977, Bourgain 2000 | DH (`A(σ) ≤ 2`) for σ ≥ 11/14, resp. σ ≥ 25/32 | Bourgain's `3/(2σ)` is the record on `[1867/2347, 4/5)` |
| Guth–Maynard 2024 | `N(σ,T) ≤ T^{30(1−σ)/13+o(1)}` uniformly; sharper `A(σ) ≤ 15/(3+5σ)` on `7/10 ≤ σ < 19/25`; short intervals of length `x^{17/30+o(1)}` | record on `[7/10, 19/25)` |
| Density Hypothesis | `A(σ) ≤ 2` for all σ | open for 1/2 < σ < 25/32; implied by LH |
| near σ = 1 | Halász–Turán type `A(1−η) ≤ C η^{1/2}`, i.e. `N(σ,T) ≪ T^{C(1−σ)^{3/2}}(log T)^{C'}`, constants down to any C > 3√2 (Pintz) | irrelevant to the strip beside 1/2 |

Two consequences for the strip question. First, *beside the line nothing has moved since 1940*: Guth–Maynard, Bourgain, Jutila, Heath-Brown, Pintz and the 2024–25 Guth–Maynard-based improvements all live at σ ≥ 7/10. Second, the conjectural ceiling of the whole method is DH, which still leaves `T^{1−2Δ+ε}` zeros, not 0.

### 2c. What Guth–Maynard changed, and how far it is from formalizable

Guth–Maynard prove a new large-values estimate: for a Dirichlet polynomial of length `N`, the number of 1-spaced points in `[0,T]` where it exceeds `V ≈ N^{3/4}` (the critical size) is bounded better than the classical Montgomery–Halász/Huxley bounds; the zero-density estimate follows by the standard zero-detecting method, and the uniform 30/13 is obtained by combining their bound with Ingham's for σ ≤ 7/10. The proof is 48 pages of Fourier analysis on the Gram matrix of exponentials (a high/low frequency decomposition with an energy argument), on top of the standard apparatus (mean value theorem for Dirichlet polynomials, Halász–Montgomery, Hölder, zero detection with mollified polynomials and the fourth moment of ζ).

Formal status: the tree has exactly one of these ingredients, the Montgomery–Vaughan weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen : MVDiag 13` (for any finite family with injective frequencies `λ_r` and gaps `δ_r ≤ |λ_r − λ_s|`: `‖Σ_{r≠s} x_r x̄_s/(λ_r−λ_s)‖ ≤ 13 Σ|x_r|²/δ_r`, literature constant 3π/2), and its consequence `M1.dirichlet_meanSquare_le`: `∫_0^T |Σ_{n≤N} a_n n^{−it}|² ≤ T Σ|a_n|² + 26 Σ (n+1)|a_n|²`. Nothing else of the large-values theory exists in Mathlib or on the tree (scoping report §2: no large sieve, no Halász–Montgomery, no fourth moment). Guth–Maynard is years away from a kernel-checked proof; and even then it would not touch σ < 7/10.

## 3. Proportions of zeros on the line

| proportion | status | source |
|---|---|---|
| positive proportion on the line | 1942 | Selberg |
| > 1/3 (then 0.3474) | 1974/75 | Levinson |
| > 2/5 (0.4088) | 1989 | Conrey |
| 41.05% | 2011 | Bui–Conrey–Young (Feng 2012 announced 41.28%; superseded) |
| > 5/12 (41.72%) on the line; 40.75% simple and on the line | 2020 | Pratt–Robles–Zaharescu–Zeindler |
| ≥ 2/3 simple (under RH); 0.6725 (Montgomery–Taylor, under RH); 19/27 simple under RH (+GLH) | conditional | Montgomery 1973; Montgomery–Taylor; Conrey–Ghosh–Gonek, Bui–Heath-Brown |
| ≥ 2/3 simple and on the line, ≥ 5/6 distinct, unconditionally; 0.6725 / 0.8362 with the Montgomery–Taylor window; same for primitive Dirichlet L-functions | 2026, **formalized and receipted here** (`Zeta23.two_thirds_simple_on_critical_line`, `montgomery_taylor_*`, receipt `e0b9a4d9…`; restated over MNF names in `MNF/RH/Zeta23Restated.lean`) | Alpöge–Furman (arXiv:2608.13637) |
| if all zeros in `(T,2T]` lie within `0.3185/log T` of the line, then ≥ 2/3 simple on the line | conditional on a box hypothesis | Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh 2025 |
| proportion within δ of the line = 1 − o(1) for every fixed δ > 0 | **formalized**: `MNF.RH.reservoirDensityOne_unconditional` (receipt v4) | Bohr–Landau 1914 |

Reading the last two rows together is the whole situation in one line: within any fixed δ the proportion is 1 − o(1); on the line itself it is ≥ 2/3; nothing says the remaining ≤ 1/3 is empty, and a strip would say exactly that for the part at distance < Δ.

What the Alpöge–Furman machinery says about zeros at distance ≥ δ: nothing beyond Bohr–Landau. In the zero side (`Zeta23/ZeroSide.lean`), off-line zeros enter only as pairs `{ρ, 1−ρ̄}` with evaluation vectors `(φ̂(γ_ρ − τ_k))_k`, `γ_ρ = (ρ−1/2)/i`; the rank–trace inequality bounds the number of on-line atoms against the pair blocks and never localizes a pair by `|β − 1/2|`. The record's restatement `offLine_le_one_third` (all off-line zeros, with multiplicity, ≤ (1/3+ε)N) is the complete content on that side, and for zeros at distance ≥ δ it is weaker than `bohrLandau_full`. The method is a lower-bound certificate, not a zero detector.

## 4. What the record could turn into a new formal theorem

Tools, with the shapes actually proved (all `[propext, Classical.choice, Quot.sound]`, Comparator-accepted in receipts v2–v4):

- T1 `BLClosure.zeta_approx_sharp` (BohrLandauClosure.lean:954): for σ₀ > 0 there is C with `‖ζ(s) − Σ_{n≤N} n^{−s} − N^{1−s}/(s−1)‖ ≤ C N^{−σ}` for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N, N ≥ 1, s ≠ 1. Built from `first_derivative_test_amp_smooth` (Titchmarsh 4.3 for a C² phase), `B2per_fourier`, `zeta_eq_euler_maclaurin` (from the tree's `Zeta0EqZeta`), `tail_sharp`.
- T2 `M1.dirichlet_meanSquare_le` (general coefficients, constant 26, from `mvDiag_thirteen`); `DPMV.dirichlet_mean_value` (direct expansion, off-diagonal `2/|log(n/m)|`).
- T3 `BLClosure.meanSquareUnif_all`: for every σ₁ > 1/2, `∃ C, ∀ σ ≥ σ₁, ∀ T ≥ 2, ∫_1^T ‖ζ(σ+it)‖² ≤ C T`; explicit constant for σ₁ ≥ 2/3 in `M3.meanSquareUnif_explicit`.
- T4 the disc counter (BohrLandauPartial.lean, nodes J0–J9): Mathlib Jensen on `closedBall (2+tI) R`, `Lz = ½ log(1+‖ζ‖²)`, concavity `circleAverage log‖f‖ ≤ ½ log circleAverage ‖f‖²` (JensenDisc.lean), Fubini over t, `count_le_integral`, `count_le_meanSquare'`, `rightHalf_of_meanSquareUnif` (uniform mean square on `Re s ≥ σ₁` ⟹ `NRight δ T = O(T)` for δ > σ₁ − 1/2), reflection `NLeft_eq_NRight`. The centre lower bound is `zeta_lower_bound_two : 1/3 ≤ ‖ζ(2+it)‖`.
- T5 zeta23's own layer: `riemannVonMangoldt_zeta` (N(T,2T) = (T/2π)ℓ₁(T) + O(log T), local count `N(t,t+1] ≤ A₀ log(|t|+3)`), `backlund_horizontal` (|Im ∫_{1/2}^2 ζ'/ζ(σ+iT)dσ| ≤ C log T off ordinates), `zeta_growth`, `zerosIn_finite`, `ncountSuperlinear`.
- T6 the explicit-formula stack (`Zeta23/WeilEF`, `ExplicitFormula*`, `ZeroSide`, `PrimeSideA/B`, `Assembly`, Gevrey taper profiles in `Zeta23/Taper/Gevrey*.lean`).
- T7 Mathlib at the pin: `ArithmeticFunction.moebius`, `moebius_mul_coe_zeta : μ * ζ = 1`, `sum_eq_iff_sum_mul_moebius_eq`, `Nat.divisors`, `card_divisors_le_self` (only the crude `d(n) ≤ n`), Abel summation (`Mathlib/NumberTheory/AbelSummation.lean`: `sum_mul_eq_sub_integral_mul`), `ConcaveOn.le_map_average`, layer-cake `lintegral_eq_lintegral_meas_lt`, the disc Jensen formula. Absent: Littlewood's lemma (rectangle), any `d(n) ≪ n^ε`, any mean-value or large-sieve material.

Before claiming novelty for any density theorem: `DEPOSIT_MAP.md` §8 records Lean zero-density estimates by Mark Lewko on Palomar (PALOMAR-2026-10-11-000010 and -10-21-000008, Lean v4.35.0-rc2, one-sided `Re ρ ≥ σ`). Read those two entries first; if they already contain a Carlson- or Ingham-type exponent, candidate 1 below becomes "at this pin, on this trust base, two-sided" rather than "first".

### Candidates

**1. Carlson's zero-density theorem via the Möbius mollifier.** Target: `∀ σ > 1/2, ∀ ε > 0, N(σ,T) ≪_{σ,ε} T^{4σ(1−σ)+ε}` in the record's vocabulary (`NRight δ T` with σ = 1/2+δ), the first power-saving zero-density bound. Route, entirely with T1–T5 + T7: `M_X(s) = Σ_{n≤X} μ(n) n^{−s}`, `f = ζ M_X`. By T1 with `N = ⌈T⌉`, `f − 1 = g + (main term)·M_X + (error)·M_X` where `g = Σ_{X<n≤NX} c_n n^{−s}`, `c_n = Σ_{d|n, d≤X, n/d≤N} μ(d)` (so `c_n = [n=1]` for `n ≤ min(N,X)` by `μ * ζ = 1`, `|c_n| ≤ d(n)`). T2 gives `∫_1^T |g(σ'+it)|² ≪ T Σ_{n>X} d(n)² n^{−2σ'} + 52 Σ d(n)² n^{1−2σ'}`, monotone in σ' ≥ σ₁; with `Σ_{n≤Y} d(n)² ≤ Y(1+log Y)³` (elementary: `Σ_{a,b≤Y} ⌊Y/lcm(a,b)⌋`) and Abel summation this is `≪ T^{1−(2σ₁−1)²+ε}` at `X = T^{2σ₁−1}`; the main-term piece `(TX)^{2−2σ₁} = T^{4σ₁(1−σ₁)}` forces the same `X`. Then run T4 for `f` instead of `ζ`: the centre bound is `|f(2+it)| ≥ 1 − Σ_{n>X} d(n)/n² ≥ 1/2` for `X ≥ X₀`, and the Jensen step uses `log ‖f‖ ≤ ½ log circleAverage‖f‖² ≤ ½(circleAverage‖f‖² − 1) = circleAverage(Re g + ½|g|²)` (the inequality `log x ≤ x − 1` is the whole trick; the `Re g` term integrates to `≪ (TX)^{1−σ₁+ε}`, which is smaller). Result `N(1/2+δ, T) ≪ T^{4σ₁(1−σ₁)+ε}` for every `σ₁ < 1/2+δ`. Cost: a generic-`f` copy of J4–J8 (≈800 lines), mollifier algebra and the divisor-square bound (≈600), the mean square of `g` with Abel summation (≈600), assembly with exponents (≈300): a few thousand lines, two or three workflows of the size that closed Bohr–Landau. Risk: medium (bookkeeping of `c_n`, the `d(n)²` sum, uniformity in σ'). Value to the strip: this is the first formal statement that zeros beside the line are `T^{1−c}` rather than `T`; it is also exactly the architecture Ingham, Huxley and Guth–Maynard refine, so it is the right foundation if the project ever goes further.

**2. The Hardy–Littlewood mean square down to the line, uniform in σ.** Target: `∃ C, ∀ σ ∈ [1/2, 2], ∀ T ≥ 2, ∫_1^T ‖ζ(σ+it)‖² ≤ C T log T` (and the `T log T` asymptotic shape on `σ = 1/2`). From T1 with `N = ⌈T⌉` and T2 with `a_n = n^{−σ}`: diagonal `T Σ_{n≤T} n^{−2σ} ≤ T(1+log T)` (`M1.sum_inv_le`), off-diagonal `26 Σ (n+1) n^{−2σ} ≤ 52 T^{2−2σ} ≤ 52 T`, main term `∫_1^T T/t² ≤ T`. About 200–400 lines; no new ideas. Value: the classical theorem of 1918, a prerequisite of candidate 3, and the σ-uniformity the present `meanSquareUnif_all` lacks (its constant blows up as σ₁ → 1/2).

**3. Littlewood's 1924 uniform bound.** Target: `Σ_{0<γ≤T}(β−1/2)^+ ≤ (T/4π) log log T + O(T)` and `N(σ,T) ≪ T log log T/(σ−1/2)` uniformly for σ > 1/2 — the only classical statement that is nontrivial for `σ − 1/2` as small as `K log log T/log T`. Needs candidate 2 plus Littlewood's lemma for ζ on `[1/2,2]×[1,T]`, which is absent from Mathlib and the tree (scoping report §2). The tree's rectangle machinery (`N_eq_halfContour_completedZeta`, `halfContour_completedZeta_split`, `exists_goodHeight`, `backlund_horizontal` with its proof via sign changes of `Re ζ` on a segment, adaptable to sub-segments) plus the layer-cake identity `Σ m_ρ(β−σ₀)^+ = ∫_{σ₀}^{2} N_ζ(σ';T) dσ'` and `∂_σ log‖ζ‖ = Re(ζ'/ζ)` gives the lemma in ≈1–2k lines. Then the theorem is `ConcaveOn.le_map_average` applied to candidate 2. Cheap fallback with the existing disc counter and candidate 2 only: a uniform bound with the worse exponent `N(1/2+η, T) ≪ T log log T/η^{3/2}` (the disc of radius 3/2 about `2+it` covers a zero at distance η from the line only for `|t−γ| ≲ √η`, and `hwin`/`log(Rout/rin)` in `geom_facts` are exactly these quantities), ≈500 lines.

**4. Bookkeeping consequences of a strip.** `SpectralGapHyp Δ → NOff_line T ≤ NRight δ T + NLeft δ T` for every δ ≤ Δ, hence any density bound at `1/2+Δ` bounds all off-line zeros; ≈50 lines. Zero mathematical value (the reviewers' "stop adding equivalences" applies); only worth it if the deposit map needs the sentence as a theorem.

**5. Ingham 1940.** The next rung after candidate 1 (`3(1−σ)/(2−σ)` is the record beside the line). It needs the fourth moment `∫_1^T |ζ(1/2+it)|⁴ ≪ T log⁴ T`, which needs the symmetric approximate functional equation (Titchmarsh Thm 4.13: lengths `√(t/2π)`, van der Corput/stationary phase); T1 is the one-sided formula with `N ≥ t` and cannot give it. Well above 5k lines; not now.

**6. Selberg's `O(T)` and Selberg's density bound.** Need Selberg's mollified moments of `log|ζ|`; out of reach, and candidate 3 already carries the uniformity that matters.

**7. Explicit-formula refinements for `|β − 1/2| ≥ δ` (T6).** No target: any zero-detecting use of the explicit formula becomes the large-values machinery again, and the certificate class of the method has a formalized ceiling (`Zeta23.PairCeiling.ceiling_law256`: bandwidth-one certificates certify at most 0.6818 + 2.55·10⁻⁶·(…) simple zeros). T6 is the wrong tool for counting off-line zeros by distance.

**8. Density Hypothesis near σ = 1 / Vinogradov–Korobov-type bounds.** Out of reach (Vinogradov's mean value theorem, or Halász–Montgomery large values) and of no value to the strip beside 1/2; on the OpenAI tree the 7/8 half-plane already contains every near-1 region for large `t`.

**9 (operations, not mathematics). Shrink the remaining strip from the right.** `riemannHypothesis_iff_remaining_strip` is parametric in θ: a cold receipted run of a smaller half-plane constant (Liu's `(1507 − 2√921)/1653 ≈ 0.874957`, the tracker's `0.873985`, both recorded in `DEPOSIT_MAP.md` §8 as unreceipted here) instantiates it verbatim with `Δ > θ − 1/2`. This is the only known way the open strip `(1/2, θ]` gets narrower, and it needs no new proof from this project.

### Ranking by (value to the strip question) × (feasibility with the listed tools)

| rank | candidate | value | feasibility | note |
|---|---|---|---|---|
| 1 | Carlson density via mollifier (4) | medium | medium | first power saving; check Lewko's Palomar entries first |
| 2 | Hardy–Littlewood mean square down to the line (2) | low alone, enabling | very high | do it first; 200–400 lines |
| 3 | Littlewood 1924 uniform bound (3), disc fallback first | medium | medium / high (fallback) | the only near-line uniformity in reach |
| 4 | receipt a smaller θ (9) | real but external | high (ops) | not this project's mathematics |
| 5 | Ingham (5) | medium-high | low | fourth moment |
| 6 | bookkeeping (4) | ~0 | trivial | only for the map |
| 7 | Selberg (6), AF refinements (7) | medium / none | very low / none | — |
| 8 | DH near 1, VK (8) | none for the strip | none | — |

What none of this does: produce a `GapMechanism Δ`, a `ZeroFreeBand Δ`, or any statement that excludes a single zero. The candidates sharpen "how many" and "how uniformly", which is the honest meaning of "tackling the strip" with counting tools.

## 5. What would falsify each approach as a route to a strip

**Mean-value / density methods (candidates 1–3, 5, 6, Guth–Maynard).** They bound a count by an integral (`∫ log|f|`, `∫|g|²`) that does not change if one zero is moved; their conjectural ceiling is DH (Montgomery's large-values conjecture), i.e. `T^{1−2Δ+ε}` zeros beside the line, never 0. Concrete refutation of any "strip by mean values" argument: the Davenport–Heilbronn function (a combination of two L-functions mod 5) satisfies a Riemann-type functional equation, has the same growth and mean-square inputs, has no Euler product, and has `≫ T` zeros with `Re s > 1` (Davenport–Heilbronn 1936) and zeros inside `1/2 < σ < 1` (Spira; Bombieri–Ghosh 2011 study their distribution). Mathlib's `hurwitzZeta` at a rational `a ∉ {1/2, 1}` is another example with zeros in `Re s > 1`. An argument that would run unchanged for either of them proves nothing about a band; the only place candidate 1 uses ζ's multiplicativity is `μ * ζ = 1` in the mollifier, and that use yields a power saving, not a band. Sanity bound: any claimed exponent beside the line better than Ingham's (`θ > 2/3` in the `T^{1−θ(2σ−1)}` normalization) is a research result to be checked against the ANTEDB; better than DH (`θ > 1`) is almost certainly an error.

**Proportion methods (Levinson, Conrey, PRZZ, Alpöge–Furman).** They are lower-bound certificates. Even "proportion `1 − o(1)`" leaves `o(N)` zeros, and the formalized ceiling (`ceiling_law256`) shows the bandwidth-one certificate class stops below 0.69. Falsifier: the certificate is a function of `(tr, ‖·‖_F)` of a Gram matrix; exhibit a zero configuration (any `ZeroConfig`) with an off-line pair that produces the same trace and Frobenius norm — the method cannot distinguish it, so it cannot exclude the pair.

**Pair-correlation / box methods (BGST 2025).** They consume a near-line hypothesis (`b/log T` box) and produce proportions; they are refuted as strip-producers by their own hypothesis. Combined with a gap they are RH for large `T`, trivially.

**Half-plane methods (the 7/8 theorem and refinements).** The only method that gives fixed bands. Falsifier for reaching `1/2+Δ`: a barrier, i.e. the parameter refinements (0.875 → 0.874957 → 0.873985 in the tracker) converging to some `σ_∞ > 1/2`; and the Davenport–Heilbronn test applied to each refinement step (the theorem is stated for Dirichlet L-functions, so some step must use the Euler product; a step that would also apply to Davenport–Heilbronn is wrong). This memo has not examined the argument itself.

**MNF-internal mechanisms (gap, nullification, τ-probes, sign gate, Sturm–Liouville, injection/ejection).** Already falsified as mechanisms in the kernel: `gapMechanism_iff` (a mechanism is the band renamed), `probes_zero_iff` ("both probes read 0" is `Re ρ = 1/2`), `sign_gate_trivial` (returns `{0}` on any symmetric set), `multipleZeroKillsGap_iff`/`fischerForward_iff` (each is `RH → AllZerosSimple`), `realization_forces_line` (filling the Schrödinger dictionary is RH), and the four-point `Counter` set (`symmetric_bounded_not_on_line`): any proposed mechanism must be run on `Counter`; if it "works" there, it is vacuous.

**Five questions for any proposed strip argument.** (i) Where does it use the Euler product or `μ`? (ii) Would it apply verbatim to the Davenport–Heilbronn function or to `hurwitzZeta (1/3)`? (iii) Is its output exactly 0 on a band uniformly in `t`, or a count `o(T)`, `T^{θ}`, or a region of width `→ 0`? (iv) Which of `GapMechanism Δ`, `ZeroFreeBand Δ`, `SchrodingerRealization` does it construct (`notes/FRONTIER.md`)? (v) Is it consistent with Platt–Trudgian (no off-line zero below `3·10^12`), i.e. does it not predict low-height off-line zeros?

## Sources

Literature
- Guth, Maynard, *New large value estimates for Dirichlet polynomials*, arXiv:2405.20552 (v2 April 2026; Annals of Mathematics listing 2026): https://arxiv.org/abs/2405.20552 , https://annals.math.princeton.edu/2026/203-2/p06
- Tao, Trudgian, Yang, *Analytic Number Theory Exponent Database*, arXiv:2501.16779, and its zero-density chapter (Table 11.1, §11.2): https://arxiv.org/abs/2501.16779 , https://teorth.github.io/expdb/blueprint/zero-density-chapter.html
- Mossinghoff, Trudgian, Yang, *Explicit zero-free regions for the Riemann zeta-function*, arXiv:2212.06867: https://arxiv.org/abs/2212.06867
- Bellotti, *Explicit bounds for the Riemann zeta function and a new zero-free region*, arXiv:2306.10680: https://arxiv.org/abs/2306.10680
- Yang, *Explicit bounds on ζ(s) in the critical strip and a zero-free region*, arXiv:2301.03165: https://arxiv.org/pdf/2301.03165
- Bellotti, Trudgian, Yang, *Zero-free regions inspired by work of Heath-Brown*, arXiv:2603.21490 (March 2026): https://arxiv.org/abs/2603.21490
- Chourasiya, Simonič, *An explicit form of Ingham's zero density estimate*, arXiv:2507.15184: https://arxiv.org/abs/2507.15184
- Chourasiya, *An explicit version of Carlson's theorem*, arXiv:2412.02068: https://arxiv.org/abs/2412.02068
- Simonič, *Explicit zero density estimate for the Riemann zeta-function near the critical line*, arXiv:1910.08274: https://arxiv.org/abs/1910.08274
- Pintz, *A remark on density theorems for Riemann's zeta-function*, arXiv:2310.04544 (LH ⟹ DH, Ingham 1937; Halász–Turán): https://arxiv.org/pdf/2310.04544
- Lindelöf hypothesis (Backlund's equivalence): https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis
- Bourgain 2000 / Jutila 1977 ranges for DH, as summarized in arXiv:2306.05599 and arXiv:2403.13157: https://arxiv.org/pdf/2306.05599 , https://arxiv.org/pdf/2403.13157
- Bui, Conrey, Young, *More than 41% of the zeros of the zeta function are on the critical line*, arXiv:1002.4127 (Acta Arith. 150 (2011)): https://arxiv.org/pdf/1002.4127
- Pratt, Robles, Zaharescu, Zeindler, *More than five-twelfths of the zeros of ζ are on the critical line*, arXiv:1802.10521 (Res. Math. Sci. 7 (2020)): https://arxiv.org/abs/1802.10521
- Conrey, *More than two fifths of the zeros of the Riemann zeta function are on the critical line*, J. reine angew. Math. 399 (1989), 1–26; Levinson, Adv. Math. 13 (1974).
- Goldston, Suriajaya, *Zeta zeros on the critical line*, arXiv:2511.20059 (history of proportions; Montgomery 1973 under RH): https://arxiv.org/abs/2511.20059
- Baluyot, Goldston, Suriajaya, Turnage-Butterbaugh, *Pair correlation of zeros … I*, arXiv:2501.14545 (box hypothesis b = 0.3185): https://arxiv.org/abs/2501.14545
- Alpöge, Furman, *More than two thirds of the zeta zeros are simple and on the critical line*, arXiv:2608.13637; Lean companion anthropics/formal-math `zeta23/`: https://arxiv.org/abs/2608.13637 , https://github.com/anthropics/formal-math/tree/main/zeta23
- Platt, Trudgian, *The Riemann hypothesis is true up to 3·10^12*, arXiv:2004.09765 (Bull. LMS 2021): https://arxiv.org/abs/2004.09765
- Davenport, Heilbronn, *On the zeros of certain Dirichlet series*, J. London Math. Soc. 11 (1936); Bombieri, Ghosh, *Around the Davenport–Heilbronn function*, Russian Math. Surveys 66:2 (2011), 221–270; Righetti, *On the density of zeros of linear combinations of Euler products for σ > 1*, Algebra & Number Theory 11 (2017): https://arxiv.org/abs/1506.05716
- Littlewood, *On the zeros of the Riemann zeta-function*, Proc. Cambridge Philos. Soc. 22 (1924), 295–318, doi:10.1017/S0305004100014225; Selberg, *Contributions to the theory of the Riemann zeta-function*, Arch. Math. Naturvid. 48 (1946); Bohr–Landau 1914; Carlson 1920; Ingham 1940; Huxley 1972. Standard references: Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed.), Ch. IX (§9.9 Littlewood's lemma, §9.15 density theorems); Ivić, *The Riemann Zeta-Function*, Ch. 11.
- OpenAI 7/8 theorem: github.com/openai/math, commit `adc7f124…`, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (as pinned and receipted in `DEPOSIT_MAP.md` §8); refinements by Liu (arXiv:2610.12234) and the Quasi-Riemann Tracker, same section.

Local files read (absolute paths)
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/BL/BohrLandauClosure.lean`, `BohrLandauPartial.lean`, `DPMV.lean`, `DPMVexp.lean`, `JensenDisc.lean`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/MV.lean`, `Zeta23/MV/Final.lean`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/FromPNTPlus/ZetaBounds.lean`, `StrongPNTPrefix.lean`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/RvM/{Statement,Defs,NcountWindow,ZetaGrowth,Backlund,ReZeroCount,LocalCount,MainTerm}.lean`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/{Statement,Hypotheses,Unconditional,Final,Main,ZeroSide,PrimeSideA,Assembly,Superlinear,OffLine,Defs}.lean`, `Zeta23/WeilEF/Contour.lean`, `Challenge.lean`, `README.md`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/MNF/RH/{Core,Gap,Hypotheses,Reduction,Density,GapDensity}.lean`
- `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/.lake/packages/mathlib/Mathlib/NumberTheory/{ArithmeticFunction/Moebius,AbelSummation,Divisors,LSeries/ZetaZeros}.lean`, `Mathlib/Analysis/Complex/JensenFormula.lean`
- `/run/media/joeyxyxyz/Seagate Portable Drive/math/DEPOSIT_MAP.md`
- `/run/media/joeyxyxyz/Seagate Portable Drive/math/notes/density-field-2026-11-03/DENSITY_LEDGER.md`, `plan/BOHR_LANDAU_PLAN.md`, `plan/BOHR_LANDAU_PARTIAL.md`, `plan/BOHR_LANDAU_CLOSURE.md`, `plan/SCOPE_REPORTS_2026-11-03.md`
- `/run/media/joeyxyxyz/Seagate Portable Drive/math/notes/FRONTIER.md`, `GROK_PROPOSALS_2026-11-03.md`
