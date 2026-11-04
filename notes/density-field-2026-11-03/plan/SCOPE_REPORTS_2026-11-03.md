# Scoping reports (workflow agents, 2026-11-03)

## 1. zeta23 inventory

# zeta23 inventory for `meanSquare_strip` / `rightHalfBound_of_meanSquare`

Project: `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23`, `lean-toolchain` = `leanprover/lean4:v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`. Every name below was resolved by `#check` against the built oleans (`/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/agents/zeta23-inventory/Check2.lean`, compiles in ~4 s; output in `Check2.out` beside it). Three defeqs were checked by `example … := rfl`: `MNF.RH.is_nontrivial_zero = Zeta23.IsNontrivialZero`, `MNF.RH.zeta_order = Zeta23.zeroMult`, `MNF.RH.zerosIn T₁ T₂ = Zeta23.zerosIn T₁ T₂`.

**Build-state warning (important for the planner).** `lake env lean` on a new file can only import modules that already have an `.olean`. Built (usable): `Zeta23.BohrLandau`, `Zeta23.FromPNTPlus.ZetaBounds`, `Zeta23.FromPNTPlus.StrongPNTPrefix`, `Zeta23.FromPNTPlus.EulerMaclaurin`, `Zeta23.RvM.{ZetaGrowth,LocalCount,ReZeroCount,Backlund,CountByIntegral,MainTerm,Halving,NcountWindow,Fold}`, `Zeta23.WeilEF.{Landau,GoodHeights}`, `Zeta23.{MNFBridge,Superlinear,OffLine,ZetaReflect,MV,MV.Final}`, `Zeta23.Statement.{Seam,SeamClosed}`, `MNF.RH.*`. NOT built (no olean; importing them fails, and building would write under the forbidden tree): `Zeta23.WeilEF.Effective`, `Zeta23.XiPrime.ZeroCount.{Generic,ArgBound,Basic}`, `Zeta23.FromPNTPlus.MediumPNT`. I still quote the statements of the unbuilt ones because they are copy-able templates.

## 0. The target file, `Zeta23/BohrLandau.lean` (117 lines, imports `MNF.RH.GapDensity`, `Zeta23.Statement.SeamClosed`, `Mathlib.Analysis.Complex.JensenFormula`; `open Set Complex`; `namespace Zeta23.BL`, `open MNF.RH`)

```lean
-- :16-17
noncomputable def NRight (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ
noncomputable def NLeft (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ 1 / 2 - ρ.re}, zeta_order ρ
-- :20-21 (proved)
theorem NOff_eq_right_add_left {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    NOff δ 0 T = NRight δ T + NLeft δ T
-- :35 (proved, via zetaZeroConfig.reflect_mem / mult_reflect)
theorem NLeft_eq_NRight (δ T : ℝ) : NLeft δ T = NRight δ T
-- :53-54
def RightHalfBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T
-- :57 (proved)
theorem bohrLandau_of_right (h : RightHalfBound) : MNF.RH.BohrLandau
-- :66-67
def ZetaMeanSquare : Prop := ∀ σ : ℝ, 1 / 2 < σ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
  ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T
-- :69-70 (proved)
theorem norm_zeta_le_tsum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta (σ + t * I)‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ σ
-- :85-86 (proved; constant Z^2, Z = ∑' n, 1/n^σ, via intervalIntegral.norm_integral_le_of_norm_le_const)
theorem meanSquare_gt_one {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T
-- :98-100  SORRY 1a
theorem meanSquare_strip {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  sorry
-- :102-103
theorem zetaMeanSquare : ZetaMeanSquare := fun σ hσ =>
  if h : 1 < σ then meanSquare_gt_one h else meanSquare_strip hσ (not_lt.1 h)
-- :107-108  SORRY 2
theorem rightHalfBound_of_meanSquare (h : ZetaMeanSquare) : RightHalfBound := by
  sorry
-- :110-111
theorem bohrLandau : MNF.RH.BohrLandau :=
  bohrLandau_of_right (rightHalfBound_of_meanSquare zetaMeanSquare)
```
Downstream consumer `Zeta23/MNFBridge.lean:28-31`: `theorem on_line_density_one_of_gap_right (hR : Zeta23.BL.RightHalfBound) {Δ : ℝ} (hΔ : 0 < Δ) (hgap : MNF.RH.SpectralGapHyp Δ) : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (MNF.RH.Ncount 0 T : ℝ) ≤ MNF.RH.N0 0 T`; `MNFBridge.lean:9` `theorem Ncount_eq (T₁ T₂ : ℝ) : MNF.RH.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := rfl`.

MNF side (`MNF/RH/Core.lean:51,58`, `Counting.lean:52,57,96`, `GapDensity.lean:66,71,76,141`):
```lean
def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
noncomputable def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite   -- via IsCompact.inter_riemannZetaZeros_finite
noncomputable def NOff (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}, zeta_order ρ
def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T
def NcountSuperlinear : Prop := ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ T ≥ T₀, c * T ≤ (Ncount 0 T : ℝ)
theorem on_line_density_one_of_gap (hBL : BohrLandau) (hN : NcountSuperlinear) {Δ : ℝ}
    (hΔ : 0 < Δ) (hgap : SpectralGapHyp Δ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T
```
zeta23 side (`Zeta23/Statement.lean:38,43,46,49`): `def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`, `def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat`, `def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}`, `def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ`. `Zeta23/Defs.lean:108` `def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ`; `:120-130` `structure ZeroConfig` (fields `carrier : Set ℂ`, `mult : ℂ → ℕ`, `one_le_mult`, `strip`, `reflect_mem`, `mult_reflect`, `finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite`); `:137` `def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}`; `Z.N T₁ T₂ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ`. `Zeta23/Statement/SeamClosed.lean:26` `def zetaZeroConfig : ZeroConfig := zetaZeros zetaSeam` with `@[simp] zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl`, `zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl`, `zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂`, `:47` `theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite`. `Zeta23/RvM/Halving.lean:43-44` `theorem N_le_two_mul_half : (Z.N T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ)` (namespace `Zeta23.ZeroConfig`, explicit `(Z : ZeroConfig) (T₁ T₂ : ℝ)`). `Zeta23/ZetaReflect.lean:62` `theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) : riemannZeta (conj s) = conj (riemannZeta s)` (Mathlib also has the unconditional `riemannZeta_conj (s : ℂ)`, `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458`); `:224` `theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) : analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w`; `:278,314` `zeta_reflect_zero`, `zeta_mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ`. `Zeta23/RvM/NcountWindow.lean` (namespace `Zeta23`): `:20` `theorem zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : zerosIn a c = zerosIn a b ∪ zerosIn b c`, `:34` `theorem Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Ncount a c = Ncount a b + Ncount b c`, `:44` `theorem Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d`.

## 1. Usable lemmas, verbatim

### 1A. The approximate formula ζ = ζ₀ N — `Zeta23/FromPNTPlus/ZetaBounds.lean` (PNT+ port, NO namespace; `open Complex Topology Filter Interval Set Asymptotics`; local notation `ζ` = riemannZeta, `ζ'` = deriv riemannZeta, `ζ₀` = riemannZeta0 — the notations are LOCAL, write `riemannZeta`, `deriv riemannZeta`, `riemannZeta0` in a new file)

```lean
-- :520-523
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
-- :529-532
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
-- :1150-1151  (identity principle from Re s > 1, where ZetaSum_aux2 applies)
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s
-- :1180-1182
lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (ζ₀ N) s = ζ' s
-- :1039-1044
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
-- :1067-1068
lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s
-- :1084-1085
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re}
-- :949-951
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s
```
Finite-range Euler–Maclaurin pieces (the Dirichlet-polynomial tail `Σ_{a<n≤b} n^{-s}` as an integral — the building block for an approximate functional equation / "ζ = Σ_{n≤N} n^{-s} + N^{1−s}/(s−1) + O(N^{−σ})" with N depending on t):
```lean
-- :546-551  (first-order Euler–Maclaurin, a b real, sum over Finset.Ioc ⌊a⌋₊ ⌊b⌋₊)
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x
-- Zeta23/FromPNTPlus/EulerMaclaurin.lean:28,80-83 (B1 x := x - ⌊x⌋₊ - 1/2; 𝕜 any RCLike)
theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t
-- :614-618  (a b : ℕ)
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))
-- :572-574
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) = (b ^ (1 - s) - a ^ (1 - s)) / (1 - s)
-- :785-788  (tail of the Dirichlet series as the integral form, Re s > 1)
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))
-- :762-764
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s))
-- :774-776
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume
```
Bounds on the error terms:
```lean
-- :654
lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2
-- :642-644
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c
-- :663-665
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re
-- :713-715  (finite-interval error bound)
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re
-- :815-817  (the tail integral, uniformly in t; s written σ + t*I)
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ
-- :840-842
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ
-- :851-854
lemma ZetaBnd_aux1p (N : ℕ) (Npos : 1 ≤ N) {σ : ℝ} (hσ : σ ∈ Ioc 0 2) :
    (fun (t : ℝ) ↦
      ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖)
    =O[Filter.principal {t | 2 ≤ |t|}] fun t ↦ |t| * N ^ (-σ) / σ
-- :1214-1216  (term bound near σ = 1)
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A
-- :1290-1293 (Dirichlet polynomial with N = ⌊|t|⌋₊, σ ≥ 1 − A/log|t|)
lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t|
-- :1319-1320
lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2
-- :1336-1340 (the three N-terms at N = ⌊|t|⌋₊, σ ∈ Ioc (1/2) 2)
lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ)
-- :1361-1369
lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t|
-- :1448-1451
lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2
```
Note: there is NO lemma bounding `‖ζ(s) − Σ_{n≤N} n^{-s}‖` for general `N` (e.g. `N ≍ t`) as a stand-alone statement; it is assembled inline in `ZetaUpperBnd'` from `Zeta0EqZeta`, `ZetaBnd_aux1`, `UpperBnd_aux6`. For the mean square one needs it at `N = ⌊t⌋` or `N = ⌊t/2π⌋` with error `O(N^{-σ}) + O(t·N^{-σ}/σ)`: all ingredients are above (`ZetaBnd_aux1b` gives `‖∫_N^∞ …‖ ≤ N^{-σ}/σ`, so `‖s·∫‖ ≤ (σ+|t|)N^{-σ}/σ`; at `N = ⌊t⌋` that is `O(t^{1−σ})`, i.e. NOT small — the classical mean-square proof needs the sharper treatment of that term, see §2).

### 1B. Growth / upper bounds on ζ and ζ′
```lean
-- ZetaBounds.lean:1402-1404
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t|
-- :1799-1802
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2
-- :2186-2187  (horizontal FTC)
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I)
-- :2211-2214
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁)
-- :1873-1874  (pole bound on the real axis)
lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1)
-- :1853-1854 / :1866-1867
lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x)
lemma ZetaNear1BndFilter :
    (fun σ : ℝ ↦ ζ σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1))
-- :1089-1090
lemma HolomorphicOn_riemannZeta : HolomorphicOn ζ {s : ℂ | s ≠ 1}
-- :2547
lemma ZetaCont : ContinuousOn ζ (univ \ {1})
```
`Zeta23/RvM/ZetaGrowth.lean` (namespace `Zeta23.RvM`; `open Complex Set MeasureTheory Real`):
```lean
-- :43-44
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S
-- :56-57  (Zeta0EqZeta with N = 1 + ZetaBnd_aux1b)
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re
-- :78-79
theorem riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im|
-- :102-103
theorem zeta_growth {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im|
-- :109-111
theorem zeta_growth_quarter :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A
-- :119-120
theorem zeta_growth_right_at (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ)
-- :143-145
theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A
-- :151-152, :198-199, :216, :223, :227-228
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖
theorem riemannZeta_ne_zero_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : riemannZeta s ≠ 0
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6
```
(`Zeta23/WeilEF/Effective.lean:39-40`, UNBUILT: `theorem zeta_growth_quarter_explicit {s : ℂ} (h₁ : (1/4 : ℝ) ≤ s.re) (h₃ : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (13/2) * |s.im|` — trivially re-derivable from `riemannZeta_linear_growth (δ := 1/4)`.)

### 1C. Lower bounds / zero-free region / log-derivative (ZetaBounds.lean)
```lean
-- :1921-1922
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1
-- :1936-1937
lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1
-- :1944-1945
lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖ζ (σ + t * I)‖
-- :1977-1979
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖
-- :2059-2060
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖ζ (σ + t * I)‖ ≤ ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)
-- :2093-2095
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4)
-- :2250-2253
lemma ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) (1 + A / (Real.log |t|) ^ 9)),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ)
-- :2330-2335
lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖
-- :2457-2462
lemma ZetaZeroFree :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    ζ (σ + t * I) ≠ 0
-- :2483-2486 / :2993-2996
lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9
lemma LogDerivZetaBndUnif :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9
-- :2541
lemma ZetaNoZerosOn1Line (t : ℝ) : ζ (1 + t * I) ≠ 0
-- :2554-2556  (compactness; σ depends on T)
lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0
-- :2662-2664, :2709-2712
lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S) (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S
theorem LogDerivZetaHolcLargeT :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 9) 2)  ×ℂ (Icc (-T) T) ) \ {1})
-- :2763-2765, :2811-2812
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖
theorem triv_bound_zeta :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C
```
Mathlib facts used by these (names verified): `riemannZeta_ne_zero_of_one_le_re : ∀ ⦃s : ℂ⦄, 1 ≤ s.re → riemannZeta s ≠ 0`, `riemannZeta_ne_zero_of_one_lt_re {s} : 1 < s.re → …`, `differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s`, `zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s`, `zeta_eq_tsum_one_div_nat_add_one_cpow`, `Complex.summable_one_div_nat_cpow {p : ℂ} : (Summable fun n => 1 / ↑n ^ p) ↔ 1 < p.re`, `Real.summable_one_div_nat_rpow {p : ℝ} : (Summable fun n => 1 / ↑n ^ p) ↔ 1 < p`, `Complex.norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re)`, `Complex.norm_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : ‖(x : ℂ) ^ y‖ = x ^ y.re`, `riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) : riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s` (functional equation, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`), `riemannZeta_eq_inv_sub_add {s} (hs : s ≠ 1) : riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s` (`ZetaAsymp.lean:544`, `riemannZeta₀` entire), `isBigO_riemannZeta_sub_one_div : (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) =O[𝓝 1] (fun _ ↦ 1)`, `IsCompact.inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) : (S ∩ riemannZetaZeros).Finite` (`riemannZetaZeros := riemannZeta ⁻¹' {0}`), `integral_cpow {a b : ℝ} {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) : (∫ x : ℝ in a..b, (x : ℂ) ^ r) = ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) / (r + 1)`, `intervalIntegral.norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) : ‖∫ x in a..b, f x‖ ≤ C * |b - a|`.

### 1D. Zero counting in discs — HOW the local count is proved

The Jensen-type engine actually used everywhere in zeta23 is the PNT+ port `ZerosBound`, NOT Mathlib's `JensenFormula.lean` (which is imported only by `BohrLandau.lean` and used nowhere — `grep circleAverage Zeta23` is empty). `Zeta23/FromPNTPlus/StrongPNTPrefix.lean` (no namespace):
```lean
-- :194
def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}
-- :196-199
lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ} (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) : (SetOfZeros r f).Finite
-- :453-458  (Blaschke-product / Jensen inequality on the unit disc, f(0)=1)
theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B
```
(`analyticOrderNatAt` is Mathlib's: `Mathlib/Analysis/Analytic/Order.lean:61`, `(analyticOrderAt f z₀).toNat`; the sum's cast to ℝ is `↑(∑ …) ≤ …`.) Also `theorem borelCaratheodory'` (:51), `BorelCaratheodoryDeriv` (:108), `LogOfAnalyticFunction` (:124), `DiskBound` (:377) in that file.

`Zeta23/RvM/LocalCount.lean` (namespace `Zeta23.RvM`; `open Complex Set Filter Topology Metric`):
```lean
-- :38-39
theorem riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite
-- :48
def gfun (s₀ c u : ℂ) (z : ℂ) : ℂ := riemannZeta (s₀ + c * z) * u
-- :63-64  (order transport under the affine rescaling)
lemma analyticOrderNatAt_gfun {s₀ c u w : ℂ} (hc : c ≠ 0) (hu : u ≠ 0) (h : s₀ + c * w ≠ 1) :
    analyticOrderNatAt (gfun s₀ c u) w = zeroMult (s₀ + c * w)
-- :93
def NhalfR (t : ℝ) : ℝ := ∑ᶠ ρ ∈ zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (zeroMult ρ : ℝ)
-- :96-97
theorem half_count_large :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3)
-- :255
theorem count_small (t : ℝ) (ht : |t| ≤ 4) : (Ncount t (t + 1) : ℝ) ≤ Ncount (-4) 5
-- :266-267
theorem zeta_local_zero_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
-- :294-295
theorem zetaZeroConfig_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
```
Proof route of `half_count_large` (:96-252), reusable as a template for "zeros with Re ≥ 1/2 + δ in a box ≤ (1/log(R/r))·log(sup/|f(centre)|)": centre `c₀ := 2 + (t+1/2)·I`, `κ := 19/10`, `u := (ζ c₀)⁻¹` (`‖u‖ ≤ 3` from `zeta_lower_bound_two`), `g := gfun c₀ κ u` so `g 0 = 1`; `hfAnalytic` from `riemannZeta_analyticOnNhd_compl_one` (`Zeta23/Statement/Seam.lean:30`, `AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ)`) since `|t+1/2| ≥ 3.5 > 1.9`; `hfin` from `riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ 1.9)` pulled back by `ρ ↦ (ρ − c₀)/κ`; `fz_bound` with `B := 3·C·(|t|+6)^A'` from `zeta_growth_right` (needs `0.15 ≤ Re`, `‖s−1‖ ≥ 1`); `ZerosBound (r := 0.84) (R := 0.95)`; then the window's `Re ≥ 1/2` part injects into the zero finset of `g` (`‖φ ρ‖ ≤ 0.84` because `(ρ.re−2)² + (ρ.im−t−1/2)² ≤ 1.5² + 0.5² ≤ (0.84·1.9)²`), multiplicities match via `analyticOrderNatAt_gfun`, and `finsum_mem_eq_finite_toFinset_sum` + `Finset.sum_le_sum_of_subset_of_nonneg`. Then `zeta_local_zero_count` = `zetaZeroConfig.N_le_two_mul_half` (reflection halving) + `count_small`. Convention: windows are `(t, t+1]` (`T₁ < Im ρ ≤ T₂`), multiplicity = `zeroMult`, counts cast to ℝ.

The same engine in `Zeta23/RvM/ReZeroCount.lean` (namespace `Zeta23.RvM`), useful because it is parametric in the growth data:
```lean
-- :27-29
lemma finite_zeros_closedBall {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball 0 R)
    (hfz₀ : f z₀ ≠ 0) : {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite
-- :53
def symZeta (T : ℝ) (z : ℂ) : ℂ := (riemannZeta (z + T * I) + riemannZeta (z - T * I)) / 2
-- :101-105  (reZeroSet T := {σ ∈ Icc (1/2) 2 | (ζ(σ+iT)).re = 0}, BacklundDefs.lean:24)
theorem reZeroSet_card_le_of_growth {A C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A) :
    ∀ T : ℝ, 4 ≤ T → (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ)
      ≤ (1 / Real.log ((0.9 : ℝ) / 0.8) * (|Real.log (6 * C)| + 2 * max A 0)) * Real.log T
-- :351-352
theorem reZeroSet_card_le : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T
```
Landau partial fractions, `Zeta23/WeilEF/Landau.lean` (namespace `Zeta23.WeilEF`, BUILT):
```lean
-- :299-306
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25:ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 44795000 * Real.log B
-- :315-317
lemma finite_SetOfZeros {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 ≠ 0) :
    (SetOfZeros 1 f).Finite
-- :348-356  (general disc; the zero finset Z and Σ m_ρ ≤ (1/log((24/25)/(22/25)))·log B is a Jensen count)
theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B
-- :512-519
theorem zeta_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3)
```
Unbuilt but copy-able templates: `Zeta23/WeilEF/Effective.lean:57-63` `zeta_logDeriv_partial_fraction_explicit` (same with constant `135000000`), `:437-438` `theorem zeta_local_count_explicit_large (t : ℝ) (hc : 6 ≤ |t + 1/2|) : (Zeta23.Ncount t (t + 1) : ℝ) ≤ 540000000 * Real.log (|t| + 3)`, `:765-766` `theorem zeta_local_count_box (t : ℝ) (hc : |t + 1/2| < 6) : (Zeta23.Ncount t (t + 1) : ℝ) ≤ 144` (Jensen for `xi s := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1/2`, `:521`), `:926-927` `theorem zeta_local_zero_count_explicit (t : ℝ) : (Zeta23.Ncount t (t + 1) : ℝ) ≤ 540000000 * Real.log (|t| + 3)`. `Zeta23/XiPrime/ZeroCount/Generic.lean:41-53` `theorem logDeriv_partial_fraction_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ} (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50))) (hCf : 0 < Cf) (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k) (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖) : ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ t₀ ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ |t| → f (2 + t * I) ≠ 0 ∧ ∃ Z : Finset ℂ, (↑Z = {ρ ∈ closedBall (2 + t * I) (22 / 25 * (91 / 50)) | f ρ = 0}) ∧ ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧ ∀ s ∈ closedBall (2 + t * I) (3 / 2), f s ≠ 0 → ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ C * Real.log (|t| + 3)` and `:329-337` `local_count_two_line … (Zc : ZeroConfig) (hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → f ρ = 0 ∧ analyticOrderNatAt f ρ = Zc.mult ρ) : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Zc.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)` — a generic "growth on a disc + lower bound at centre ⇒ local count" theorem for arbitrary f (e.g. a mollified `ζ·M`), but its module is unbuilt.

### 1E. Mathlib Jensen material (verified names; all in this checkout)
`Mathlib/Analysis/Complex/JensenFormula.lean` (lemmas live in root namespace; the file `open`s `Real`, so write `Real.circleAverage`):
```lean
-- :308-312
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖
-- :376-380
theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|)) (h₂f : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖
-- :390-394
theorem AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u ≤ Real.log (M / ‖f c‖) / Real.log (R / r)
```
`divisor` = `MeromorphicOn.divisor f U : Function.locallyFinsuppWithin U ℤ`; `MeromorphicOn.AnalyticOnNhd.divisor_apply (hf : AnalyticOnNhd 𝕜 f U) (hz : z ∈ U) : (MeromorphicOn.divisor f U) z = (ENat.map Nat.cast (analyticOrderAt f z)).untop₀`; `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`. `Mathlib/MeasureTheory/Integral/CircleAverage.lean` (namespace `Real`): `Real.circleAverage_def : circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)`, `Real.circleAverage_mono (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) (h : ∀ x ∈ Metric.sphere c |R|, f₁ x ≤ f₂ x) : circleAverage f₁ c R ≤ circleAverage f₂ c R`, `Real.circleAverage_nonneg_of_nonneg`, `circleAverage_const`, `circleAverage_add/sub/sum/smul`, `circleAverage_eq_intervalAverage`, `ContinuousOn.circleAverage`. `Mathlib/Analysis/Convex/Integral.lean`: `ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ)`, `ConcaveOn.le_map_integral [IsProbabilityMeasure μ] … : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ)` (and the `ConvexOn.map_average_le`, `ConvexOn.map_integral_le` duals). `Mathlib/Analysis/Complex/ValueDistribution/{CharacteristicFunction,FirstMainTheorem,Cartan,LogCounting/*,Proximity/*}.lean` exist (Nevanlinna `characteristic`, `logCounting`, `proximity`), unused by zeta23.

### 1F. Counting zeros in rectangles (argument principle, RvM), all BUILT
`Zeta23/FromPNTPlus/ResidueCalcOnRectangles.lean:31-56`: `HIntegral f x₁ x₂ y := ∫ x in x₁..x₂, f (x + y * I)`, `VIntegral f x y₁ y₂ := I • ∫ y in y₁..y₂, f (x + y * I)`, `RectangleIntegral f z w := HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im + VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im`, `abbrev RectangleIntegral' f z w := (1 / (2 * π * I)) • RectangleIntegral f z w`; also `ResidueTheoremOnRectangleWithSimplePole` (:525), `HolomorphicOn.vanishesOnRectangle` (:117), `RectangleIntegralHSplit/VSplit` (:203,:254). `Zeta23/RvM/CountByIntegral.lean:98-102` (namespace `Zeta23.RvM`):
```lean
theorem rectangleIntegral'_logDeriv_completedZeta_eq_Ncount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ)
```
`Zeta23/RvM/Defs.lean:31,35-37`: `def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.im ≠ T`; `def halfContour (F : ℂ → ℂ) (T₁ T₂ : ℝ) : ℂ := (∫ σ in (1/2:ℝ)..2, F (σ + T₁ * I)) + (∫ t in T₁..T₂, F (2 + t * I)) * I - ∫ σ in (1/2:ℝ)..2, F (σ + T₂ * I)`. `Zeta23/RvM/MainTerm.lean:196` `theorem exists_goodHeight (a : ℝ) : ∃ T ∈ Set.Icc a (a + 1), GoodHeight T`; `:482-484` `theorem rvM_main (hΓ : GammaFacts) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T` (`ell1 T := l T + 2 * Real.log 2 - 1`, `Defs.lean:52`; `GammaFacts` is discharged elsewhere: `gammaFacts : GammaFacts` in `Zeta23/GammaFacts/Complete.lean`). `Zeta23/RvM/Backlund.lean:266-270` `theorem im_integral_logDeriv_le (hT : T ≠ 0) (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) (hfin : (reZeroSet T).Finite) : |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi * ((reZeroSet T).ncard + 1)`; `:330-332` `theorem backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) → |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T`; `:400-401` `theorem vertical_two : ∀ T₁ T₂ : ℝ, |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi`; `:348` `lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re`. `Zeta23/Superlinear.lean:49` `theorem ncountSuperlinear : NcountSuperlinear` (proved), `:62-63` `theorem tendsto_Ncount_div_atTop : Tendsto (fun T => (Ncount 0 T : ℝ) / T) atTop atTop`. `Zeta23/OffLine.lean:38-39` `theorem offLine_le_one_third : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NoffMult 0 T : ℝ) ≤ (1 / 3 + ε) * Ncount 0 T` with `NoffMult T₁ T₂ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}, zeroMult ρ` (:11) — a weaker-than-Bohr–Landau off-line bound already proved (depends on the big [thm:B] pipeline). Unbuilt: `Zeta23/XiPrime/ZeroCount/ArgBound.lean:33,73,95,129` (`abs_im_integral_logDeriv_le_pi`, `…_vertical_le_pi`, `…_horizontal_le_pi`, `abs_im_integral_inv_sub_le_pi : |Im ∫_a^b dσ/(σ+iT−ρ)| ≤ π`) — Mathlib-only, copy-able.

### 1G. Montgomery–Vaughan (the only "mean value" tool present), BUILT
`Zeta23/MV.lean:52-56` (namespace `Zeta23`):
```lean
def MVDiag (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * ∑ r, ‖x r‖ ^ 2 / δ r
```
`Zeta23/Hypotheses.lean:109-113` `def MVHilbert (C : ℝ) : Prop := … ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)` (bilinear form). `Zeta23/MV/Final.lean:27` `theorem mvDiag_thirteen : MVDiag 13`, `:30` `theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C` — both PROVED outright. This is exactly the Hilbert inequality from which the Montgomery–Vaughan mean value theorem `∫_0^T |Σ a_n n^{-it}|² dt = Σ|a_n|²(T + O(n))` follows (frequencies `log n`, gaps `δ_n ≍ 1/n`), but that derivation is NOT in the tree (see §2). The closest thing is `Zeta23/XiPrime/PrimeSide/PP.lean:456-466` `prop_PP_c (hMV : Zeta23.MVHilbert C) … : |Mform F.Phi p.T (Pc p.X c) (Pc p.X c) - p.T / π * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n * F.g (Real.log n)| ≤ …` where `Mform Φ T u₁ u₂ := ∫ q in (Icc T (2T)) ×ˢ (Icc T (2T)), (Φ (q.1 - q.2)) ^ 2 * u₁ q.1 * u₂ q.2` (`PrimeSideA/Defs.lean:150`) and `Pc X c τ := (1/π) Σ_{N ∈ Ioc 0 ⌊X⌋₊} (Re c_N cos(τ log N) + Im c_N sin(τ log N))/√N` (`XiPrime/Defs.lean:101`) — a smoothed, real-part, 1/√N-weighted Dirichlet polynomial second moment tied to the paper's window machinery (`LocalHypsCore`, `Setting`, `LocalFun`); not directly a `∫_0^T |Σ a_n n^{-σ-it}|²`, and `Zeta23.XiPrime.*` modules are unbuilt.

## 2. What is ABSENT (checked by grep over all 320 files in `Zeta23/` and Mathlib `NumberTheory/`)
- **Mean square of ζ** (`∫_0^T |ζ(σ+it)|² dt`, any σ ≤ 1): NOT found. Only `Zeta23.BL.meanSquare_gt_one` (σ > 1, trivial sup bound) and the sorried `meanSquare_strip`. The only ζ-integrals over t in the tree are `Zeta_eq_int_derivZeta` (horizontal FTC), `vertical_two`/`im_integral_logDeriv_le`/`backlund_horizontal` (arguments of ζ′/ζ), `Fold.lean:147` (conjugation of `∫ logDeriv completedRiemannZeta (2 + t*I)`), and `WeilEF/FullLine.lean:322` `Fline` (`Hfn·logDeriv completedRiemannZeta` on `Re = c`).
- **Dirichlet-polynomial mean value theorem** (`∫_0^T |Σ_{n≤N} a_n n^{-it}|² dt ≤ (T + O(N)) Σ|a_n|²`, or the `Σ |a_n|² (T + O(n))` form): NOT found. The Hilbert inequality `MVDiag 13` / `MVHilbert` (§1G) is proved and is the standard input; the `∫_0^T` derivation (expand the square, diagonal `T Σ|a_n|²`, off-diagonal `Σ_{m≠n} a_m ā_n (e^{iT log(n/m)}−1)/(i log(n/m))`, apply MV with `freq = log n`, `δ_n = log(1+1/n) ≥ 1/(2n)`) must be written. The string "Dirichlet polynomial" appears only in XiPrime prime-side files (`Pc`, `prop_PP_c`, `frobSq_Ppart_le`) with the paper's smoothing; "partial sum" hits are Chebyshev/Abel-summation lemmas (`Zeta23/Chebyshev.lean:513,516,674,884`), not Dirichlet polynomials in t.
- **Littlewood's lemma** (`∫_{σ₀}^{2} … = 2π Σ_ρ (Re ρ − σ₀)`, or `∫_0^T log|ζ(σ₀+it)| dt` vs zero count): NOT found ("Littlewood" occurs only in `XiPrime/{Statement,Defs,StatementW,Final}.lean` referring to Littlewood's gap theorem as a named Prop). No lemma relates `∫ log|f|` on a vertical segment/rectangle to zeros. Mathlib has only the disc version (`circleAverage_log_norm`, `sum_divisor_le`, §1E).
- **Jensen/concavity-of-log on a line** (`∫ log|ζ| ≤ T log( (1/T)∫|ζ|² )/2`): NOT found in zeta23; Mathlib's `ConcaveOn.le_map_average`/`le_map_integral` (§1E) provide the abstract inequality (need `ConcaveOn ℝ (Ioi 0) Real.log` = `Real.strictConcaveOn_log_Ioi.concaveOn`, and integrability).
- **First-derivative test / van der Corput / exponential-sum lemmas**: NOT found anywhere (grep `van der Corput`, `first derivative`, `vdC`: no hits; `Zeta23/Poisson*` is Poisson summation for the explicit formula).
- **Approximate functional equation** (`ζ(s) = Σ_{n≤x} n^{-s} + χ(s) Σ_{n≤y} n^{s−1} + O(…)`): NOT found. Only the one-sided Euler–Maclaurin `riemannZeta0`/`Zeta0EqZeta` (§1A), valid for every `N ≥ 1`, `Re s > 0`, with the tail `s∫_N^∞(⌊x⌋+1/2−x)x^{−s−1}` bounded by `(σ+|t|)N^{−σ}/σ` (`ZetaBnd_aux1b`) — i.e. `ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + O(|t| N^{−σ}/σ)`, the Titchmarsh (2.1.4)/Thm 4.11-type formula with the crude error (no `O(N^{−σ})` sharpening via the second Euler–Maclaurin step; no `ζ₀'`-free `∫ (x−⌊x⌋−1/2)` second integration by parts). The functional equation itself is Mathlib `riemannZeta_one_sub` (Γ, cos, (2π)^{-s}), with `Zeta23/RvM/{CountByIntegral,Fold}.lean` and `GammaFacts/StirlingVert.lean` (`digamma_stirling`) holding Stirling-type material for `Γℝ`, not `|χ(s)|` asymptotics.
- **Mathlib**: no mean-value, large-sieve, Hilbert-inequality, Littlewood, van der Corput or approximate-functional-equation material (`grep -rli` over `Mathlib/NumberTheory` returns only unrelated Hilbert-theory files); `Mathlib/NumberTheory/LSeries/` = {AbstractFuncEq, Basic, Convergence, Convolution, Deriv, Dirichlet, DirichletContinuation, HurwitzZeta*, Injectivity, Linearity, MellinEqDirichlet, Nonvanishing, Positivity, PrimesInAP, RiemannZeta, SumCoeff, ZMod, ZetaZeros}.

## 3. Conventions a new file must follow
- **Point on a vertical line**: everywhere `(σ : ℝ) (t : ℝ)` with the point written `↑σ + ↑t * Complex.I` (`σ + t * I` under `open Complex`); the target statements use exactly `riemannZeta (σ + t * I)`. `ZetaGrowth.lean`/`LocalCount.lean` instead quantify over `s : ℂ` with hypotheses on `s.re`, `s.im`, `‖s - 1‖` — to apply them at `σ + t*I` use `by simp` to rewrite `(↑σ + ↑t * I).re = σ`, `.im = t`. Disc centres are `2 + t * I` (or `2 + (t + 1/2 : ℝ) * I`). PNT+ lower bounds sometimes write `σ + 2 * t * I` or `1 + x + I * y` (order of factors matters for `rw`).
- **Height restrictions**: PNT+ (`ZetaBounds.lean`) bounds need `3 < |t|` and `σ ∈ Icc (1 - A / Real.log |t|) 2` (closed), with `A ∈ Ioc 0 (1/2)` existential; `ZetaBnd_aux1` needs `σ ∈ Ioc 0 2`, `2 ≤ |t|`; `ZetaNear1BndExact` needs `σ ∈ Ioc 1 2`; `ZetaInvBnd`/`ZetaLowerBnd`/`LogDerivZetaBnd` use `Ico` windows around 1, `LogDerivZetaBndUnif` uses `Ici`. zeta23's own growth lemmas need only `1 ≤ |s.im|` (`riemannZeta_linear_growth`, `δ ≤ s.re`) or `1 ≤ ‖s − 1‖` (`zeta_growth_right`, `0.15 ≤ s.re`); the local count is for all `t`. The mean-square target has `2 ≤ T` and the integral from `0`, so the region `|t| ≤ 3` must be handled separately (continuity/compactness: `ZetaCont`, or `norm_riemannZeta_le_of_re_pos` which needs only `0 < Re s`, `s ≠ 1` and gives `‖ζ(σ+it)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖/σ`, fine for `σ > 1/2`, `t ≠ 0`… but blows up only at `s = 1`, which is not on the line for σ ≤ 1 unless σ = 1, t = 0 — NOTE `σ = 1` is allowed by `meanSquare_strip` (`h2 : σ ≤ 1`), and `ζ(1 + 0·I)` is the pole; the integrand is still locally integrable (`|ζ|² ~ 1/t²` is NOT integrable at t = 0!). So at σ = 1 the statement `∫ t in 0..T, ‖ζ(1 + t I)‖^2 ≤ C T` is about a non-integrable function; Mathlib's Bochner integral of a non-integrable function is `0`, so it holds vacuously via `intervalIntegral.integral_undef`/`MeasureTheory.integral_undef` — the planner must decide to exploit this (prove non-integrability at σ = 1) or handle σ = 1 by the σ > 1/2 argument only on `[1, T]` plus the junk value; cleanest is to split `σ = 1` off and use `integral_undef`.)
- **Norms and powers**: real norm `‖·‖` on ℂ (`Complex.norm_eq_abs` is not used; lemmas are stated with `‖ ‖`), `‖riemannZeta (…)‖ ^ 2` is the ℕ-power of a real; `rpow` appears as `(n : ℝ) ^ σ` with `σ : ℝ`; cpow norms via `Complex.norm_natCast_cpow_of_pos`/`norm_cpow_eq_rpow_re_of_pos`. Sums over naturals use `Finset.range (N + 1)` (includes `n = 0`, whose term `1 / (0:ℂ)^s = 0` for `s ≠ 0` by `Complex.zero_cpow`) in `riemannZeta0`, but `Finset.Ioc a b` in `ZetaSum_aux1`/`sum_eq_int_deriv` and `Finset.Ioc 0 ⌊X⌋₊` in XiPrime; `Finset.Ioc_eq_Ico`, `Finset.Ioc_eq_Icc`, `Finset.Icc_eq_Ico` (`ZetaBounds.lean:723-729`) convert. Floor: `⌊x⌋` (ℤ) inside the Euler–Maclaurin integrands, `⌊|t|⌋₊` (ℕ) for `N`; `Int.natCast_floor_eq_floor` bridges.
- **Integrals**: interval integrals `∫ t in a..b, …` (`intervalIntegral`, membership hypotheses on `Ι a b = Set.uIoc a b`, so `norm_integral_le_of_norm_le_const` needs `∀ x ∈ Ι 0 T`, i.e. `x ∈ Ioc 0 T` after `uIoc_of_le`); set integrals `∫ x in Ioi (N : ℝ), …` for the tail; `MeasureTheory.IntegrableOn … volume`. `[[a, b]]` is `Set.uIcc` (notation from `open Interval`).
- **Constants**: PNT+ style `∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ …`; zeta23 style `∃ C : ℝ, 0 < C ∧ ∀ …` or `∃ C T₀ : ℝ, ∀ T, T₀ ≤ T → …`; the targets want a bare `∃ C : ℝ` (no positivity) and `2 ≤ T`.
- **Zero sets / multiplicity**: `IsNontrivialZero ρ` (strip `0 < Re < 1`), multiplicity `zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat = analyticOrderNatAt riemannZeta ρ` (defeq to `MNF.RH.zeta_order`); the disc engines use `SetOfZeros`, `finiteSetOfZeros_mono`, `analyticOrderNatAt`, `Finset` sums; the window counts use `∑ᶠ ρ ∈ S, …` over `zerosIn T₁ T₂` (`T₁ < Im ρ ≤ T₂`, positive-ordinate windows, not `|Im|`), converted to `Finset` sums by `finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite T₁ T₂)`; finiteness of zeros in compacts: `riemannZeta_zeros_finite_of_isCompact` (zeta23) or `IsCompact.inter_riemannZetaZeros_finite` (Mathlib); analyticity: `riemannZeta_analyticOnNhd_compl_one`, `Zeta23.RvM.analyticOnNhd_riemannZeta (hS : 1 ∉ S)`; `analyticOrderAt_riemannZeta_ne_top (hs : s ≠ 1)`. `NRight δ T` in the target is `∑ᶠ ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ` — note `δ ≤ Re ρ − 1/2` (closed), window `(0, T]`.
- **Imports/opens**: `import Zeta23.BohrLandau` alone brings `MNF.RH.*`, `Zeta23.Statement.SeamClosed` (zero configs) and Mathlib Jensen; add `import Zeta23.FromPNTPlus.ZetaBounds`, `Zeta23.RvM.ZetaGrowth`, `Zeta23.RvM.LocalCount`, `Zeta23.WeilEF.Landau`, `Zeta23.MV.Final`, `Zeta23.RvM.Backlund` as needed (all built; 4 s load). Do not rely on the local notations `ζ`, `ζ'`, `ζ₀` from ZetaBounds (they are `local notation`). `ZetaBounds.lean` sets `set_option lang.lemmaCmd true`; a new file using `lemma` needs the same option or `import Batteries.Tactic.Lemma`.

## 2. Mathlib inventory

All names are now verified against this checkout (one `#check` per name compiled with `lake env lean`; the only failures were namespace spellings, corrected below). Inventory follows.

# Mathlib inventory — zeta23 checkout (Mathlib 51e6992e)

Mathlib root `M` = `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/.lake/packages/mathlib/Mathlib`. All names below resolve under `import Mathlib` at this checkout (verification files: `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/agents/mathlib-inventory/Check.lean` and `.../Check2.lean`; 230 `#check`s, all pass with the names as written here).

## (a) Jensen's formula / inequality, divisor API, order API

### `M/Analysis/Complex/JensenFormula.lean` — every theorem (all root-level; `circleAverage` means `Real.circleAverage`, `divisor` means `MeromorphicOn.divisor`)

- line 160 (auxiliary, center 0):
```lean
theorem circleAverage_re_herglotzRieszKernel_mul_log₀ {w ρ : ℂ} {R : ℝ} (hρ : ρ ∈ sphere 0 R)
    (hw : w ∈ ball 0 R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (log ‖· - ρ‖)) (0 : ℂ) R
      = log ‖w - ρ‖
```
- line 209:
```lean
theorem circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : ℂ} {R : ℝ} (hρ : ρ ∈ sphere c R)
    (hw : w ∈ ball c R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖
```
- line 232 (`@[simp]`):
```lean
lemma circleAverage_log_norm_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R
```
- line 265 (`@[simp]`):
```lean
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|)) (h₂g : ∀ u ∈ closedBall c |R|, g u ≠ 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖
```
- line 276:
```lean
lemma countingFunction_finsum_eq_finsum_add {c : ℂ} {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0)
    (hD : D.HasFiniteSupport) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R
```
- line 308 — **Jensen's Formula** (meromorphic):
```lean
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖
```
- line 376 — **Jensen's Formula** (analytic, `f c ≠ 0`):
```lean
theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖
```
- line 390 — **Jensen's Inequality** (zero count in the smaller ball):
```lean
theorem AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u ≤ Real.log (M / ‖f c‖) / Real.log (R / r)
```
(The LHS sum is over `ℤ`-valued divisor, coerced to `ℝ`; the bound is on the number of zeros in `closedBall c |r|` with multiplicity.)

Reformulation via the logarithmic counting function, `M/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean`:
- line 580:
```lean
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (hR : R ≠ 0) :
    logCounting (divisor f univ) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖
```
- line 596: `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const` (same RHS, LHS `(logCounting f 0 - logCounting f ⊤) R`).
- line 99 (namespace `Function.locallyFinsuppWithin`): `noncomputable def logCounting ... : locallyFinsupp E ℤ →+ (ℝ → ℝ)` with `toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r`.
- line 72: `lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} (h : Meromorphic f) : (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ)`.

### Divisor API — `M/Analysis/Meromorphic/Divisor.lean` (`namespace MeromorphicOn`; variables `{𝕜} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜} {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`)

- line 39:
```lean
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ where
  toFun := fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0
```
- line 59: `theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) : divisor f U z = if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0`
- line 68 (`@[simp]`): `lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) : divisor f U z = (meromorphicOrderAt f z).untop₀`
- line 71 (full name `MeromorphicOn.AnalyticOnNhd.divisor_apply`, verified):
```lean
lemma AnalyticOnNhd.divisor_apply {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) (hz : z ∈ U) :
    divisor f U z = ((analyticOrderAt f z).map (↑)).untop₀
```
- line 83: `lemma _root_.divisor_sphere_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜} : (divisor f (Metric.sphere c R)).support.Finite`
- line 91: `lemma divisor_support_finite_of_subset {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hU : IsCompact U) (hV : V ⊆ U) : (divisor f V).support.Finite`
- line 104: `lemma divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜} (hf : MeromorphicOn f (Metric.closedBall c R)) : (divisor f (Metric.ball c R)).support.Finite`
- line 177 (full name `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`): `theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) : 0 ≤ MeromorphicOn.divisor f U`
- line 188: `theorem divisor_const (e : E) : divisor (fun _ ↦ e) U = 0`
- line 310: `theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ u : U, meromorphicOrderAt f₁ u ≠ ⊤) (h₂f₂ : ...) : divisor (f₁ * f₂) U = divisor f₁ U + divisor f₂ U` (hypotheses abbreviated; also `divisor_fun_mul`, `divisor_prod`, `divisor_inv`, `divisor_pow`, `divisor_zpow` lines 319–404)
- line 411: `theorem divisor_restrict {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V ⊆ U) : (divisor f U).restrict hV = divisor f V`
- line 450: `lemma divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x ≠ z₀) : divisor (· - z₀) U x = 0`
- line 461: `lemma divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h : z₀ ∈ U) : divisor (· - z₀) U z₀ = 1`

### locallyFinsuppWithin — `M/Topology/LocallyFinsupp.lean` (namespace `Function.locallyFinsuppWithin`)
- line 48: `structure Function.locallyFinsuppWithin [Zero Y] where toFun : X → Y; supportWithinDomain' : toFun.support ⊆ U; supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)`
- line 140: `lemma supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) : D.support ⊆ U`
- line 196 (`@[simp]`): `lemma apply_eq_zero_of_notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y) (hz : z ∉ U) : D z = 0`
- line 253:
```lean
theorem finiteSupport [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsCompact U) :
    Set.Finite D.support
```

### Order API — `M/Analysis/Analytic/Order.lean` (root-level)
- line 47: `noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞` (⊤ iff locally zero; junk `0` if not analytic)
- line 61: `noncomputable def analyticOrderNatAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ := (analyticOrderAt f z₀).toNat`
- line 71 (`@[simp]`): `lemma Nat.cast_analyticOrderNatAt (hf : analyticOrderAt f z₀ ≠ ⊤) : analyticOrderNatAt f z₀ = analyticOrderAt f z₀`
- line 75: `lemma analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0`
- line 86: `lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = n ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z`
- line 101: `lemma AnalyticAt.analyticOrderNatAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ ≠ ⊤) {n : ℕ} : analyticOrderNatAt f z₀ = n ↔ ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z`
- line 113: `lemma AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ ≠ ⊤ ↔ ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ analyticOrderNatAt f z₀ • g z`
- line 120: `lemma analyticOrderAt_eq_zero : analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ ≠ 0`
- line 133: `protected lemma AnalyticAt.analyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0`
- `M/Analysis/Meromorphic/Order.lean:283`: `lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) : meromorphicOrderAt f x = (analyticOrderAt f x).map (↑)`; line 295: `theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) : 0 ≤ meromorphicOrderAt f x`

### Link `divisor f (closedBall …) z` → `analyticOrderNatAt`: **no single lemma found**; it is a 3-step composition, all verified:
1. `MeromorphicOn.AnalyticOnNhd.divisor_apply` gives `divisor f U z = ((analyticOrderAt f z).map (↑)).untop₀`;
2. `M/Data/ENat/Basic.lean:576` `theorem map_natCast (f : ℕ → α) (a : ℕ) : map f a = f a` (`ENat.map_natCast`) and `:573` `theorem map_top (f : ℕ → α) : map f ⊤ = ⊤`;
3. `M/Algebra/Order/WithTop/Untop0.lean:72` `lemma untop₀_natCast [AddMonoidWithOne α] (n : ℕ) : untop₀ (n : WithTop α) = n` (`WithTop.untop₀_natCast`), `:47` `lemma untop₀_coe (a : α) : (a : WithTop α).untop₀ = a`, `:41` `lemma untop₀_top : untop₀ ⊤ = (0 : α)`, `:49` `lemma coe_untop₀_of_ne_top {a : WithTop α} (ha : a ≠ ⊤) : a.untop₀ = a`.
So for `f` analytic on `U`, `z ∈ U`, `analyticOrderAt f z ≠ ⊤`: `divisor f U z = (analyticOrderNatAt f z : ℤ)` after `Nat.cast_analyticOrderNatAt`. MNF side: `MNF/RH/Core.lean:58` `noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat` is literally the unfolding of `analyticOrderNatAt riemannZeta ρ` (`rfl`), and `Core.lean:108` `theorem analyticOrderAt_eq_zeta_order {ρ : ℂ} (h : is_nontrivial_zero ρ) : analyticOrderAt riemannZeta ρ = (zeta_order ρ : ℕ∞)`.

finsum → Finset sum (`M/Algebra/BigOperators/Finprod.lean`, all `to_additive`-generated, verified): `finsum_eq_sum_of_support_subset` (from line 354 `finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i`), `finsum_mem_eq_finite_toFinset_sum` (line 529: `∏ᶠ i ∈ s, f i = ∏ i ∈ hs.toFinset, f i` for `hs : s.Finite`), `finsum_le_finsum'` (line 613: `(hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) (h : f ≤ g) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a`), `finsum_nonneg` (line 265 `one_le_finprod'`).

## (b) circleAverage API — `M/MeasureTheory/Integral/CircleAverage.lean` (`namespace Real`; variables `{E} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f₁ f₂ : ℂ → E} {c : ℂ} {R : ℝ} {a : 𝕜}`)

- line 53: `noncomputable def circleAverage : E := (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)` (explicit args `f c R`)
- line 56: `lemma circleAverage_def : circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)`
- line 62: `theorem circleAverage.integral_undef (hf : ¬CircleIntegrable f c R) : circleAverage f c R = 0`
- line 67: `lemma circleAverage_eq_intervalAverage : circleAverage f c R = ⨍ θ in 0..2 * π, f (circleMap c R θ)`
- line 83: `lemma circleAverage_map_add_const : circleAverage (fun z ↦ f (z + c)) 0 R = circleAverage f c R`
- line 95: `theorem circleAverage_eq_circleIntegral {F} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} (h : R ≠ 0) : circleAverage f c R = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z)`
- line 116: `lemma circleAverage_eq_integral_add (η : ℝ) : circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R (θ + η))`
- line 128/134 (`@[simp]`): `circleAverage_neg_radius : circleAverage f c (-R) = circleAverage f c R`; `circleAverage_abs_radius : circleAverage f c |R| = circleAverage f c R`
- line 141: `theorem circleAverage_congr_codiscreteWithin` (f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂, R ≠ 0 → equal averages); line 151: `theorem circleAverage_congr_sphere {f₁ f₂ : ℂ → E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) : circleAverage f₁ c R = circleAverage f₂ c R`
- line 160: `theorem circleAverage_eq_circleAverage_zero_one` (reduction to unit circle)
- line 200 (full name `Real.ContinuousOn.circleAverage`): `theorem ContinuousOn.circleAverage {f : ℂ → E} {s : Set ℝ} {c : ℂ} (hf : ContinuousOn f {z : ℂ | ‖z - c‖ ∈ s}) (hs : ∀ r ∈ s, 0 ≤ r) : ContinuousOn (circleAverage f c) s`; `Real.Continuous.circleAverage (hf : Continuous f) : Continuous (circleAverage f c)` (`@[fun_prop]`)
- line 243: `theorem circleAverage_const [CompleteSpace E] (a : E) (c : ℂ) (R : ℝ) : circleAverage (fun _ ↦ a) c R = a`
- line 252: `theorem circleAverage_const_on_circle [CompleteSpace E] {a : E} (hf : ∀ x ∈ Metric.sphere c |R|, f x = a) : circleAverage f c R = a`
- line 270 (`@[gcongr]`):
```lean
theorem circleAverage_mono {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℝ} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) (h : ∀ x ∈ Metric.sphere c |R|, f₁ x ≤ f₂ x) :
    circleAverage f₁ c R ≤ circleAverage f₂ c R
```
- line 281: `theorem circleAverage_mono_on_of_le_circle {f : ℂ → ℝ} {a : ℝ} (hf : CircleIntegrable f c R) (h₂f : ∀ x ∈ Metric.sphere c |R|, f x ≤ a) : circleAverage f c R ≤ a`
- line 293: `theorem abs_circleAverage_le_circleAverage_abs {f : ℂ → ℝ} : |circleAverage f c R| ≤ circleAverage |f| c R`
- line 302: `theorem circleAverage_nonneg_of_nonneg {c : ℂ} {R : ℝ} {f : ℂ → ℝ} (h₂f : ∀ x ∈ Metric.sphere c |R|, 0 ≤ f x) : 0 ≤ circleAverage f c R` (no integrability hypothesis)
- line 317: `theorem _root_.ContinuousLinearMap.circleAverage_comp_comm [CompleteSpace E] (L : E →L[ℝ] F) {f : ℂ → E} (hf : CircleIntegrable f c R) : circleAverage (L ∘ f) c R = L (circleAverage f c R)`
- line 330/338: `circleAverage_smul : circleAverage (a • f) c R = a • circleAverage f c R`; `circleAverage_fun_smul : circleAverage (fun z ↦ a • f z) c R = a • circleAverage f c R`
- line 343/350: `theorem circleAverage_add (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage f₁ c R + circleAverage f₂ c R`; `circleAverage_fun_add` (pointwise form)
- line 356/363: `theorem circleAverage_sum {ι} {s : Finset ι} {f : ι → ℂ → E} (h : ∀ i ∈ s, CircleIntegrable (f i) c R) : circleAverage (∑ i ∈ s, f i) c R = ∑ i ∈ s, circleAverage (f i) c R`; `circleAverage_fun_sum`
- line 370/377: `circleAverage_sub`, `circleAverage_fun_sub` (same hypotheses as add)

CircleIntegrable — `M/MeasureTheory/Integral/CircleIntegral.lean` (root-level):
- line 176: `def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop := IntervalIntegrable (fun θ : ℝ ↦ f (circleMap c R θ)) volume 0 (2 * π)`; line 179 `circleIntegrable_def` (Iff.rfl)
- line 183 (`@[simp]`): `theorem circleIntegrable_const (a : E) (c : ℂ) (R : ℝ) : CircleIntegrable (fun _ => a) c R`
- line 319: `theorem circleIntegrable_iff [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} (R : ℝ) : CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π)`
- line 333: `theorem ContinuousOn.circleIntegrable' {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R`
- line 337: `theorem ContinuousOn.circleIntegrable {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R`
- line 301: `CircleIntegrable.congr_codiscreteWithin`; `CircleIntegrable.add` exists (verified).

Log-norm integrability — `M/Analysis/SpecialFunctions/Integrability/LogMeromorphic.lean` (root-level, `{E} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : ℂ} {R : ℝ} {f : ℂ → E}`):
- line 132: `theorem MeromorphicOn.circleIntegrable_log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c R`
- line 174: `theorem MeromorphicOn.circleIntegrable_log_norm_of_nonneg (hf : MeromorphicOn f (sphere c R)) (hR : 0 ≤ R) : CircleIntegrable (log ‖f ·‖) c R`
- line 187: `theorem circleIntegrable_log_norm_factorizedRational {R : ℝ} {c : ℂ} (D : ℂ → ℤ) : CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R`

`M/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean` (root-level, `{a c : ℂ} {R : ℝ}`):
- line 34: `lemma circleIntegrable_log_norm_sub_const (r : ℝ) : CircleIntegrable (log ‖· - a‖) c r`
- line 178 (`@[simp]`): `theorem circleAverage_log_norm_sub_const_eq_posLog : circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖`
- line 202: `theorem circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (hR : R ≠ 0) : circleAverage (log ‖· - a‖) c R = log R + log⁺ (R⁻¹ * ‖c - a‖)`
- line 244: `lemma circleAverage_log_norm_sub_const_of_mem_closedBall (hu : a ∈ closedBall c |R|) : circleAverage (log ‖· - a‖) c R = log R`

Interval average — `M/MeasureTheory/Integral/IntervalAverage.lean`: line 46 notation `⨍ x in a..b, f x := average (Measure.restrict volume (uIoc a b)) f`; line 52 `theorem interval_average_eq (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x`; line 59 `theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) : (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a)`; line 64 `intervalAverage_congr_codiscreteWithin`.

## (c) Jensen's inequality for concave functions; concavity of log

`M/Analysis/Convex/Integral.lean` (root-level; `{α E} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ}`):
- line 141:
```lean
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ)
```
- line 188:
```lean
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) ≤ g (⨍ x in t, f x ∂μ)
```
- line 208:
```lean
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ)
```
- line 118 `ConcaveOn.average_mem_hypograph`, line 165 `ConcaveOn.set_average_mem_hypograph`, line 130 `ConvexOn.map_average_le`, line 199 `ConvexOn.map_integral_le`, line 297 `StrictConcaveOn.ae_eq_const_or_lt_map_average` (strict version).

**Pitfall:** every Jensen variant needs `hsc : IsClosed s`; `Ioi 0` is not closed, so for `log` one must work on a closed set such as `Icc ε M`/`Ici ε` (log is concave and continuous there) — a positive lower bound on `‖f‖²` on the circle/interval (or truncation) is required before applying these.

Concavity of log — `M/Analysis/Convex/SpecificFunctions/Basic.lean`:
- line 67: `theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log`
- line 217: `theorem strictConcaveOn_log_Iio : StrictConcaveOn ℝ (Iio 0) log`
- `concaveOn_log_Ioi`: **not found** (no such declaration at this checkout; the only `concaveOn_log` is `CFC.concaveOn_log` for operators). Use `strictConcaveOn_log_Ioi.concaveOn` via `M/Analysis/Convex/Function.lean:400` `theorem StrictConcaveOn.concaveOn {s : Set E} {f : E → β} (hf : StrictConcaveOn 𝕜 s f) : ConcaveOn 𝕜 s f`.
- `MeasureTheory.average_eq_integral`, `MeasureTheory.setAverage_eq`, `MeasureTheory.average_eq` exist (verified) for converting `⨍` to `∫`.

## (d) Interval integrals of `exp (c t)` and of `(a:ℂ)^(I t)`

`M/Analysis/SpecialFunctions/Integrals/Basic.lean` (root-level, `variable {a b : ℝ}`):
- line 242:
```lean
theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c
```
- line 236 (`@[simp]`): `theorem integral_exp : ∫ x in a..b, exp x = exp b - exp a`
- line 254: `lemma integral_exp_mul_I_eq_sin (r : ℝ) : ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * Real.sin r`; line 268 `integral_exp_mul_I_eq_sinc`
- line 116: `theorem integral_cpow {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) : (∫ x : ℝ in a..b, (x : ℂ) ^ r) = ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) / (r + 1)` (this is `x ^ r` in the *base*, not `a ^ (I t)`)
- line 147: `theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) : ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1)`
- `M/Analysis/SpecialFunctions/ImproperIntegrals.lean:87` `theorem integral_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ)` (improper version).

`∫ t in a..b, (n:ℂ) ^ (I * t)`: **not found** as a lemma. Route (all names verified): `M/Analysis/SpecialFunctions/Pow/Complex.lean:38` `theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y)` (`Complex.cpow_def_of_ne_zero`) rewrites the integrand to `Complex.exp ((Complex.log n * I) * t)` (after `mul_assoc`), then `integral_exp_mul_complex` with `c = Complex.log n * I` (`c ≠ 0 ↔ n ≠ 1`); `M/Analysis/SpecialFunctions/Complex/Log.lean:71` `theorem ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x` (`Complex.ofReal_log`) makes the log real. Supporting: `Complex.cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z` (Pow/Complex.lean:81), `Complex.cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹` (:90), `Complex.cpow_natCast` (:124); norms: `M/Analysis/SpecialFunctions/Pow/Real.lean:337` `theorem norm_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : ‖(x : ℂ) ^ y‖ = x ^ y.re` (`Complex.`), `Complex.norm_natCast_cpow_of_pos` (already used in BohrLandau.lean), `M/Analysis/Complex/Trigonometric.lean:950` `theorem norm_exp_ofReal_mul_I (x : ℝ) : ‖exp (x * I)‖ = 1`, `:983` `theorem norm_exp (z : ℂ) : ‖exp z‖ = Real.exp z.re` (`Complex.`), `Pow/Real.lean:282` `theorem ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ)`, `:362` `Complex.cpow_mul_ofReal_nonneg`.
Interval-integral algebra (`M/MeasureTheory/Integral/IntervalIntegral/Basic.lean`, namespace `intervalIntegral`): `integral_const_mul` (:817), `integral_mul_const` (:822), `integral_const (c : E) : ∫ _ in a..b, c = (b - a) • c` (:836), `integral_finsetSum {ι} {s : Finset ι} {f : ι → ℝ → E} (h : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) : ∫ x in a..b, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x in a..b, f i x ∂μ` (:778), `integral_comp_mul_left (hc : c ≠ 0)` (:934), `norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) : ‖∫ x in a..b, f x‖ ≤ C * |b - a|` (:769), `integral_mono_on (h : ∀ x ∈ Icc a b, f x ≤ g x)` (:1432), `integral_mono_on_of_le_Ioo` (:1437), `integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u)` (:1390), `abs_integral_le_integral_abs (hab : a ≤ b)` (:1393), `integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ` (:677), `intervalIntegral_eq_integral_uIoc` (:690); `Continuous.intervalIntegrable {u : ℝ → E} (hu : Continuous u) (a b : ℝ)` (:512), `ContinuousOn.intervalIntegrable (hu : ContinuousOn u (uIcc a b))` (:502).

## (e) Fubini — `M/MeasureTheory/Integral/Prod.lean` (`namespace MeasureTheory`; `{α β E} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [NormedSpace ℝ E] [SFinite ν]`, plus `[SFinite μ]` from line 348 on)

- line 444: `theorem integral_prod (f : α × β → E) (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`
- line 467: `theorem integral_prod_symm (f : α × β → E) (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν`
- line 472: `theorem integral_integral {f : α → β → E} (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂μ.prod ν`
- line 482: `theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν`
- line 487:
```lean
lemma intervalIntegral_integral_swap {a b : ℝ} {f : ℝ → α → E}
    (h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ
```
- line 499 — **interval × interval** (the one for `∫ t in 0..T` against a `circleAverage`, since `Real.circleAverage_def` is `(2π)⁻¹ • ∫ θ in 0..2π, …`):
```lean
lemma intervalIntegral_intervalIntegral_swap {F : ℝ → ℝ → E} {a b c d : ℝ}
    (h : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y
```
- line 509: `theorem setIntegral_prod (f : α × β → E) {s : Set α} {t : Set β} (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) : ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ`
- line 539: `theorem integral_prod_mul {L} [RCLike L] (f : α → L) (g : β → L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν` (no integrability hypothesis); line 543 `setIntegral_prod_mul ... : ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν`; line 528 `integral_prod_smul`
- line 603: `lemma integral_integral_swap_of_hasCompactSupport {f : X → Y → E} (hf : Continuous f.uncurry) (h'f : HasCompactSupport f.uncurry) {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] : ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν`
- integrability: line 231 `theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ`; line 239 `integrable_prod_iff'` (other order); line 246/250 `Integrable.prod_left_ae`/`Integrable.prod_right_ae`; line 254 `Integrable.integral_norm_prod_left`; line 335/342 `Integrable.integral_prod_left : Integrable (fun x => ∫ y, f (x, y) ∂ν) μ` / `Integrable.integral_prod_right`; line 301 (`@[fun_prop]`) `theorem Integrable.mul_prod {L} [NormedRing L] {f : α → L} {g : β → L} (hf : Integrable f μ) (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν)`; line 294 `Integrable.smul_prod`; line 192 `Integrable.swap`; line 306 `IntegrableOn.swap`; line 350 `integral_prod_swap`.
- To discharge the `IntegrableOn … (uIoc a b ×ˢ uIoc c d)` hypothesis for continuous integrands: `M/MeasureTheory/Function/LocallyIntegrable.lean:592` `theorem ContinuousOn.integrableOn_compact [T2Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ`, `:617` `theorem Continuous.integrableOn_uIoc (hf : Continuous f) : IntegrableOn f (Ι a b) μ`, `:600` `Continuous.integrableOn_Icc`; `M/Topology/Compactness/Compact.lean:1077` `theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ×ˢ t)`; `M/MeasureTheory/Integral/IntegrableOn.lean:128` `theorem IntegrableOn.mono_set (h : IntegrableOn f t μ) (hst : s ⊆ t) : IntegrableOn f s μ`; `:913` `theorem integrableOn_Icc_iff_integrableOn_Ioc (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) : IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ` (root-level, not `MeasureTheory.`); `MeasureTheory.Measure.prod_restrict`, `MeasureTheory.Measure.volume_eq_prod` (verified).

## (f) p-series and partial-sum bounds

`M/Analysis/PSeries.lean` (`namespace Real`, lines 273–367):
- line 317: `theorem summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p`
- line 280 (`@[simp]`): `theorem summable_nat_rpow_inv {p : ℝ} : Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p`
- line 311 (`@[simp]`): `theorem summable_nat_rpow {p : ℝ} : Summable (fun n => (n : ℝ) ^ p : ℕ → ℝ) ↔ p < -1` (this is the `∑ n^{-2σ}` form: `p = -2σ < -1 ↔ σ > 1/2`)
- line 325/330: `summable_nat_pow_inv {p : ℕ}`, `summable_one_div_nat_pow {p : ℕ} : Summable (fun n => 1 / (n : ℝ) ^ p) ↔ 1 < p`
- root-level section (line 392 `variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]`): line 394 `theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) : (∑ i ∈ Ioc k n, ((i : α) ^ 2)⁻¹) ≤ (k : α)⁻¹ - (n : α)⁻¹`; line 406 `theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i ∈ Ioo k n, (i ^ 2 : α)⁻¹) ≤ 2 / (k + 1)`.
- `∑_{n ≤ N} n^{-a}` for general real `a`: **no closed-form lemma found**; the available route is `M/Analysis/SumIntegralComparisons.lean` (root-level, `variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}`): line 84 `theorem AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) : ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ .range a, f (x₀ + i)`; line 97 `theorem AntitoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) : ∫ x in a..b, f x ≤ ∑ x ∈ .Ico a b, f x`; line 104 `theorem AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) : ∑ i ∈ .range a, f (x₀ + ↑(i + 1)) ≤ ∫ x in x₀..x₀ + a, f x`; line 117 `theorem AntitoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) : ∑ i ∈ .Ico a b, f ↑(i + 1) ≤ ∫ x in a..b, f x`; lines 124–139 the `MonotoneOn` mirrors; line 186 `lemma AntitoneOn.sum_Ico_le_integral {a b : ℕ} (anti : AntitoneOn f (Icc a b)) (integrable : IntegrableOn f (Ioi a)) (nonneg : ∀ t ∈ Ioi (a : ℝ), 0 ≤ f t) : ∑ n ∈ .Ico a b, f ↑(n + 1) ≤ ∫ x in Ioi (a : ℝ), f x`; line 196 `lemma AntitoneOn.sum_range_le_integral {N : ℕ} (anti : AntitoneOn f (Icc 0 (N : ℝ))) (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) : ∑ n ∈ Finset.range N, f ((n + 1 : ℕ)) ≤ ∫ x in Ioi 0, f x` — combine with `integral_rpow` above. For `a = 1`: `M/NumberTheory/Harmonic/Bounds.lean:33` `theorem harmonic_le_one_add_log (n : ℕ) : harmonic n ≤ 1 + Real.log n` and `:24` `theorem log_add_one_le_harmonic (n : ℕ) : Real.log ↑(n + 1) ≤ harmonic n` (`harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹`, `harmonic_eq_sum_Icc`); `inv_antitoneOn_Icc_right` exists.
- rpow helpers (`M/Analysis/SpecialFunctions/Pow/Real.lean`, namespace `Real`): `rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹` (:259), `inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹` (:483), `rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n` (:62), `rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z` (:548), `rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z` (:615), `rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z` (:641), `rpow_le_one`, `one_le_rpow`, `rpow_nonneg`, `rpow_pos_of_pos`, `rpow_add (hx : 0 < x)`, `rpow_sub (hx : 0 < x)`, `rpow_mul (hx : 0 ≤ x)`, `mul_rpow`, `div_rpow`, `rpow_two`, `rpow_neg_one` (all verified).

## (g) Real.log inequalities (`M/Analysis/SpecialFunctions/Log/Basic.lean`, `namespace Real`; exp ones in `M/Analysis/Complex/Exponential.lean`, `namespace Real`)

- Exponential.lean:633 `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x`; :624 `theorem add_one_lt_exp {x : ℝ} (hx : x ≠ 0) : x + 1 < Real.exp x`; :639 `lemma one_sub_lt_exp_neg {x : ℝ} (hx : x ≠ 0) : 1 - x < exp (-x)`
- Log/Basic.lean:307 `theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1`
- :312 `lemma one_sub_inv_le_log_of_pos (hx : 0 < x) : 1 - x⁻¹ ≤ log x` — this is exactly `log (n/m) ≥ (n − m)/n` with `x = n/m` (`1 - (n/m)⁻¹ = 1 - m/n = (n-m)/n`); equivalently `log_le_sub_one_of_pos` at `x = m/n`.
- :260 `theorem log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x ≠ 1) : log x < x - 1`
- :316 `lemma log_le_self (hx : 0 ≤ x) : log x ≤ x`
- :151 `lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y`; :147 `theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y`
- :213 `theorem log_nonneg (hx : 1 ≤ x) : 0 ≤ log x`; :188 `theorem log_pos (hx : 1 < x) : 0 < log x`; :225 `theorem log_natCast_nonneg (n : ℕ) : 0 ≤ log n`
- :133 `theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y`; :138 `theorem log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y`; :143 `theorem log_inv (x : ℝ) : log x⁻¹ = -log x`; :288 `theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x`; :293 `log_zpow`; :299 `log_sqrt {x : ℝ} (hx : 0 ≤ x) : log (√x) = log x / 2`; Pow/Real.lean:492 `theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x`.

## Not found (after real search)
- `concaveOn_log_Ioi` (derive via `strictConcaveOn_log_Ioi.concaveOn`).
- A direct lemma `divisor f U z = analyticOrderNatAt f z` (compose `MeromorphicOn.AnalyticOnNhd.divisor_apply` + `ENat.map_natCast` + `WithTop.untop₀_natCast`, or `Nat.cast_analyticOrderNatAt`).
- A direct `∫ t in a..b, (n:ℂ)^(I*t)` lemma (compose `Complex.cpow_def_of_ne_zero` + `integral_exp_mul_complex`).
- A closed-form `∑_{n ≤ N} n^{-a} ≤ …` for real `a ≠ 2` (use `AntitoneOn.*_le_integral*` + `integral_rpow`; `a = 1`: `harmonic_le_one_add_log`; `a = 2`: `sum_Ioc_inv_sq_le_sub`, `sum_Ioo_inv_sq_le`).
- Jensen's inequality for concave functions without an `IsClosed s` hypothesis.

Files written (verification only, nothing under the zeta23 tree): `/tmp/claude-1000/-home-joeyxyxyz--config-Claude-scratch-workspaces-7e77cf71-e1c7-4f02-afcd-2f47af5ebdd4-8f8b3000-2966-4980-93f3-540a0fefac31-scratch-2026-10-28-0cd942/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/density-work/agents/mathlib-inventory/Check.lean` and `.../Check2.lean`.

## 3. Mathematical route

# RightHalfBound — complete proof routes (A classical, B Littlewood‑free), the mean square (C), and the input table (D)

File read with `cat`: `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/BohrLandau.lean`. Sorry‑free there: `NOff_eq_right_add_left`, `NLeft_eq_NRight`, `bohrLandau_of_right`, `meanSquare_gt_one`, `norm_zeta_le_tsum`. Sorried: `meanSquare_strip` (1/2<σ≤1, ∫ from 0) and `rightHalfBound_of_meanSquare`. Notation below: s = σ+it, zeros ρ = β+iγ with multiplicity m(ρ) = `zeta_order ρ` = `(analyticOrderAt riemannZeta ρ).toNat` (MNF/RH/Core.lean:58); NRight(δ,T) as in the file; WLOG δ ≤ 1/2 (NRight is antitone in δ and NRight(δ,T)=0 for δ ≥ 1/2 by `riemannZeta_ne_zero_of_one_le_re`).

## 0. Two statement‑level warnings about the sorried lemmas

**(W1) σ = 1 with lower limit 0 is vacuous.** |ζ(1+it)|² ~ t⁻² as t→0 is not integrable on (0,T); Lean's interval integral of a non‑integrable function is 0, so `meanSquare_strip` at σ=1 is true for any C ≥ 0 and carries no information. Everything below uses ∫ from 1 (route B needs u ≥ 3/2 anyway; route A needs t ≥ T₁ ∈ (2,3)). For 1/2<σ<1 the 0‑based and 1‑based forms differ by ∫_0^1|ζ|² ≤ (1/2 + 1/(1−σ) + 3)² (`norm_riemannZeta_le_of_re_pos`), which is not uniform as σ→1⁻ — a second reason to use lower limit 1.

**(W2) `ZetaMeanSquare` is pointwise in σ (∀σ ∃C).** Route B integrates over a one‑parameter family of abscissae σ_θ = 2+R cos θ and needs sup_θ C(σ_θ) < ∞, which cannot be extracted from the pointwise statement (C(σ) is an arbitrary choice function). The proof in §C gives uniformity for free (every piece is monotone in σ), so the lemma should be stated as

```
def ZetaMeanSquareUnif : Prop := ∀ σ₁ : ℝ, 1/2 < σ₁ → σ₁ < 1 → ∃ C : ℝ,
  ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T
```
Route A only needs the pointwise version at one abscissa σ₀ < 1 (lower limit 1).

## A. Classical route (Littlewood's lemma; Titchmarsh §9.9 + §9.15, Ivić §11 / Thm 11.?)

**Littlewood's lemma** (Titchmarsh §9.9, real form; sign checked by the slit argument). Let f be holomorphic in and on the rectangle 𝓡 = [α,β]×[T₁,T₂], f ≠ 0 on the three sides σ=β, t=T₁, t=T₂ (zeros on σ=α are allowed; they get weight 0). Then, with arg f on the horizontal sides defined by continuous variation from the side σ=β,

  2π Σ_{ρ∈𝓡} m(ρ)(β_ρ − α) = ∫_{T₁}^{T₂} log|f(α+it)| dt − ∫_{T₁}^{T₂} log|f(β+it)| dt + ∫_α^β arg f(σ+iT₂) dσ − ∫_α^β arg f(σ+iT₁) dσ.

(Derivation: ∫_{∂𝓡} log f ds = −2πi Σ m(ρ)(β_ρ−α) by cutting from each zero to the left side; the right side above is Re(i∫_{∂𝓡} log f ds).)

**Application.** Fix δ ∈ (0,1/2], put σ₀ := 1/2 + δ/2 (any σ₀ ∈ (1/2, 1/2+δ) works; η := 1/2+δ−σ₀ = δ/2), β := 2, T₁ ∈ (2,3) not an ordinate of a zero, and for T ≥ 4 pick T' ∈ (T, T+1) not an ordinate (both exist: zeros in a box are finite, `zerosIn_finite`). Take f = ζ (no pole in 𝓡 since T₁ > 0). All weights β_ρ − σ₀ are ≥ 0 and the zeros with β ≥ 1/2+δ, T₁<γ≤T have weight ≥ η, so

  η·(NRight(δ,T) − NRight(δ,3)) ≤ Σ_{ρ∈𝓡} m(ρ)(β_ρ−σ₀) = (1/2π)[ I₁ + I₂ + I₃ + I₄ ].

Term by term:
1. I₂ = −∫_{T₁}^{T'} log|ζ(2+it)| dt ≤ (T'−T₁) log 3 ≤ T log 3, from |ζ(2+it)| ≥ 1/3 (`Zeta23.RvM.zeta_lower_bound_two`).
2. I₁ = ∫_{T₁}^{T'} log|ζ(σ₀+it)| dt. Pointwise log x ≤ ½ log(1+x²) (true also at x=0 with Lean's log 0 = 0); then Jensen for the concave log on the probability measure dt/(T'−T₁) on [T₁,T'] (`ConcaveOn.le_map_set_average`, s = Ici 1, f = 1+|ζ|², no a.e. positivity issue):
  I₁ ≤ ½ (T'−T₁) log(1 + (1/(T'−T₁))∫_{T₁}^{T'}|ζ(σ₀+it)|² dt) ≤ ½ (T+1) log(1 + 5C(σ₀)) ≤ T log(1+5C(σ₀)),
  using ∫_{T₁}^{T'}|ζ|² ≤ ∫_1^{T+1}|ζ(σ₀+it)|² ≤ C(σ₀)(T+1) and (T+1)/(T'−T₁) ≤ (T+1)/(T−3) ≤ 5 for T ≥ 4. Only the pointwise mean square at σ₀ = 1/2+δ/2 < 1 with lower limit 1 is used.
3. I₃ = ∫_{σ₀}^2 arg ζ(σ+iT') dσ. |arg ζ(2+iT')| < π/2 since Re ζ(2+it) > 0 (`Zeta23.RvM.re_riemannZeta_two_pos`), and the variation along the segment is Backlund's bound |Im ∫_σ^2 ζ'/ζ(u+iT') du| ≤ C_B log T' for T' ≥ T₀ zero‑free (tree: `Zeta23.RvM.backlund_horizontal` for the full segment [1/2,2]; the sub‑segment [σ,2] version is the same proof, the aux lemma `im_integral_logDeriv_le_aux` is already stated with general endpoints). So |I₃| ≤ 2(π/2 + C_B log(T+1)) = O(log T). Only O(T) is needed here, so even a crude O(log T) is overkill.
4. I₄ = −∫_{σ₀}^2 arg ζ(σ+iT₁) dσ: T₁ fixed, same bound, a constant K₁.

Collecting, for T ≥ 4:
  NRight(δ,T) ≤ NRight(δ,3) + (2/δ)(1/2π)[ T(log 3 + log(1+5C(1/2+δ/2))) + π + 2C_B log(T+1) + K₁ ],
and for 2 ≤ T ≤ 4, NRight(δ,T) ≤ NRight(δ,4). Hence RightHalfBound with
  C_A(δ) = NRight(δ,4)/2 + (1/(πδ))[log 3 + log(1+5C(1/2+δ/2)) + (π + 2C_B log 3 + K₁)/2 + C_B].

Inputs: Littlewood's lemma (not in Mathlib, not in the tree), Backlund (tree has), |ζ(2+it)| ≥ 1/3 (tree has), concavity of log (Mathlib), pointwise mean square at one σ₀<1 (missing, §C). Littlewood's lemma is the only genuinely new complex‑analytic object; it can be obtained by integrating a rectangle argument principle over the left abscissa (layer‑cake: Σ m(ρ)(β_ρ−α) = ∫_α^β N_f(σ') dσ' and 2πN_f(σ') = Δ_{∂𝓡(σ')} arg f, then Cauchy–Riemann ∂_σ log|f| = ∂_t arg f), but that is exactly the contour machinery route B avoids.

## B. Littlewood‑free route (Jensen on discs centred 2+it, averaged in t)

**Geometry and radii.** Centre c_t = 2+it, outer radius R, inner radius r, 0 < r < R < 3/2. For t ≥ 3 the closed disc B(c_t,R) misses the pole (|c_t − 1| ≥ √10 > 3/2) and lies in {Re s ≥ 2−R} ⊂ {Re s > 1/2}; ζ is analytic there (`Zeta23.RvM.analyticOnNhd_riemannZeta`) and ζ(c_t) ≠ 0 with |ζ(c_t)| ≥ 1/3.

A zero ρ with β ≥ 1/2+δ lies in the closed inner disc B(c_t,r) iff (2−β)² + (t−γ)² ≤ r², i.e. |t−γ| ≤ √(r² − (2−β)²), and since 2−β ≤ 3/2−δ this holds whenever |t−γ| ≤ h := √(r² − (3/2−δ)²). So the t‑interval has positive length 2h iff **r > 3/2 − δ**. With r < R < 3/2 this forces δ > 3/2 − R: **route B with outer radius R reaches exactly δ > δ₀(R) := 3/2 − R.** Conversely, if the (uniform) mean square is available for σ ≥ σ₁, one needs 2 − R ≥ σ₁, so route B reaches δ > σ₁ − 1/2: with the full mean square (any σ₁ > 1/2) every δ > 0; with only the naive mean square of §C (σ₁ > 2/3) only δ > 1/6.

Concrete choice for δ ∈ (0,1/2]:
  R := 3/2 − δ/4, r := 3/2 − δ/2, σ₁ := 2 − R = 1/2 + δ/4,
  r² − (3/2−δ)² = (δ/2)(3 − 3δ/2) = (3δ/2)(1−δ/2) ≥ 9δ/8 (δ ≤ 1/2), so take h₀ := (3/2)√(δ/2) ≤ 3/4,
  log(R/r) = log(1 + δ/(6−2δ)) ≥ δ/(6−δ) ≥ δ/6.

**Step 1 (Jensen, per t).** Mathlib `AnalyticOnNhd.circleAverage_log_norm`: circleAverage(log‖ζ‖)(c_t,R) = Σᶠ_u divisor ζ (B(c_t,R)) u · log(R/‖c_t−u‖) + log‖ζ(c_t)‖. All terms are ≥ 0; those with ‖u−c_t‖ ≤ r have log(R/‖c_t−u‖) ≥ log(R/r). Hence, with n_t(r) := Σᶠ_u divisor ζ (B(c_t,r)) u (zeros in the closed inner disc with multiplicity),

  n_t(r) · log(R/r) ≤ circleAverage(log‖ζ‖)(c_t,R) − log‖ζ(c_t)‖ ≤ circleAverage(log‖ζ‖)(c_t,R) + log 3.

This is the first `calc` step inside Mathlib's `AnalyticOnNhd.sum_divisor_le` with the sup bound not applied; a ~10‑line refactor gives the lemma
`(∑ᶠ u, (divisor f (closedBall c r) u : ℝ)) * Real.log (R / r) ≤ circleAverage (Real.log ‖f ·‖) c R - Real.log ‖f c‖` (0<r<R, f analytic on closedBall c R, f c ≠ 0).

**Step 2 (kill log at zeros).** Put L(s) := ½ log(1+‖ζ(s)‖²) ≥ 0, continuous on the region, with log‖ζ(s)‖ ≤ L(s) pointwise (including ζ(s)=0). `circleAverage_mono` (both sides circle‑integrable: `MeromorphicOn.circleIntegrable_log_norm`, resp. continuity) gives n_t(r) log(R/r) ≤ circleAverage(L)(c_t,R) + log 3.

**Step 3 (counting by covering).** Let Z := {ρ : ζ(ρ)=0, β ≥ 1/2+δ, 4 < γ ≤ T} (finite). For t ∈ [3,T+3]: Σ_{ρ∈Z} m(ρ)·1[|t−γ_ρ| ≤ h₀] ≤ n_t(r) (each such ρ is in B(c_t,r): (2−β)²+(t−γ)² ≤ (3/2−δ)² + 9δ/8 ≤ r²; divisor ζ (B(c_t,r)) ρ = m(ρ) by `AnalyticOnNhd.divisor_apply` and the definition of `zeta_order`; all other divisor values are ≥ 0). Since h₀ < 1, [γ−h₀, γ+h₀] ⊂ [3,T+3] for every ρ ∈ Z, so integrating over t ∈ [3,T+3] (left side: finite sum of indicators; right side: t ↦ circleAverage(L)(c_t,R) is a continuous parametric integral):

  2h₀ · log(R/r) · (NRight(δ,T) − NRight(δ,4)) ≤ ∫_3^{T+3} circleAverage(L)(c_t,R) dt + T log 3.

**Step 4 (Fubini + shift).** circleAverage(L)(c_t,R) = (2π)⁻¹∫_0^{2π} L(σ_θ + i(t + R sin θ)) dθ, σ_θ := 2 + R cos θ ∈ [σ₁, 7/2]. The integrand is continuous on the compact rectangle [0,2π]×[3,T+3] (no pole), so `integral_integral_swap` applies; then u := t + R sin θ ∈ [3−R, T+3+R] ⊂ [3/2, T+5] and L ≥ 0 let us enlarge the u‑range:

  ∫_3^{T+3} circleAverage(L)(c_t,R) dt ≤ (2π)⁻¹ ∫_0^{2π} ∫_1^{T+5} L(σ_θ+iu) du dθ.

**Step 5 (concavity, one variable).** For each θ, Jensen for log on Ici 1 with the probability measure du/(T+4) on [1,T+5]:
  ∫_1^{T+5} L(σ_θ+iu) du ≤ ½ (T+4) log(1 + (1/(T+4)) ∫_1^{T+5} |ζ(σ_θ+iu)|² du) ≤ ½ (T+4) log(1 + 2 C_u(σ₁)),
using the **uniform** mean square ∫_1^{T'}|ζ(σ+iu)|² du ≤ C_u(σ₁)T' for all σ ≥ σ₁, T' ≥ 2, and (T+5)/(T+4) ≤ 2. (Doing concavity first over the circle and then over t, as in the task's phrasing, is equally valid and ends at the same quantity; either order needs sup over σ ∈ [σ₁, 7/2] — pointwise C(σ) is not enough, see W2.)

**Step 6 (assemble).** With T+4 ≤ 3T (T ≥ 2):
  2h₀ log(R/r) (NRight(δ,T) − NRight(δ,4)) ≤ T[(3/2) log(1+2C_u(σ₁)) + log 3],
and 2h₀ log(R/r) ≥ 3√(δ/2)·δ/6 = (δ/2)^{3/2}. Hence RightHalfBound with

  C_B(δ) = NRight(δ,4)/2 + (2/δ)^{3/2} [ (3/2) log(1 + 2 C_u(1/2+δ/4)) + log 3 ].

Uniformity ledger for route B: (i) the mean‑square constant must be one number for all σ ∈ [1/2+δ/4, 7/2] (for σ ≥ 2 use ‖ζ‖ ≤ π²/6, `norm_riemannZeta_le_of_two_le_re`; the proof in §C gives σ ≥ σ₁ anyway); (ii) lower limit of the u‑integral is ≥ 3/2, so a lemma with lower limit 1 suffices and σ = 1 is harmless; (iii) nothing else depends on θ or t except through continuity on a compact set.

## C. The mean square ∫_1^T |ζ(σ+it)|² dt = O(T), 1/2 < σ (uniform for σ ≥ σ₁)

**Starting point (what the tree has).** `Zeta0EqZeta` + `riemannZeta0` + `ZetaBnd_aux1b` (Zeta23/FromPNTPlus/ZetaBounds.lean): for Re s > 0, s ≠ 1, N ≥ 1,
  ζ(s) = D_N(s) + P_N(s) − N^{−s}/2 + s·J_N(s), D_N = Σ_{n=1}^N n^{−s}, P_N = N^{1−s}/(s−1), J_N = ∫_N^∞ ψ(x)x^{−s−1}dx, ψ(x)=⌊x⌋+1/2−x, |J_N| ≤ N^{−σ}/σ.

**Dirichlet‑polynomial mean value (elementary form).** For any a_n, |∫_1^T (n/m)^{it} dt| ≤ 2/|log(n/m)| (m ≠ n), so
  ∫_1^T |Σ_{n≤N} a_n n^{−it}|² dt ≤ T Σ|a_n|² + 2 Σ_{m≠n} |a_m a_n| / |log(n/m)|.
With a_n = n^{−σ}, σ ∈ [σ₁, ∞), σ₁ ∈ (1/2,1): using 1/log(n/m) ≤ n/(n−m) (m<n) and S_n := Σ_{m<n} m^{−σ}/(n−m) ≤ n^{−σ}(4 + 2/(1−σ) + 2 log n) (split at m = n/2) and Σ_{n≤N} n^{1−2σ} ≤ N^{2−2σ}/(2−2σ):
  ∫_1^T |D_N|² dt ≤ T ζ(2σ₁) + E_off(N,σ₁),  E_off(N,σ₁) := (2/(1−σ₁))(4 + 2/(1−σ₁) + 2 log N) N^{2−2σ₁},
and every term is monotone decreasing in σ, so the bound at σ₁ is a bound for all σ ≥ σ₁ (this is where uniformity comes from). The Montgomery–Vaughan form removes the log: the tree has the weighted Hilbert inequality sorry‑free (`Zeta23.MV.mv_hilbert`: `MVHilbert 26`, Zeta23/MV/Final.lean); with freq_n = log n, δ_n = log(1+1/n) ≥ 1/(n+1) it gives |off‑diag| ≤ 2·26·Σ(n+1)|a_n|², i.e. ∫_0^T|D_N|² ≤ Tζ(2σ) + 104 N^{2−2σ}/(2−2σ). Not needed, but available.

**Naive error term — the computation.** For t ∈ [1,T], σ ≥ σ₁ > 1/2, N ≥ 1 fixed (depending on T only):
  |ζ|² ≤ 4(|D_N|² + |P_N|² + 1/4 + |sJ_N|²);
  ∫_1^T |P_N|² = N^{2−2σ}∫_1^T dt/((σ−1)²+t²) ≤ N^{2−2σ₁};
  |sJ_N| ≤ (σ+t)N^{−σ}/σ ≤ (1+2t)N^{−σ₁} ≤ 3tN^{−σ₁}, so ∫_1^T|sJ_N|² ≤ 3T³N^{−2σ₁}.
Total: ∫_1^T|ζ(σ+it)|²dt ≤ 4[ Tζ(2σ₁) + E_off(N,σ₁) + N^{2−2σ₁} + T/4 + 3T³N^{−2σ₁} ].
Take N = ⌈T^a⌉. Then 3T³N^{−2σ₁} ≤ 3T iff a σ₁ ≥ 1, and E_off ≈ T^{a(2−2σ₁)} log T ≤ C·T iff a(2−2σ₁) < 1. Both hold iff 1/σ₁ ≤ a < 1/(2−2σ₁), i.e. iff **σ₁ > 2/3** (with MV's log‑free E_off, σ₁ ≥ 2/3). With a = 1/σ₁: E_off ≈ T^{2/σ₁−2} log T. So the naive error term gives the mean square (uniformly) for σ ≥ σ₁ for every σ₁ > 2/3 and for nothing below 2/3 — also with t‑dependent or dyadic N (same exponents block‑wise).

Where "3/4" comes from: if one fixes N = T² (so that |sJ_N| ≤ 3t·T^{−2σ} ≤ 3 for all σ ≥ 1/2 at once), then E_off ≈ T^{4−4σ₁} log T = O(T) iff σ₁ > 3/4. Optimising N = T^{1/σ₁} improves 3/4 to 2/3; nothing improves 2/3 while the error is |s|N^{−σ}/σ. (With N = ⌊t⌋ as in `ZetaUpperBnd`, ∫|sJ|² ≈ T^{3−2σ₁}, which is O(T) only at σ₁ = 1.)

Consequence for Bohr–Landau with only the naive tool: route A needs σ₀ ∈ (2/3, 1/2+δ), route B needs σ₁ = 2−R > 2/3 and δ > 3/2−R: both give RightHalfBound only for δ > 1/6 (i.e. N(2/3+ε, T) = O(T)). The full ∀δ>0 needs the strip 1/2 < σ ≤ 2/3.

**What is needed for 1/2 < σ ≤ 2/3 — not MV.** MV only sharpens the polynomial part (removes the log, moves σ > 2/3 to σ ≥ 2/3). The bottleneck is the approximation error; it must be bounded (O(1) suffices; O(x^{−σ}) is Titchmarsh Thm 4.11) with N ≈ T, so that E_off ≈ T^{2−2σ₁} log T = o(T) for every σ₁ > 1/2. Two ways:

(C1) *Titchmarsh Theorem 4.11, made elementary* (Lemma 4.8/4.10 replaced by a second Euler–Maclaurin step + Fourier series of the periodic B₂; Lemma 4.3 = first‑derivative test kept). With B̃₂(x) = {x}²−{x}+1/6, ψ = −B̃₂'/2, one more integration by parts in J_N gives
  ζ(s) = D_N(s) + P_N(s) + E₂,  E₂ = −N^{−s}/2 + (s/12)N^{−s−1} − (s(s+1)/2)∫_N^∞ B̃₂(x)x^{−s−2}dx.
Expand B̃₂(x) = π^{−2}Σ_{k≥1} cos(2πkx)/k² (absolutely convergent; Mathlib `hasSum_one_div_nat_pow_mul_cos`, k=1), swap Σ and ∫ (dominated by Σk^{−2}x^{−σ−2}), and bound I_k^± = ∫_N^∞ e^{i(±2πkx − t log x)} x^{−σ−2} dx by the first‑derivative test: for x ≥ N ≥ t the phase derivative ±2πk − t/x has modulus ≥ 2πk−1 and x^{−σ−1}/(2πkx ∓ t) is positive decreasing, so one integration by parts gives |I_k^±| ≤ 2N^{−σ−2}/(2πk−1) ≤ N^{−σ−2}/(2k). Hence |∫_N^∞ B̃₂ x^{−s−2}| ≤ ζ(3)N^{−σ−2}/(2π²) ≤ 0.061 N^{−σ−2}, and for 0 < σ ≤ 2, t ≥ 0, **N ≥ t+3**:
  |E₂| ≤ 1/2 + 1/12 + 0.031 < 1.
Lean shape: `‖riemannZeta (σ+t*I) − ∑ n ∈ Finset.Icc 1 N, 1/(n:ℂ)^(σ+t*I) − (N:ℂ)^(1−(σ+t*I))/((σ+t*I)−1)‖ ≤ 1` for `0<σ≤2`, `0≤t`, `t+3 ≤ N`. Then with N := ⌊T⌋+3 fixed on [1,T]: ∫_1^T|ζ|² ≤ 3[Tζ(2σ₁) + E_off(T+3,σ₁) + (T+3)^{2−2σ₁} + T] ≤ C_u(σ₁)·T for every σ₁ ∈ (1/2,1), all σ ≥ σ₁, with C_u(σ₁) explicit (≈ ζ(2σ₁) + (1−σ₁)^{−2}·sup_{T≥2} T^{1−2σ₁}log(T+3), i.e. of size (2σ₁−1)^{−2}‑ish). This is `ZetaMeanSquareUnif`.

(C2) *No oscillatory integrals at all*: k‑th order Euler–Maclaurin for x^{−s} with N = ⌈T^{1+ε}⌉. The k‑th remainder is ≤ C_k ∏_{j<k}|s+j| · N^{1−σ−k} ≤ C_k' T^{(1+ε)(1−σ₁) − εk}, bounded as soon as εk ≥ (1+ε)(1−σ₁); the boundary terms are ≤ T^{−ε(j−1)−(1+ε)σ} ≤ 1; the polynomial part needs (1+ε)(2−2σ₁) < 1. Choose ε := (2σ₁−1)/(4(1−σ₁)) (then (1+ε)(2−2σ₁) = 3/2−σ₁ < 1) and k := ⌈(1+ε)(1−σ₁)/ε⌉ (σ₁=0.6: ε=1/8, k=4; σ₁=0.51: ε≈0.0102, k=49). Works for every fixed σ₁ > 1/2 but k → ∞ as σ₁ → 1/2, so a formalisation needs general‑order Euler–Maclaurin (tree has order 1 only: `ZetaSum_aux1`; Mathlib has `bernoulliFun`/`periodizedBernoulli` but, as far as I can see, no Euler–Maclaurin summation formula — unknown).

Recommendation: (C1). Its three ingredients are each short, and it also shortens the Dirichlet polynomial to length ≈ T, which is what makes E_off = o(T) down to σ = 1/2⁺.

## D. Input table

| # | Analytic input | Classical ref. | Lean statement (shape) | Tree / Mathlib status |
|---|---|---|---|---|
| 1 | Jensen's formula, analytic f, f(c)≠0 | Titchmarsh §3.6 | `AnalyticOnNhd.circleAverage_log_norm` | Mathlib has (JensenFormula.lean:376) |
| 2 | Jensen counting inequality with circle average retained: n(r)·log(R/r) ≤ circleAverage(log‖f‖) c R − log‖f c‖ | same | `(∑ᶠ u, (divisor f (closedBall c r) u:ℝ)) * log (R/r) ≤ circleAverage (log ‖f ·‖) c R − log ‖f c‖` | Not present as such; Mathlib `AnalyticOnNhd.sum_divisor_le` (line 390) has the sup‑bounded version and its proof contains this step verbatim — easy refactor |
| 3 | ζ analytic on B(2+it,R), R<3/2, t≥3; ζ(2+it)≠0; ‖ζ(2+it)‖ ≥ 1/3 | trivial | `analyticOnNhd_riemannZeta`, `zeta_lower_bound_two`, `riemannZeta_ne_zero_of_two_le_re` | tree has (Zeta23/RvM/ZetaGrowth.lean) |
| 4 | divisor ζ (closedBall c r) ρ = zeta_order ρ for ρ in the ball | — | glue: `AnalyticOnNhd.divisor_apply` + unfold `MNF.RH.zeta_order` | Mathlib + MNF have the pieces; glue lemma missing (trivial) |
| 5 | finiteness of zeros in boxes / discs | — | `MNF.RH.zerosIn_finite`, `Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact` | tree has |
| 6 | log x ≤ ½log(1+x²); log concave; Jensen for integrals | — | `strictConcaveOn_log_Ioi`, `ConcaveOn.le_map_set_average` / `ConcaveOn.le_map_integral` (s = Ici 1) | Mathlib has (Convex/SpecificFunctions/Basic.lean:67, Convex/Integral.lean:188/208) |
| 7 | circleAverage as interval integral; monotonicity; circle‑integrability of log‖ζ‖ | — | `circleAverage_def`, `circleAverage_mono`, `MeromorphicOn.circleIntegrable_log_norm` | Mathlib has |
| 8 | Fubini on a compact rectangle for a continuous integrand; shift of variable | — | `MeasureTheory.integral_integral_swap`, `ContinuousOn.integrableOn_compact`, `intervalIntegral.integral_comp_add_right` | Mathlib has |
| 9 | continuity of t ↦ circleAverage g (2+it) R for continuous g | — | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` (Mathlib's `ContinuousOn.circleAverage` is continuity in the radius only) | Mathlib has the tool; the centre‑continuity lemma itself is missing (short) |
| 10 | Mean square, uniform: ∀σ₁∈(1/2,1) ∃C ∀σ≥σ₁ ∀T≥2, ∫_1^T‖ζ(σ+it)‖² ≤ CT | Titchmarsh Thm 7.2 (§7.2), Ivić Thm 1.9 | `ZetaMeanSquareUnif` above | MISSING (the core); tree's `meanSquare_strip` is sorried, pointwise, lower limit 0 (W1, W2) |
| 11 | Approximate formula, naive error ‖sJ_N‖ ≤ ‖s‖N^{−σ}/σ | Titchmarsh (2.1.4)/(3.5.3) | `Zeta0EqZeta`, `ZetaBnd_aux1b`, `ZetaBnd_aux1` | tree has (Zeta23/FromPNTPlus/ZetaBounds.lean:815–850) — suffices only for σ₁ > 2/3 |
| 12 | Approximate formula with bounded error for N ≥ t+3 (C1) | Titchmarsh Thm 4.11; Lemmas 4.2/4.3 (first‑derivative test), 4.8/4.10 | `zeta_approx_bounded` as in §C | MISSING. Sub‑inputs: 2nd‑order E–M for x^{−s} (tree has 1st order `ZetaSum_aux1`: missing one more IBP); Fourier series of B̃₂: Mathlib has `hasSum_one_div_nat_pow_mul_cos`/`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` (ZetaValues.lean:301–389); first‑derivative test: not in Mathlib, provable from `intervalIntegral.integral_deriv_mul_eq_sub` + monotonicity (IntegrationByParts.lean:87); Σ/∫ swap: `integral_tsum` or dominated convergence |
| 13 | Dirichlet‑polynomial mean value, elementary (2/‖log(n/m)‖ off‑diagonal) and the off‑diagonal sum ≤ E_off(N,σ₁) | Titchmarsh §7.2 (inside proof of Thm 7.2) | `∫ t in 1..T, ‖∑ n ∈ Icc 1 N, 1/(n:ℂ)^(σ+t*I)‖^2 ≤ T * ζ(2σ₁) + E_off N σ₁` for σ ≥ σ₁ | MISSING (elementary; only finite sums, ∫(n/m)^{it}, and 1/log(n/m) ≤ n/(n−m)) |
| 14 | Montgomery–Vaughan weighted Hilbert inequality (optional, log‑free E_off) | Montgomery–Vaughan 1974 | `Zeta23.MVHilbert C` | tree has, sorry‑free, C = 26: `Zeta23.MV.mv_hilbert` (Zeta23/MV/Final.lean); the specialisation freq=log n, δ_n=log(1+1/n) is missing (short) |
| 15 | Littlewood's lemma (rectangle) | Titchmarsh §9.9 | real form as in §A for f = ζ on [σ₀,2]×[T₁,T'] | NOT in Mathlib; NOT in the tree as far as I can see; derivable from a rectangle argument principle (whether Zeta23/RvM/Fold.lean etc. contain a reusable one: unknown) |
| 16 | Backlund: ‖arg ζ(σ+iT)‖ ≪ log T on σ∈[σ₀,2], T zero‑free | Titchmarsh §9.4 | `Zeta23.RvM.backlund_horizontal`, `im_integral_logDeriv_le`, `reZeroSet_card_le`; `re_riemannZeta_two_pos`, `vertical_two` | tree has for the segment [1/2,2]; sub‑segment [σ,2] version: aux lemma has general endpoints (line 186) — check |
| 17 | growth ‖ζ(s)‖ ≤ C‖Im s‖ on Re s ≥ δ (used by Backlund; not needed in B) | Titchmarsh (3.5) | `zeta_growth`, `zeta_growth_right`, `ZetaUpperBnd` | tree has |
| 18 | zero‑free ordinates near any T; NRight(δ,T)=0 for δ≥1/2; NRight antitone in δ | — | from `zerosIn_finite`, `riemannZeta_ne_zero_of_one_le_re` | trivial glue |
| 19 | local zero count ≪ log t (not needed for A or B as written) | Backlund/RvM | `zeta_local_zero_count` | tree has (Zeta23/RvM/LocalCount.lean:266) |

Bottom line: route B needs only Mathlib's Jensen formula plus rows 2, 4, 9 (short glue) and row 10; route A additionally needs Littlewood's lemma (row 15, the only heavy contour‑integration object) but only a pointwise mean square. Row 10 is the real work in either case; with the tree's naive error it closes only for σ₁ > 2/3 (δ > 1/6); closing all σ₁ > 1/2 needs row 12 (C1), i.e. one more Euler–Maclaurin step, the Fourier series of B̃₂ (Mathlib has it), and a one‑integration‑by‑parts first‑derivative test — not Montgomery–Vaughan, which the tree already has and which only removes a log.