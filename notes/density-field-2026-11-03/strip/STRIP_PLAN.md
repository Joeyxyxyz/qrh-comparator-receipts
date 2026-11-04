# STRIP_PLAN — a power-saving zero-density estimate on the zeta23/MNF tree

Planner's document, 2026-11-03. Tree: `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23` (read-only; Lean `v4.33.0-rc2`, Mathlib `51e6992e`). All new Lean goes under `…/scratchpad/density-work/strip/<label>/`, compiled with `cd <tree> && PATH=$HOME/.elan/bin:$PATH lake env lean /abs/path/File.lean`, header `import Zeta23.BL.BohrLandauClosure` (which pulls in `BohrLandauPartial`, `JensenDisc`, `Zeta23.BohrLandau`, `Zeta23.MV`, `Mathlib`). Every tree name below was re-grepped on 2026-11-03 against the files named; every Mathlib name was grepped under `.lake/packages/mathlib`. Inputs: the inventory, the route report, the landscape memo (all three read in full).

Conventions used in the statements: `open Finset Complex MeasureTheory Metric`, `open scoped ArithmeticFunction.Moebius` (so `μ` is `ArithmeticFunction.moebius`), `I = Complex.I`, `NRight` is `Zeta23.BL.NRight` (= `MNF.RH.NRight`, `Zeta23/BohrLandau.lean:16`), `zeta_order`, `is_nontrivial_zero`, `zerosIn` are `MNF.RH.*` (`MNF/RH/Core.lean:52,58`, `Counting.lean:52`), `Rout/rin/hwin` are `Zeta23.BL.*` (`BohrLandauPartial.lean:1238-1240`). New declarations live in `namespace Zeta23.Density`.

---

## (A) Honest framing

1. The strip is `MNF.RH.SpectralGapHyp Δ`, kernel-checked (`spectralGapHyp_iff_zeroFree_strip`, `MNF/RH/Hypotheses.lean:85`) to be exactly "ζ(s) ≠ 0 for 1/2 < Re s < 1/2 + Δ": it follows from RH, it *is* RH for Δ > 3/8 given the receipted 7/8 half-plane, and for 0 < Δ ≤ 3/8 it is open, has no name in the literature, and has been claimed by nobody.
2. Every method that is known beside the line yields a *count* of zeros, never their absence — Bohr–Landau's O(T) (receipted on this tree as `Zeta23.BL.bohrLandau_full`), the Carlson/Ingham/Guth–Maynard power savings, the proportions on the line — and the conjectural ceiling of the whole family, the density hypothesis, still leaves T^{1−2Δ+ε} zeros; moreover any mean-value argument that would run unchanged for the Davenport–Heilbronn function (which has zeros off the line and even in Re s > 1) cannot produce a band, and the only place the plan below uses ζ's multiplicativity (`μ * ζ = 1` in the mollifier) buys a power, not a band.
3. Therefore no step in this plan proves, or claims to approach, the strip; `SpectralGapHyp Δ` is untouched by everything below.
4. The honest, formalizable step is to sharpen the receipted Bohr–Landau bound `NRight δ T ≤ C·T` to a power saving `NRight δ T ≤ C·T^{1−c(δ)}·(1+log T)³` with explicit c(δ) > 0 (Carlson-type), using the same disc-average machinery already receipted (`JensenDisc.lean`, `BohrLandauPartial.lean` J0–J9) applied to the mollified function f = ζ·M_X, M_X(s) = Σ_{n≤X} μ(n) n^{−s}, plus the receipted sharp approximate formula and the receipted Montgomery–Vaughan mean value: it replaces "at most C·T zeros at distance ≥ δ from the line below height T" by "at most T^{1−c}", i.e. the proportion of zeros in (T, 2T] at distance ≥ δ is ≤ T^{−c} rather than ≤ C.
5. This is strictly weaker than the strip and is not known to imply anything about it; its value is (i) the first kernel-checked zero-density estimate with a power saving on this trust base (novelty subject to Mark Lewko's two unverified Palomar entries, `DEPOSIT_MAP.md` §8, to be read before any claim), and (ii) exactly the architecture that Ingham, Huxley and Guth–Maynard refine, so it is the right foundation if the project ever goes further, while costing about one Bohr–Landau-sized workflow (~3,000–3,500 lines).

---

## (B) The chosen target

**Milestone target (the deliverable of this plan): the single-window estimate**, exponent `1 − (2σ₁−1)²/(2σ₁)` (route report §(c), "θ_A"). It uses one approximate-formula length N ≈ T on the one window [3, T+1] — exactly the receipted shape of `zeta_approx_sharp_segment` and of the J6–J8 bookkeeping — so the assembly is a re-parametrization of `count_le_meanSquare'`, not a new argument.

```lean
/-- Zero-density with a power saving, single-window form (Carlson's method, weaker exponent).
Near the line (δ → 0) the saving is 4δ²/(1+2δ) ≈ 4δ², i.e. essentially Carlson's. -/
theorem Zeta23.Density.density_single_window {σ₁ δ : ℝ}
    (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      (NRight δ T : ℝ) ≤ C * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3
```

(`σ₁ < 1` is implied by `σ₁ − 1/2 < δ ≤ 1/2`; for δ ≥ 1/2 the count is 0 by `NRight_eq_zero_of_half_le`, so the hypothesis `hδ` costs nothing.) Numerics: σ₁ = 3/4 → T^{5/6}; σ₁ = 0.9 → T^{0.644}; σ₁ = 1/2 + δ → T^{1 − 4δ²/(1+2δ)}.

**Stretch target (Stage 5, same lemma chain re-parametrized dyadically): Carlson's theorem.**

```lean
theorem Zeta23.Density.carlson_density {σ₁ δ : ℝ}
    (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      (NRight δ T : ℝ) ≤ C * T ^ (4 * σ₁ * (1 - σ₁)) * (1 + Real.log T) ^ 3

/-- MNF-facing corollary over `NOff`, via `NOff_eq_right_add_left` + `NLeft_eq_NRight`
(`Zeta23/BohrLandau.lean:20,35`). -/
theorem Zeta23.Density.offLine_density {δ σ₁ : ℝ}
    (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      (MNF.RH.NOff δ 0 T : ℝ) ≤ C * T ^ (4 * σ₁ * (1 - σ₁)) * (1 + Real.log T) ^ 3
```

Why these exponents and not better: the route report shows (i) the disc method loses only absolute constants and a (log T)^{1/2} against Littlewood's lemma, never an exponent (geometric factor `2·hwin·log(Rout/rin) ≥ Δ^{3/2}/3`, Δ := δ − (σ₁ − 1/2)); (ii) the balance diagonal `T·X^{1−2σ₁}` vs off-diagonal `(TX)^{2−2σ₁}` vs centre `T/X` gives Carlson's `4σ₁(1−σ₁)` at X = T^{2σ₁−1} *only* with N ≈ t per dyadic window; with one N ≈ T the main term N^{1−s}/(s−1)·M_X is large at small t, the cross term costs the factor `X^{1−σ₁}T^{−(2σ₁−1)/2}`, and the balance moves to X = T^{(2σ₁−1)/(2σ₁)}, exponent `1 − (2σ₁−1)²/(2σ₁)`. (iii) A linear saving `1 − c(σ−1/2)` (Ingham) needs the fourth moment on the half-line, which is not on the tree; the plan cannot and does not promise it.

Comparator shape: statements quote no theorem as a term; all auxiliary objects (`Mx`, `fz`, `cm`, `dX`, `Leps`, `NSigma`) are definitions, and since the density challenge runs with `definition_names: []` their bodies are compared, so the challenge must mirror them module by module — keep them minimal and freeze them once Stage 0 compiles (memory note: "Comparator definition-body pitfall").

---

## (C) Dependency DAG

Status key: **available** (exact tree/Mathlib name) · **to-prove** (est. lines / agent-hours / risk) · **blocked-by**. Hours are for one agent with the tree compiled; "risk" is the chance the lemma needs a different shape, not that it is false.

### Definitions (Stage 0, file `Density/Defs.lean`, ~60 lines, 1 h)

```lean
namespace Zeta23.Density
open Finset Complex MeasureTheory Metric
open scoped ArithmeticFunction.Moebius

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
```

### Stage 0 — eight independent packages (all parallel; nothing depends on anything new)

**C. Analyticity and the centre bound** (`Density/Centre.lean`)

| id | statement | status |
|---|---|---|
| C1 | `theorem analyticOnNhd_Mx (X : ℕ) : AnalyticOnNhd ℂ (Mx X) Set.univ` | to-prove, 40 / 2 h / low. Finite sum; `(n:ℂ)^(-s) = cexp (-s * log n)` for `n ≥ 1` (`Complex.cpow_def_of_ne_zero`), `analyticOnNhd_cexp.comp`, `Finset.analyticOnNhd_sum`. |
| C1' | `theorem analyticOnNhd_fz {X : ℕ} {S : Set ℂ} (hS : (1:ℂ) ∉ S) : AnalyticOnNhd ℂ (fz X) S` and `theorem continuousOn_fz {X : ℕ} {U : Set ℂ} (hU : (1:ℂ) ∉ U) : ContinuousOn (fz X) U` | to-prove, 20 / 1 h / low. `Zeta23.RvM.analyticOnNhd_riemannZeta hS` (`RvM/ZetaGrowth.lean:43`) `.mul (C1.mono …)`. |
| C2a | `theorem tail_inv_sq_le {X : ℕ} (hX : 1 ≤ X) : ∑' n : ℕ, (if X < n then 1 / (n:ℝ) ^ 2 else 0) ≤ 1 / X` | to-prove, 60 / 3 h / low. Telescoping `1/n² ≤ 1/(n−1) − 1/n`; `summable_of_nonneg_of_le`, `tsum_le_of_sum_le`. |
| C2b | `theorem fz_sub_one_eq {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 1 < s.re) : fz X s - 1 = -(riemannZeta s * ∑' n : ℕ, (if X < n then ((μ n : ℤ) : ℂ) * (n:ℂ) ^ (-s) else 0))` | to-prove, 120 / 6 h / **medium** (LSeries API). `LSeries_zeta_mul_Lseries_moebius` (`Mathlib/NumberTheory/LSeries/Dirichlet.lean:293`), `LSeries_zeta_eq_riemannZeta` (:280), `LSeriesSummable_moebius_iff` (:71), split `LSeries ↗μ s` as `Σ_{n≤X} + tail` (`sum_add_tsum_nat_add`/`Summable.sum_add_tsum_compl`), `LSeries.term` unfolding `if n = 0 then 0 else f n / n^s`. |
| C2c | `theorem norm_fz_sub_one_le {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 2 ≤ s.re) : ‖fz X s - 1‖ ≤ Real.pi ^ 2 / 6 * (1 / X)` | to-prove, 50 / 2 h / low. `Zeta23.RvM.norm_riemannZeta_le_of_two_le_re` (`RvM/ZetaGrowth.lean:227`), `abs_moebius_le_one`, `‖n^{-s}‖ = n^{-Re s} ≤ n^{-2}`, C2a. |
| C2d | `theorem fz_lower_two {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : (1/2 : ℝ) ≤ ‖fz X (2 + t * I)‖` · `theorem neg_log_norm_fz_two_le {X : ℕ} (hX : 4 ≤ X) (t : ℝ) : -Real.log ‖fz X (2 + t * I)‖ ≤ Real.pi ^ 2 / (3 * X)` · `theorem log_norm_fz_le_of_two_le_re {X : ℕ} (hX : 4 ≤ X) {s : ℂ} (hs : 2 ≤ s.re) : Real.log ‖fz X s‖ ≤ Real.pi ^ 2 / (6 * X)` · `theorem norm_sq_fz_le_of_two_le_re … : ‖fz X s‖ ^ 2 ≤ 1 + Real.pi ^ 2 / (2 * X)` | to-prove, 80 / 3 h / low. `π²/24 < 0.412`; `−log(1−x) ≤ 2x` on [0,1/2] via `Real.log_le_sub_one_of_pos` on `1/(1−x)`; `log(1+x) ≤ x`. |

**P. The product polynomial** (`Density/Product.lean`)

| id | statement | status |
|---|---|---|
| P1 | `theorem S_mul_Mx_eq (N X : ℕ) (s : ℂ) : BLClosure.S N s * Mx X s = ∑ m ∈ Icc 1 (N * X), ((cm N X m : ℤ) : ℂ) * (m : ℂ) ^ (-s)` | to-prove, 200 / 8 h / **medium** (Finset reindexing). `Finset.sum_mul_sum`, `Finset.sum_product`, `Finset.sum_fiberwise` on `(n,d) ↦ n*d`, `Complex.mul_cpow_ofReal_nonneg` (`Pow/Complex.lean:186`) for `(d:ℂ)^(-s) * (n:ℂ)^(-s) = ((d*n:ℕ):ℂ)^(-s)`, `Nat.mem_divisors`, `Nat.div_mul_cancel`. `BLClosure.S` is `BohrLandauClosure.lean:72`. |
| P2 | `theorem cm_eq_of_le {N X m : ℕ} (hXN : X ≤ N) (hm : m ≤ X) : cm N X m = if m = 1 then 1 else 0` | to-prove, 60 / 3 h / low. For `d ∣ m`: `d ≤ m ≤ X`, `m / d ≤ m ≤ N`, so `cm = Σ_{d ∣ m} μ d`; then the verified rewrite `← ArithmeticFunction.coe_zeta_mul_apply, coe_zeta_mul_moebius, one_apply` (inventory §3; `Moebius.lean:172`). `m = 0`: `Nat.divisors 0 = ∅`. |
| P3 | `theorem abs_cm_le (N X m : ℕ) : (|cm N X m| : ℝ) ≤ dX X m` | to-prove, 40 / 2 h / low. `Finset.abs_sum_le_sum_abs`, `abs_moebius_le_one`, `Finset.sum_le_card_nsmul`. |

**E. The divisor-sum bound — the one new piece of mathematics** (`Density/DivisorSum.lean`)

| id | statement | status |
|---|---|---|
| E1a | `theorem card_filter_dvd_dvd_le (Y d₁ d₂ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : (((Icc 1 Y).filter (fun m => d₁ ∣ m ∧ d₂ ∣ m)).card : ℝ) ≤ Y * Nat.gcd d₁ d₂ / (d₁ * d₂)` | to-prove, 70 / 3 h / low. Filter equals `{m ∈ Ioc 0 Y ∣ lcm d₁ d₂ ∣ m}` (`lcm_dvd_iff`, `Mathlib/Algebra/GCDMonoid/Basic.lean:755` / `Nat.lcm_dvd_iff`), card `= Y / lcm` (`Nat.Ioc_filter_dvd_card_eq_div`, `Data/Nat/Factorization/Basic.lean:534`), `Nat.cast_div_le`, `Nat.gcd_mul_lcm`. |
| E1b | `theorem gcd_le_sum_dvd (d₁ d₂ : ℕ) (h₁ : 0 < d₁) : (Nat.gcd d₁ d₂ : ℝ) ≤ ∑ g ∈ d₁.divisors.filter (· ∣ d₂), (g : ℝ)` | to-prove, 25 / 1 h / low. `gcd` is a term of a sum of nonnegatives (`Finset.single_le_sum`, `Nat.gcd_dvd_left/right`). This replaces the (g, e₁, e₂) reparametrization of the route report: no injectivity argument needed. |
| E1c | `theorem sum_div_of_dvd_le (X g : ℕ) (hg : 0 < g) : ∑ d ∈ (Icc 1 X).filter (g ∣ ·), (1 / (d : ℝ)) ≤ (1 / g) * (1 + Real.log X)` | to-prove, 60 / 3 h / low-medium. Image of `e ↦ g * e`, `e ∈ Icc 1 X` (`Finset.sum_le_sum_of_subset_of_nonneg` + `Finset.sum_image`), then `M1.sum_inv_le` (`BohrLandauPartial.lean:226`). |
| E1d | `theorem sum_gcd_div_le (X : ℕ) : ∑ d₁ ∈ Icc 1 X, ∑ d₂ ∈ Icc 1 X, (Nat.gcd d₁ d₂ : ℝ) / (d₁ * d₂) ≤ (1 + Real.log X) ^ 3` | to-prove, 90 / 4 h / medium. E1b, swap `Σ_{d₁,d₂} Σ_{g∣d₁, g∣d₂}` to `Σ_{g ≤ X} g · (Σ_{d ≤ X, g∣d} 1/d)²` (`Finset.sum_comm`, `Finset.sum_filter`), E1c, `M1.sum_inv_le` once more. |
| **E1** | `theorem sum_dX_sq_le (X Y : ℕ) : ∑ m ∈ Icc 1 Y, (dX X m : ℝ) ^ 2 ≤ Y * (1 + Real.log X) ^ 3` | to-prove, 80 / 4 h / medium. `dX X m ^ 2 = Σ_{d₁ ≤ X, d₁∣m} Σ_{d₂ ≤ X, d₂∣m} 1` (`Finset.card_eq_sum_ones`, `sq`, `Finset.sum_mul_sum`), `Finset.sum_comm`, E1a, E1d. **Note the log is in X, not Y**: the saving depends only on the mollifier length. |

**D. Partial-summation lemmas, generic weights** (`Density/Abel.lean`)

| id | statement | status |
|---|---|---|
| D0 | `theorem sum_mul_le_of_partial_sums {w g : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L) (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) (hg : ∀ m, 0 ≤ g m) (hanti : Antitone g) (M : ℕ) : ∑ m ∈ Icc 1 M, w m * g m ≤ L * ∑ m ∈ Icc 1 M, g m` | to-prove, 120 / 6 h / medium. Abel: `Finset.sum_Ioc_by_parts` (`Algebra/BigOperators/Module.lean:47`) or direct induction on M with `W(M) ≤ M L`. |
| D0' | tail version: same hypotheses, `∑ m ∈ Ioc X M, w m * g m ≤ L * ((X + 1) * g (X + 1) + ∑ m ∈ Ioc X M, g m)` | to-prove, 60 / 3 h / medium (same proof, shifted start). |
| D1 | `theorem tail_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L) (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) {X M : ℕ} (hX : 1 ≤ X) : ∑ m ∈ Ioc X M, w m * (m : ℝ) ^ (-2 * σ) ≤ (2 + 1 / (2 * σ - 1)) * L * (X : ℝ) ^ (1 - 2 * σ)` | to-prove, 100 / 5 h / medium. D0' with `g m = m^{-2σ}` (antitone: `Real.rpow_le_rpow_of_exponent_nonpos`), `Σ_{m > X} m^{-2σ} ≤ X^{1−2σ}/(2σ−1)` via `AntitoneOn.sum_le_integral_Ico` (`Analysis/SumIntegralComparisons.lean:117`) + `integral_rpow`; `(X+1)^{1−2σ} ≤ X^{1−2σ}`. (Fallback if the integral comparison fights: dyadic blocks `(2^k X, 2^{k+1} X]` as in the route report, constant `2/(1−2^{1−2σ})`.) |
| D2 | `theorem weight_sum_le {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {L : ℝ} (hL : 0 ≤ L) (hW : ∀ Y : ℕ, ∑ m ∈ Icc 1 Y, w m ≤ Y * L) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {M : ℕ} (hM : 1 ≤ M) : ∑ m ∈ Icc 1 M, ((m : ℝ) + 1) * (w m * (m : ℝ) ^ (-2 * σ)) ≤ (2 + 2 / (2 - 2 * σ)) * L * (M : ℝ) ^ (2 - 2 * σ)` | to-prove, 80 / 4 h / low-medium. D0 with `g m = (m+1) m^{-2σ}` (antitone for σ > 1/2; ≤ `2 m^{1−2σ}`), then `M1.sum_Icc_rpow_le` (`BohrLandauPartial.lean:329`, a = 1−2σ ∈ (−1, 0]). |

**G1/G3. The ε-majorant, generic f** (`Density/Majorant.lean`)

| id | statement | status |
|---|---|---|
| G1a | `theorem log_norm_le_Leps {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℂ) {z : ℂ} (hz : f z ≠ 0) : Real.log ‖f z‖ ≤ Leps ε f z` | to-prove, 20 / 1 h / low. (`Real.log 0 = 0` is why `hz` is needed; cf. `log_norm_le_Lz :1447`, which has `1 +` and needs no `hz`.) |
| G1b | `theorem concaveOn_half_log_add {ε : ℝ} (hε : 0 < ε) : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (1/2) * Real.log (ε ^ 2 + x))` | to-prove, 30 / 1 h / low. Pattern `concaveOn_half_log_one_add :1472` (`Real.strictConcaveOn_log_Ioi.concaveOn.comp_affineMap`-style). |
| G1c | `theorem segment_average_Leps_le {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℂ) (σ a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hf : IntervalIntegrable (fun t => ‖f ((σ:ℂ) + t * I)‖ ^ 2) volume a (a + ℓ)) (hL : IntervalIntegrable (fun t => Leps ε f ((σ:ℂ) + t * I)) volume a (a + ℓ)) : ∫ t in a..(a + ℓ), Leps ε f ((σ:ℂ) + t * I) ≤ ℓ * ((1/2) * Real.log (ε ^ 2 + (1/ℓ) * ∫ t in a..(a + ℓ), ‖f ((σ:ℂ) + t * I)‖ ^ 2))` | to-prove, 120 / 6 h / **medium**. `ConcaveOn.le_map_average` (`Analysis/Convex/Integral.lean:141`) with `μ = volume.restrict (Ioc a (a+ℓ))`, `average_eq_integral`, `intervalIntegral.integral_of_le`. This is the step at which the receipted proof (`:1718-1723`, `Lz_le_half_sq`) threw the logarithm away; here it is kept. |
| G1d | `theorem half_log_le_half {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) : (1/2) * Real.log (ε ^ 2 + (1 + x)) ≤ (1/2) * (ε ^ 2 + x)` | to-prove, 10 / 0.5 h / low. `Real.log_le_sub_one_of_pos`. |
| G3 | `theorem circleAverage_log_norm_le_Leps {ε : ℝ} (hε : 0 < ε) (c : ℂ) {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (h₁f : AnalyticOnNhd ℂ f (closedBall c R)) (h₂f : f c ≠ 0) : circleAverage (fun z => Real.log ‖f z‖) c R ≤ circleAverage (Leps ε f) c R` | to-prove, 120 / 6 h / medium. **available inputs**: `AnalyticOnNhd.ae_circleMap_ne_zero` (`JensenDisc.lean:121`), `MeromorphicOn.circleIntegrable_log_norm` (`Mathlib/Analysis/SpecialFunctions/Integrability/LogMeromorphic.lean:132`), `intervalIntegral.integral_mono_ae` (`IntervalIntegral/Basic.lean:1429`), continuity of `Leps ε f` on the sphere (`Real.continuous_log` off 0, `ε² + ‖f‖² > 0`). Pattern: the `_of_ae` proof at `JensenDisc.lean:63-116`. |

**G4. ζ-multiplicities are counted by the divisor of ζ·M** (`Density/Divisor.lean`)

| id | statement | status |
|---|---|---|
| G4a | `theorem Mx_ne_zero_of_le_re {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : 3 ≤ s.re) : Mx X s ≠ 0` | to-prove, 50 / 2 h / low. `‖Mx − 1‖ ≤ Σ_{n ≥ 2} n^{-3} < 1` (`M1.sum_Icc_rpow_le_tsum :720` or crude `Σ_{n≥2} 1/n³ ≤ Σ 1/(n(n−1)) ... ≤ 1/2`). |
| G4b | `theorem analyticOrderAt_Mx_ne_top {X : ℕ} (hX : 1 ≤ X) (z : ℂ) : analyticOrderAt (Mx X) z ≠ ⊤` | to-prove, 60 / 3 h / medium. `analyticOrderAt_eq_top` ⟹ `Mx =ᶠ[𝓝 z] 0` ⟹ (identity theorem on ℂ, `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `Analysis/Analytic/IsolatedZeros.lean:214`, `isPreconnected_univ`) `Mx X = 0` everywhere, contradicting G4a. |
| G4 | `theorem zeta_order_le_divisor_fz {X : ℕ} (hX : 1 ≤ X) {c : ℂ} {r : ℝ} (h1 : (1:ℂ) ∉ closedBall c r) {ρ : ℂ} (hρ : ρ ∈ closedBall c r) : (zeta_order ρ : ℤ) ≤ MeromorphicOn.divisor (fz X) (closedBall c r) ρ` | to-prove, 100 / 5 h / medium. `AnalyticOnNhd.divisor_apply` (`Meromorphic/Divisor.lean:71`), `analyticOrderAt_mul` (`Analytic/Order.lean:497`), `Zeta23.analyticOrderAt_riemannZeta_ne_top` (`Statement/Seam.lean:40`), G4b, `ENat.map`/`untop₀` arithmetic; the tree's equality `divisor_riemannZeta_eq_int :1156` is the pattern. (Alternative: `MeromorphicOn.divisor_mul :310` + `AnalyticOnNhd.divisor_nonneg :177`.) |
| G4' | `theorem finset_sum_zeta_order_le_finsum_divisor_fz {X : ℕ} (hX : 1 ≤ X) {c : ℂ} {r : ℝ} (h1 : (1:ℂ) ∉ closedBall c r) (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall c r) : (∑ ρ ∈ S, (zeta_order ρ : ℝ)) ≤ ∑ᶠ u, (MeromorphicOn.divisor (fz X) (closedBall c r) u : ℝ)` | to-prove, 60 / 3 h / low. Pattern copy of `finset_sum_zeta_order_le_finsum_divisor :1377` with `≤` from G4 in place of `=`; needs `(divisor (fz X) …).finite_support`/nonnegativity (`AnalyticOnNhd.divisor_nonneg`). |

**G8. Geometry** (`Density/Geometry.lean`)

| id | statement | status |
|---|---|---|
| G8 | `theorem geom_lower {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) : (δ - (σ₁ - 1 / 2)) ^ (3/2 : ℝ) / 3 ≤ 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ)` | to-prove, 80 / 4 h / low. With Δ := δ − (σ₁ − 1/2): `rin = (3/2 − δ) + Δ/2`, `rin² − (3/2−δ)² = Δ(3/2 − δ) + Δ²/4 ≥ Δ` (as 3/2 − δ ≥ 1), so `2·hwin ≥ √Δ`; `log(Rout/rin) = log(1 + (Δ/2)/rin) ≥ (Δ/2)/Rout ≥ Δ/3` via `Real.log_le_sub_one_of_pos` on the reciprocal; **available**: `geom_facts :1290` for positivity. |
| G8' | `theorem hwin_le_one … : hwin σ₁ δ ≤ 1` and `Rout σ₁ < 3/2` | **available** inside `geom_facts :1290-1293`. |

**W1/W3. Window translation; pointwise mollifier bound** (`Density/Window.lean`)

| id | statement | status |
|---|---|---|
| W1 | `theorem integral_window_eq (c : ℕ → ℂ) (M : ℕ) (σ a ℓ : ℝ) : ∫ t in a..(a + ℓ), ‖∑ m ∈ Icc 1 M, c m * (m : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 = ∫ u in (0:ℝ)..ℓ, ‖∑ m ∈ Icc 1 M, (c m * (((m:ℝ) ^ (-σ) : ℝ) : ℂ) * (m : ℂ) ^ (-(a : ℂ) * I)) * (m : ℂ) ^ (-(u : ℂ) * I)‖ ^ 2` | to-prove, 80 / 4 h / low. `intervalIntegral.integral_comp_add_right` (`IntervalIntegral/Basic.lean:954`), `M1.cpow_neg_add_eq :210`, `Complex.cpow_add` (base ≠ 0), `mul_assoc`. |
| W3 | `theorem norm_Mx_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) {s : ℂ} (hs : σ₁ ≤ s.re) (X : ℕ) : ‖Mx X s‖ ≤ 1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)` | to-prove, 60 / 3 h / low. `norm_sum_le`, `abs_moebius_le_one`, `Complex.norm_natCast_cpow_of_pos`, `M1.sum_Icc_rpow_le :329` with a = −σ₁. |
| W0 | `theorem norm_add_sq_le_eta (a b : ℂ) {η : ℝ} (hη : 0 < η) : ‖a + b‖ ^ 2 ≤ (1 + η) * ‖a‖ ^ 2 + (1 + 1 / η) * ‖b‖ ^ 2` | to-prove, 20 / 1 h / low. `norm_add_le`, `nlinarith` (pattern `M2.norm_add4_sq_le :399`). |

**A2. Exponent arithmetic** (`Density/Exponent.lean`; pure real inequalities, independent of everything, can start on day 1)

| id | statement | status |
|---|---|---|
| A2 | `theorem exponent_single {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) : ∃ K T₀ : ℝ, 0 < K ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (4 ≤ ⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊) ∧ (⌊T ^ ((2 * σ₁ - 1) / (2 * σ₁))⌋₊ ≤ ⌈T⌉₊ + 5) ∧ Esingle σ₁ T ≤ K * (1 + Real.log T) ^ 3 * T ^ (-((2 * σ₁ - 1) ^ 2 / (2 * σ₁)))` where `Esingle σ₁ T` is the explicit real expression `η·(1+E₀) + E₀ + (1+1/η)·(2 M̄²(N^{2−2σ₁}/3 + C_G² N^{−2σ₁} T))/T + 1/X + …` with `X = ⌊T^{(2σ₁−1)/(2σ₁)}⌋₊`, `N = ⌈T⌉₊ + 5`, `η = E₀ = (2 + 1/(2σ₁−1))·(1+log X)³·X^{1−2σ₁} + 26(2 + 2/(2−2σ₁))(1+log X)³ (NX)^{2−2σ₁}/T`, `M̄ = 1 + X^{1−σ₁}/(1−σ₁)`, and `C_G` a free nonnegative parameter | to-prove, 250 / 12 h / **medium-high** (tedious `rpow` algebra; the one place an off-by-a-power mistake hides). Write `Esingle` as a `def` **only inside the scratch file**; in the final module inline it (definition bodies are compared by Comparator). Sanity values: σ₁ = 3/4 → X ≈ T^{1/3}, E₀ ≈ T^{−1/6}, cross ≈ T^{−1/6}, total exponent −1/6, count T^{5/6}. |

### Stage 1 — first combinations (four parallel workers; each blocked only by Stage 0 items named)

| id | statement | status / blocked-by |
|---|---|---|
| W2 | `theorem meanSquare_prodPoly {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ) {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : ∫ t in a..(a + ℓ), ‖BLClosure.S N ((σ : ℂ) + t * I) * Mx X ((σ : ℂ) + t * I)‖ ^ 2 ≤ ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁)) + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁)` | to-prove, 220 / 10 h / medium. **blocked-by** P1, P2, P3, E1, D1, D2, W1. **available**: `M1.dirichlet_meanSquare_le` (`BohrLandauPartial.lean:172`, `T·Σ‖a‖² + 26·Σ(n+1)‖a‖²`, no hypothesis on T). Proof: P1 + W1, apply M1 with `a_m = cm·m^{-σ}·m^{-ia}` (`‖a_m‖² = cm² m^{-2σ}`), split `Icc 1 (NX)` at X (P2: coefficients `[m=1]` below X, so the diagonal is `1 + Σ_{X<m≤NX} cm² m^{-2σ}`), P3 + E1 give `w m := dX X m ^ 2` with `L = (1+log X)³`, monotonicity `m^{-2σ} ≤ m^{-2σ₁}` (`Real.rpow_le_rpow_of_exponent_ge`), D1 for the tail, D2 for the weighted sum. |
| W5 | `theorem meanSquare_B_window {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ) {N X : ℕ} (hN : 1 ≤ N) {a ℓ : ℝ} (ha : 1 ≤ a) (hℓ : 0 ≤ ℓ) {C_G : ℝ} (hCG : 0 ≤ C_G) (hE : ∀ t ∈ Set.Icc a (a + ℓ), ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I) - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ)) : ∫ t in a..(a + ℓ), ‖(riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I)) * Mx X ((σ:ℂ) + t * I)‖ ^ 2 ≤ 2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ)` | to-prove, 180 / 8 h / medium. **blocked-by** W3. **available**: `M2.norm_P_le :454` (`‖N^{1−s}/(s−1)‖ ≤ N^{1−σ₁}/t`), `∫_a^{a+ℓ} t^{-2} ≤ 1/a` (pattern `integral_bound_abstract :885`'s `4A/t²` term), `(x+y)² ≤ 2x² + 2y²`, integrability of the integrand (continuity off `s = 1`, pattern `intervalIntegrable_normSq_zeta_segment :1682`). |
| G5 | `theorem count_finset_le_fz {X : ℕ} (hX : 4 ≤ X) {t r R : ℝ} (ht : 3 ≤ t) (hr : 0 < r) (hrR : r < R) (hR : R < 3) (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ ρ ∈ closedBall (2 + t * I) r) : (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (R / r) ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) R + Real.pi ^ 2 / (3 * X)` | to-prove, 100 / 4 h / low. **blocked-by** C1', C2d, G4'. **available**: `sum_divisor_mul_log_le` (`JensenDisc.lean:8`), `one_notMem_closedBall_two_add :1342`; pattern `count_disc_le :1367` → `count_finset_le :1406` with `log 3` → `π²/(3X)`. |
| G5' | `theorem count_window_le_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ) (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) : (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ) ≤ circleAverage (fun z => Real.log ‖fz X z‖) (2 + t * I) (Rout σ₁) + Real.pi ^ 2 / (3 * X)` | to-prove, 40 / 2 h / low. **blocked-by** G5. Pattern copy of `count_window_le :1543` (`geom_facts` supplies the inclusion). |
| G6 | `theorem integral_circleAverage_Leps_eq_swap {X : ℕ} {ε : ℝ} (hε : 0 < ε) {R a ℓ : ℝ} (hR0 : 0 ≤ R) (hR : R < 3) (ha : 3 ≤ a) (hℓ : 0 ≤ ℓ) : ∫ t in a..(a + ℓ), circleAverage (Leps ε (fz X)) (2 + t * I) R = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ∫ t in a..(a + ℓ), Leps ε (fz X) (circleMap (2 + t * I) R θ)` plus the four integrability lemmas it needs (`continuousOn_Leps_circleMap`, `integrableOn_Leps_circleMap_prod`, `intervalIntegrable_circleAverage_Leps`, `intervalIntegrable_Leps_segment`) and `intervalIntegrable_normSq_fz_segment` | to-prove, 220 / 9 h / medium (Fubini bookkeeping). **blocked-by** C1'. Pattern copy of `:1605-1652` and `:1676-1682` with `Lz` → `Leps ε (fz X)` (the proofs there are "continuity on {z ≠ 1}" + `continuousOn_Lz`-style; `Leps ε f` is continuous where f is since `ε² + ‖f‖² > 0`). |

### Stage 2 — the two spines (two parallel workers)

| id | statement | status / blocked-by |
|---|---|---|
| W4 | `theorem meanSquare_fz_window {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h1' : σ₁ < 1) (hσ : σ₁ ≤ σ) {N X : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) {a ℓ : ℝ} (ha : 1 ≤ a) (hℓ : 0 ≤ ℓ) {C_G : ℝ} (hCG : 0 ≤ C_G) (hE : ∀ t ∈ Set.Icc a (a + ℓ), ‖riemannZeta ((σ:ℂ) + t * I) - BLClosure.S N ((σ:ℂ) + t * I) - (N:ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ C_G * (N:ℝ) ^ (-σ)) {η : ℝ} (hη : 0 < η) : ∫ t in a..(a + ℓ), ‖fz X ((σ : ℂ) + t * I)‖ ^ 2 ≤ (1 + η) * (ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log X) ^ 3 * (X : ℝ) ^ (1 - 2 * σ₁)) + 26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log X) ^ 3 * ((N * X : ℕ) : ℝ) ^ (2 - 2 * σ₁)) + (1 + 1 / η) * (2 * (1 + (X : ℝ) ^ (1 - σ₁) / (1 - σ₁)) ^ 2 * ((N : ℝ) ^ (2 - 2 * σ₁) / a + C_G ^ 2 * (N : ℝ) ^ (-2 * σ₁) * ℓ))` | to-prove, 150 / 6 h / low-medium. **blocked-by** W2, W5, W0. `fz = S·Mx + (ζ − S)·Mx` (ring), W0 pointwise, `intervalIntegral.integral_mono_on` + linearity. The approximate formula enters only as the hypothesis `hE`, discharged at the call site by `BLClosure.zeta_approx_sharp` (`BohrLandauClosure.lean:954`, σ₀ := σ₁, needs `t ≤ N`, `σ ≤ 2`, `0 ≤ t`). Taking `η` free (not pointwise `η = q`) is what makes the same lemma serve both the single-window and the dyadic assembly; both use `η := X^{1−2σ₁}`-sized values. |
| G7 | `theorem count_le_integral_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 4 ≤ T) : 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4) ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage (Leps ε (fz X)) (2 + t * I) (Rout σ₁) + Real.pi ^ 2 / (3 * X))` | to-prove, 320 / 12 h / **medium-high** (longest copy; the step-function/indicator integration). **blocked-by** G5', G3, C1'. Pattern copy of `count_le_integral :1767-1840` with: `count_window_le` → G5', `circleAverage_log_le_Lz :1568` → G3 (needs `fz X (2+tI) ≠ 0`, from C2d), `log 3` → `π²/(3X)`. **available** unchanged: `NRight_sub_eq :1129`, `NRight_add :1117`, `MNF_zerosIn_union :1103`, `zerosIn_finite` (`MNF/RH/Counting.lean:96`), the step-function lemmas in `:1767-1840`. For the Carlson stage the same proof is re-run with `NSigma (1/2+δ) T₁ T₂` and window `[T₁ − 1, T₂ + 1]`; plan it with the window parameters abstracted from the start (`T₁ T₂` with `4 ≤ T₁ ≤ T₂`) and derive the `NRight` form, so Stage 5 costs nothing here. |

### Stage 3 — the count-to-mean-square bridge (one worker)

| id | statement | status / blocked-by |
|---|---|---|
| A0 | `theorem count_le_meanSquare_fz {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) {X : ℕ} (hX : 4 ≤ X) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 4 ≤ T) {E : ℝ} (hE0 : 0 ≤ E) (hMS : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 2 → ∀ a : ℝ, 3 / 2 ≤ a → a ≤ 9 / 2 → ∫ t in a..(a + T), ‖fz X ((σ:ℂ) + t * I)‖ ^ 2 ≤ T * (1 + E)) : 2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4) ≤ T * ((1/2) * (ε ^ 2 + E) + Real.pi ^ 2 / X)` | to-prove, 260 / 12 h / medium. **blocked-by** G7, G6, G1c, G1d, C2d. Proof: G7, G6 (swap), for each θ the inner integral is along `Re = 2 + Rout·cos θ ∈ [σ₁, 4 − σ₁]`, `Im = t + Rout·sin θ`, so the t-window is `[3 + Rout sin θ, T + 3 + Rout sin θ]`, `a ∈ [3/2, 9/2]`; if `Re ≤ 2` use `hMS` + G1c + G1d; if `Re > 2` use `Leps ≤ ½(ε² + ‖fz‖²) ≤ ½ε² + π²/(4X)` pointwise from C2d's `‖fz‖² ≤ 1 + π²/(2X)` (so no mean square is needed on those lines — the σ > 2 extension `meanSquare_hyp_extend :1900` is not needed); `π²/(3X) + π²/(4X) < π²/X`. Then `(2π)⁻¹ ∫₀^{2π}` of a constant. This is the analogue of `count_le_meanSquare' :1862`. |

### Stage 4 — the single-window assembly (one worker)

| id | statement | status / blocked-by |
|---|---|---|
| A1 | `density_single_window` as in (B) | to-prove, 220 / 10 h / medium. **blocked-by** A0, W4, A2, G8. Proof: fix `T₀, K` from A2; for `T ≤ T₀` use `NRight_mono :1137` and `T^{…} ≥ 1`; for `T ≥ T₀` set `X := ⌊T^{(2σ₁−1)/(2σ₁)}⌋₊`, `N := ⌈T⌉₊ + 5`, `ε := X^{-1/2}` (so `ε² = 1/X`), `η := E₀`, obtain `C_G` from `BLClosure.zeta_approx_sharp (σ₀ := σ₁)`, discharge `hMS` of A0 by W4 (window `[a, a+T]` with `a ≥ 3/2 ≥ 1`, `a + T ≤ T + 9/2 ≤ N`; `σ ≤ 2` and `0 ≤ t` hold), A2 bounds the resulting `E`, G8 divides by the geometric factor, `NRight δ 4` is absorbed into `C`. **available**: `zeta_approx_sharp :954`, `NRight_mono`, `NRight_sub_eq`. |

### Stage 5 — Carlson (stretch; two workers, after Stage 4 compiles)

| id | statement | status / blocked-by |
|---|---|---|
| A3 | `theorem exponent_dyadic {σ₁ : ℝ} (h1 : 1/2 < σ₁) (h1' : σ₁ < 1) : ∃ K U₀ : ℝ, 0 < K ∧ 8 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → (4 ≤ ⌊U ^ (2 * σ₁ - 1)⌋₊) ∧ (⌊U ^ (2 * σ₁ - 1)⌋₊ ≤ ⌈2 * U⌉₊ + 5) ∧ Edyadic σ₁ U ≤ K * (1 + Real.log U) ^ 3 * U ^ (-(2 * σ₁ - 1) ^ 2)` with `Edyadic` the W4 right-hand side divided by `ℓ = U + 2` at `X = ⌊U^{2σ₁−1}⌋₊`, `N = ⌈2U⌉₊ + 5`, `a ≥ U/2`, `η = X^{1−2σ₁}` | to-prove, 220 / 10 h / medium-high. Independent of A2 (parallel). Check: `(1+1/η)·2M̄²N^{2−2σ₁}/a / ℓ ≈ X·U^{2−2σ₁}/U² = U^{2σ₁−1+2−2σ₁−2} = U^{−1} ≤ U^{−(2σ₁−1)²}` ✓; diagonal `X^{1−2σ₁} ≈ U^{−(2σ₁−1)²}` ✓; off-diagonal `(NX)^{2−2σ₁}/U ≈ U^{(2σ₁)(2−2σ₁)−1} = U^{−(2σ₁−1)²}` ✓; centre `1/X ≈ U^{−(2σ₁−1)} ≤ U^{−(2σ₁−1)²}` ✓. |
| A4 | `theorem count_dyadic_le {σ₁ δ : ℝ} … {U : ℝ} (hU : U₀ ≤ U) : (NSigma (1/2 + δ) U (2 * U) : ℝ) ≤ K' * (1 + Real.log U) ^ 3 * U ^ (4 * σ₁ * (1 - σ₁))` | to-prove, 200 / 8 h / medium. **blocked-by** the window-parametrized form of G7/A0 (planned above), W4, A3, G8; `1 − (2σ₁−1)² = 4σ₁(1−σ₁)`. |
| A5 | `theorem NSigma_dyadic_sum {σ : ℝ} {T U₀ : ℝ} (h : 2 * U₀ ≤ T) : (NSigma σ 0 T : ℝ) ≤ NSigma σ 0 (2 * U₀) + ∑ k ∈ range ⌈Real.logb 2 (T / U₀)⌉₊, NSigma σ (T / 2 ^ (k+1)) (T / 2 ^ k)` and `theorem NRight_eq_NSigma (δ T : ℝ) : NRight δ T = NSigma (1/2 + δ) 0 T` (set-builder `δ ≤ ρ.re − 1/2 ↔ 1/2 + δ ≤ ρ.re`, `linarith`) | to-prove, 160 / 7 h / medium. Pattern `NRight_add :1117` / `MNF_zerosIn_union :1103` (disjoint unions of `zerosIn`, `finsum_mem_union`, `zerosIn_finite`). |
| A6 | `carlson_density`, `offLine_density` as in (B) | to-prove, 120 / 5 h / low-medium. **blocked-by** A4, A5. Geometric sum `Σ_k (T/2^k)^θ ≤ T^θ/(1 − 2^{−θ})`, `(1 + log(T/2^k))³ ≤ (1 + log T)³`; **available**: `NOff_eq_right_add_left` (`Zeta23/BohrLandau.lean:20`), `NLeft_eq_NRight` (:35). |

### Totals

Stage 0 ≈ 1,250 lines / 60 h (8 parallel workers → ~8 h wall-clock); Stage 1 ≈ 760 / 33 h (4 workers); Stage 2 ≈ 470 / 18 h (2 workers); Stage 3 ≈ 260 / 12 h; Stage 4 ≈ 220 / 10 h; **M1 deliverable ≈ 2,950 lines / 135 agent-hours, ~5 stages of wall-clock**. Stage 5 adds ≈ 700 lines / 30 h. This is the size of `BohrLandauPartial.lean` + half of `BohrLandauClosure.lean`, as the route report estimated.

Already-receipted inputs consumed without change (names re-grepped today): `M1.dirichlet_meanSquare_le :172`, `M1.sum_inv_le :226`, `M1.sum_Icc_rpow_le :329`, `M1.cpow_neg_add_eq :210`, `M2.norm_P_le :454`, `M2.norm_add4_sq_le :399`, `geom_facts :1290`, `one_notMem_closedBall_two_add :1342`, `finset_sum_zeta_order_le_finsum_divisor :1377` (pattern), `count_le_integral :1767` (pattern), `NRight_* :1093-1137`, `rightHalf_of_meanSquareUnif :1933` (pattern), `sum_divisor_mul_log_le` / `AnalyticOnNhd.ae_circleMap_ne_zero` / `AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq` (`JensenDisc.lean:8,121,159`), `BLClosure.S :72`, `BLClosure.zeta_approx_sharp :954`, `Zeta23.RvM.analyticOnNhd_riemannZeta :43`, `Zeta23.RvM.norm_riemannZeta_le_of_two_le_re :227`, `Zeta23.analyticOrderAt_riemannZeta_ne_top` (`Statement/Seam.lean:40`), `MNF.RH.zerosIn_finite`, `NOff_eq_right_add_left`, `NLeft_eq_NRight`. Mathlib: `moebius_mul_coe_zeta`/`coe_zeta_mul_moebius`, `abs_moebius_le_one`, `LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta`, `LSeriesSummable_moebius_iff`, `zeta_eq_tsum_one_div_nat_cpow`, `Nat.Ioc_filter_dvd_card_eq_div`, `Nat.gcd_mul_lcm`, `lcm_dvd_iff`, `Finset.sum_Ioc_by_parts`, `AntitoneOn.sum_le_integral_Ico`, `ConcaveOn.le_map_average`, `intervalIntegral.integral_comp_add_right`, `intervalIntegral.integral_mono_ae`, `MeromorphicOn.circleIntegrable_log_norm`, `AnalyticOnNhd.divisor_apply`, `AnalyticOnNhd.divisor_nonneg`, `MeromorphicOn.divisor_mul`, `analyticOrderAt_mul`, `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `Complex.mul_cpow_ofReal_nonneg`, `Real.log_le_sub_one_of_pos`.

Not on the tree and not needed: Littlewood's lemma, `d(n) ≪ n^ε`, `Σ d(n)²` asymptotics, any fourth moment, large sieve, Halász–Montgomery.

---

## (D) Order of attack

**The single best first lemma: E1 (`sum_dX_sq_le`), via E1a–E1d.** Reasons: it is the only lemma in the DAG that is new mathematics rather than a re-instantiation; it is the only one whose *shape* could change the exponent (if it could only be proved as `Y·X^{c}` instead of `Y·(1+log X)³`, there would be no power saving at all); it depends on nothing new (only `M1.sum_inv_le` and Mathlib divisor/gcd lemmas); it compiles standalone in seconds (no analysis, no integrals); and its sub-lemmas E1a–E1d are each under 100 lines, so a first agent can land a kernel-checked E1 on day 1 and the rest of the plan then rests on receipted material plus bookkeeping.

Then, in this order (parallelism noted):

1. **Day 1, in parallel with E1**: Defs; A2 (exponent arithmetic — the second-riskiest item, pure real analysis, needs nothing; finding an algebra mistake here early is cheap, late is expensive); C2b (the only Mathlib-API risk: `LSeries` manipulation); G4b (identity-theorem detour).
2. **Days 1–2**: the rest of Stage 0 (C1, C1', C2a/c/d, P1–P3, D0–D2, G1a–d, G3, G4, G4', G8, W0, W1, W3): eight independent workers; no coordination needed beyond the frozen `Defs.lean`.
3. **Day 3**: Stage 1 (W2, W5, G5/G5', G6). W2 is the first point where the *size* of the saving is visible in Lean: check its right-hand side at σ₁ = 3/4 against the route report by hand before continuing.
4. **Day 4**: Stage 2 (W4; G7 with window parameters `T₁ T₂` abstracted).
5. **Day 5**: Stage 3 (A0), then Stage 4 (A1 = `density_single_window`). Run `#print axioms` (expect `[propext, Classical.choice, Quot.sound]`); write the challenge (same statements, `sorry` bodies, definitions mirrored verbatim) and the Comparator config in the shape of `MNFChallengesD/Density.json`.
6. **Stretch**: Stage 5 (A3 ∥ A5, then A4, A6) for `carlson_density` and the `NOff` corollary.

Before claiming novelty in any write-up: read Lewko's Palomar entries PALOMAR-2026-10-11-000010 and -10-21-000008 (`DEPOSIT_MAP.md` §8); if either contains a Carlson-type exponent, the claim is "at this pin, on this trust base, over MNF's two-sided `NOff`", not "first".

---

## (E) Success and failure criteria

**Stage 0.**
- Success: every item compiles with `lake env lean`, `#print axioms` shows no `sorryAx`; E1's constant is `(1 + log X)³` with *X*, not `Y`, inside the log; A2's `K, T₀` are explicit `∃`-witnesses and the exponent on the right is literally `-((2σ₁−1)²/(2σ₁))`.
- Shows the route cannot deliver the exponent: E1 provable only with a power `X^{c}` or `Y^{c}` (c > 0) in place of the logs — then the diagonal excess `Σ_{m>X} cm² m^{−2σ}` is not `X^{1−2σ+o(1)}` and no choice of X gives a power saving. (Expected: no; the classical `Σ 1/lcm ≪ log³` argument is complete as written in E1a–E1d.) A2 failing to close means an algebra error in the plan's balance, not a route failure; the fix is to recompute, and the check value is σ₁ = 3/4 → total exponent −1/6.
- Not a problem (costs only logs/constants): D1/D2 needing the dyadic-block constants instead of the Abel ones; C2b needing `X ≥ 8` instead of `4`; P1 needing `Icc 1 (N*X)` replaced by `range (N*X+1)`.

**Stage 1.**
- Success: W2's bound is of the stated form with the `1 +` isolated (the mean square of the product polynomial over a window of length ℓ is `ℓ·(1 + o(1))` for X → ∞) — this is the whole content of the mollifier; G5 has `π²/(3X)`, not `log 3`, at the centre.
- Failure signal: if W2 can only be proved with the `1` replaced by a constant `> 1` (e.g. because P2's `[m = 1]` identification needs `X ≤ N` in a form the window bookkeeping cannot supply), then `E_max` does not tend to 0 and the count is O(T) again — exactly the Bohr–Landau situation the plan is meant to leave. Diagnosis: check `cm_eq_of_le` is being applied for all `m ≤ X` and that `X ≤ N` holds in the assembly (it does: X ≈ T^{<1} ≤ N ≈ T).

**Stage 2.**
- Success: W4 with a *free* η; G7 with `Leps` and `π²/(3X)`; both re-use `count_le_integral`'s step-function machinery untouched.
- Failure signal: if G3 (a.e. comparison `log‖f‖ ≤ Leps` on circles) cannot be obtained because the zeros of f on the circle are not a.e. avoided — impossible given the receipted `ae_circleMap_ne_zero` for analytic f with `f c ≠ 0`, which is supplied by C2d. If G7 forces the window `[3, T+3]` to depend on X or ε, the Fubini copy has gone wrong, not the route.

**Stage 3.**
- Success: A0 has the shape `T·(½(ε² + E) + π²/X)`, with E the *window* mean-square excess, and no `log(1 + …)` left unsimplified. This is the quantitative replacement of `count_le_meanSquare' :1862`.
- Failure signal: an `O(1)` term surviving on the right (e.g. `½ log 2`) — that is the `Lz` majorant sneaking back; the fix is G1c/G1d, not more analysis.

**Stage 4 (deliverable).**
- Success: `density_single_window` kernel-checked with axioms `[propext, Classical.choice, Quot.sound]`; a Comparator PASS against a challenge with the same statement; the exponent `1 − (2σ₁−1)²/(2σ₁)`, which at σ₁ = 3/4 is 5/6 and as σ₁ → 1/2⁺ is `1 − 4δ²/(1+2δ)`.
- Sanity bounds on the assembled exponent (any violation is a bookkeeping bug, since this route provably cannot do better): the saving must be ≤ Carlson's `(2σ₁−1)²` (so exponent ≥ `4σ₁(1−σ₁)`); a fortiori ≥ Ingham's `3(1−σ₁)/(2−σ₁)` (at 3/4: 0.6) and ≥ the density hypothesis `2(1−σ₁)` (at 3/4: 0.5). A `sorry`-free proof claiming an exponent below Ingham's would be a research result and should be assumed wrong until the proof is read line by line.
- A linear saving `1 − c·(σ₁ − 1/2)` cannot appear: the method's saving is quadratic in `σ₁ − 1/2`.

**Stage 5 (stretch).**
- Success: `carlson_density` with exponent `4σ₁(1−σ₁)` and `offLine_density` over `MNF.RH.NOff`; same axioms; the log power stays 3.
- Failure signal: if the dyadic exponent arithmetic (A3) needs `X ≤ N` to fail for σ₁ > (1+√5)/4 ≈ 0.809 — it does not, since `X = ⌊U^{2σ₁−1}⌋₊ ≤ U ≤ N`; a failure there is an algebra error. If the dyadic sum A5 cannot be expressed with `NSigma` because `zerosIn`'s half-open convention `(T₁, T₂]` mismatches the tiling, use `T/2^{k+1} < Im ρ ≤ T/2^k` exactly, which is `zerosIn`'s convention.

**What success does and does not mean for the strip.** Success is the statement "for every δ > 0 the number of zeros with Re ρ ≥ 1/2 + δ and 0 < Im ρ ≤ T is at most C·T^{1−c(δ)}(1+log T)³, c(δ) > 0 explicit", kernel-checked over the same `NRight`/`NOff` that `MNF.RH.BohrLandau` uses. It leaves `SpectralGapHyp Δ` exactly where it was, it does not exclude a single zero, and by the five-question test of the landscape memo (§5) it uses `μ` only to buy a power. It is the honest unit of progress these tools afford.
