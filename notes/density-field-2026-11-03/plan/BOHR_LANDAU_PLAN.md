# BOHR_LANDAU_PLAN — removing `meanSquare_strip` and `rightHalfBound_of_meanSquare`

Target file (read-only): `/home/joeyxyxyz/mnf-stageB/z23work2/formal-math/zeta23/Zeta23/BohrLandau.lean`
(`namespace Zeta23.BL`, `open Set Complex`, `open MNF.RH`). All new work goes in scratch files that
`import Zeta23.BohrLandau` (plus `Zeta23.FromPNTPlus.ZetaBounds`, `Zeta23.RvM.ZetaGrowth`,
`Zeta23.RvM.LocalCount`, `Zeta23.MV.Final`, `Zeta23.RvM.Backlund`, all built). Every Lean name below
is either quoted from the three reports or was verified by `grep` against this checkout; names I
could not verify are marked **(verify)**.

## 0. Decisions (read this first)

1. **Route B (Jensen on discs centred `2 + t*I`, averaged in `t`), not route A (Littlewood).**
   Littlewood's lemma is in neither Mathlib nor the tree; every other ingredient of route B is
   present (Mathlib `AnalyticOnNhd.circleAverage_log_norm`, `ConcaveOn.le_map_set_average`,
   `intervalIntegral_intervalIntegral_swap`; tree `zeta_lower_bound_two`,
   `analyticOnNhd_riemannZeta`, `zerosIn_finite`).

2. **The hypothesis `h : ZetaMeanSquare` of `rightHalfBound_of_meanSquare` is unusable for route B**
   (pointwise in σ, lower limit 0, see W1/W2 of the route report). Route B needs the *uniform*
   mean square `∫ t in 1..T, ‖ζ(σ+it)‖² ≤ C·T` for all σ ≥ σ₁ at once. The mean-square proof below is
   uniform for free, so the plan is: prove `MeanSquareUnifFrom σ₁` outright (a theorem, not a
   hypothesis), derive `rightHalfBound_of_meanSquare h := rightHalf_of_unif …` (ignoring `h`; this is
   a legitimate proof of the sorried statement) and derive `meanSquare_strip` from the same uniform
   theorem plus a `[0,1]` patch and the σ = 1 junk-value case. **Recommend to Joey**: restate
   `ZetaMeanSquare` as the uniform, lower-limit-1 version (`ZetaMeanSquareUnif` of the route report)
   in a later tarball; nothing in this plan depends on that happening.

3. **What the naive tools reach, honestly.** With the tree's approximate formula
   (`Zeta0EqZeta` + `ZetaBnd_aux1b`, error `‖s‖N^{-σ}/σ`) and the sorry-free weighted Hilbert
   inequality `Zeta23.MV.mvDiag_thirteen : MVDiag 13`, the uniform mean square closes for
   **σ ≥ σ₁ > 2/3** (MV removes the log, so 2/3 itself is reachable as `σ₁ ≥ 2/3`; the `P_N` term
   `N^{1-s}/(1-s)` forces `σ₁ ≥ 2/3` independently, so 2/3 is the true naive limit, not 3/4; 3/4 is
   what one gets with the lazy choice `N = ⌊T⌋₊^2`). Through route B this gives
   **`RightHalfBound` for every δ > 1/6**, i.e. `NRight δ T = O(T)` for δ > 1/6 — partial result (i).
   Partial result (ii) is `MeanSquareUnifFrom σ₁` for every σ₁ > 2/3 (and `meanSquare_strip`
   verbatim for 2/3 < σ ≤ 1).

4. **Closing the full statements (every δ > 0, every σ > 1/2) is blocked by exactly one deep tool**:
   the approximate formula with *bounded* error for `N ≥ t + 3` (Titchmarsh Thm 4.11 made elementary,
   route report §C (C1)): second Euler–Maclaurin step + Fourier series of the periodic Bernoulli
   polynomial `B̃₂` (Mathlib has `hasSum_one_div_nat_pow_mul_cos`) + a first-derivative test for
   oscillatory integrals (not in Mathlib). Everything else in the DAG is independent of it, so the
   order of attack below gets (i) and (ii) first and leaves C1 as the last, isolated, high-risk block.

5. **Neither sorry can be removed *inside the given file* by us** (the zeta23 tree is read-only for
   this work). Deliverables are scratch files whose final theorems have *exactly* the sorried
   statements, ready to be pasted by Joey.

## 1. Statement-level facts that shape the plan

- **(W1) σ = 1 is vacuous.** `‖ζ(1+it)‖² ~ t⁻²` near `t = 0` is not integrable on `(0,T)`; Lean's
  `intervalIntegral` of a non-integrable function is `0` (`intervalIntegral.integral_undef`, verified,
  `IntervalIntegral/Basic.lean:709`), so `meanSquare_strip` at σ = 1 holds with any `C ≥ 0`. We prove
  non-integrability with `not_intervalIntegrable_of_sub_inv_isBigO_punctured`
  (`Analysis/SpecialFunctions/NonIntegrable.lean:173`, verified) and `riemannZeta_eq_inv_sub_add`.
- **(W2) lower limit 0 vs 1 for 1/2 < σ < 1.** `∫_0^1 ‖ζ(σ+it)‖² ≤ (9/2 + 1/(1-σ))²` from
  `Zeta23.RvM.norm_riemannZeta_le_of_re_pos`; fine for the pointwise target, not uniform as σ → 1⁻.
  All uniform statements use lower limit 1 (route B only needs lower limit ≥ 3/2).
- **δ ≥ 1/2 is trivial**: `NRight δ T = 0` because nontrivial zeros have `re < 1`.
- The whole DAG never uses the local notations `ζ`, `ζ'`, `ζ₀` of `ZetaBounds.lean`; write
  `riemannZeta`, `riemannZeta0`. A new file using `lemma` needs `set_option lang.lemmaCmd true`.

## 2. The DAG

```
                     meanSquare_strip (SORRY 1a)        rightHalfBound_of_meanSquare (SORRY 2)
                        │          │                                  │
                 [σ=1]  M4b        M5 ◄── M4a ([0,1] patch)           J10 (full, every δ>0)
                                   │                                  │
                                   └──────────► M7 ZetaMeanSquareUnif ◄┘    ← BLOCKED by M6 (C1)
                                                  ▲
   partial (ii): M3 MeanSquareUnifFrom σ₁ (σ₁ > 2/3) ──────► J9 partial (i): RightHalfBound for δ > 1/6
        ▲    ▲    ▲                                                ▲
       M1   M2   M3a                                               J8 rightHalf_of_meanSquareUnif (generic in σ₁)
   (MV mean   (approx.  (p-sum                                      ▲   ▲   ▲   ▲
    value)    formula   bounds)                                    J5  J6  J7  J0
     ▲          pieces)                                             ▲   (Fubini)(concavity)(δ≥1/2 trivial)
    M1a-d                                                        J3,J4
                                                                   ▲
                                                                 J1,J2 (Jensen refactor, divisor glue)
```

Two independent halves: **M** (mean square; analysis of Dirichlet polynomials) and **J**
(Jensen/covering; complex analysis + measure theory). They meet only in J8/J9 and can be worked in
parallel.

## 3. Lemmas, with Lean statements, status, estimates

Conventions: `s := (σ:ℂ) + t * I`; estimates are "lines / focused hours / risk"; risk = chance the
statement needs reshaping or the proof hits a Lean-side obstacle (low / medium / high).

### Part M — the mean square

#### M1. Dirichlet-polynomial mean value via the weighted Hilbert inequality

**M1a** (twist integral) — to-prove, 25 lines / 1 h / low.
```lean
theorem integral_exp_neg_mul_I {A B lam : ℝ} (hl : lam ≠ 0) :
    ∫ t in A..B, Complex.exp (-(t * lam) * I)
      = (Complex.exp (-(B * lam) * I) - Complex.exp (-(A * lam) * I)) / (-(lam : ℂ) * I)
```
From `integral_exp_mul_complex` (`Analysis/SpecialFunctions/Integrals/Basic.lean:242`) with
`c := -(lam:ℂ) * I` after rewriting the exponent as `c * t` (`ring_nf`/`push_cast`).

**M1b** (expand the square) — to-prove, 30 lines / 1 h / low.
```lean
theorem norm_sum_sq_eq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ n ∈ s, f n‖ ^ 2 = (∑ m ∈ s, ∑ n ∈ s, f m * (starRingEnd ℂ) (f n)).re
```
`RCLike.mul_conj` (`‖z‖^2` form, `Analysis/RCLike/Basic.lean:465`) or `Complex.mul_conj` +
`Complex.normSq_eq_norm_sq` **(verify)**, `Finset.sum_mul_sum`
(`Algebra/BigOperators/Ring/Finset.lean:62`), `map_sum`.

**M1c** (log gaps) — to-prove, 25 lines / 1 h / low.
```lean
theorem log_nat_gap {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) :
    1 / ((n : ℝ) + 1) ≤ |Real.log n - Real.log m|
```
Cases `m < n` / `m > n`; `Real.log_div`, `Real.one_sub_inv_le_log_of_pos` (`Log/Basic.lean:312`):
`log(n/m) ≥ 1 - m/n ≥ 1/n ≥ 1/(n+1)` resp. `log(m/n) ≥ 1 - n/m ≥ 1/m ≥ 1/(n+1)`.

**M1d** (the mean value, MV form) — to-prove, 150–220 lines / 6–10 h / medium. The key lemma of part M.
```lean
theorem dirichlet_meanSquare_le (a : ℕ → ℂ) (N : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    ∫ t in A..B, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(t * Real.log n) * I)‖ ^ 2
      ≤ (B - A) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + 26 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) + 1) * ‖a n‖ ^ 2
```
Proof sketch: M1b; `intervalIntegral.integral_finsetSum` twice (integrands continuous,
`Continuous.intervalIntegrable`); diagonal terms integrate to `(B-A)‖a n‖²`; off-diagonal term
`(m,n)` integrates by M1a to `i·(x_m(B)·conj(x_n(B)) − x_m(A)·conj(x_n(A)))/(log m − log n)` with
`x_n(u) := a n * exp(-(u log n) I)`, `‖x_n(u)‖ = ‖a n‖`; the two double sums are exactly the shape of
`Zeta23.MVDiag` (`Zeta23/MV.lean:52`) with `ι := Fin N` (or `↥(Finset.Icc 1 N)`),
`freq i := Real.log (i+1)`, `δ i := 1/((i+1)+1)`, injectivity from `Real.log_injOn_pos` **(verify)**
or strict monotonicity, gaps from M1c; apply `Zeta23.MV.mvDiag_thirteen` twice: `2·13 = 26`.
Take real parts at the end (`Complex.re_le_norm`-type lemma **(verify)**: `(z).re ≤ ‖z‖`).
Risk is bookkeeping (`Fin N` ↔ `Finset.Icc 1 N` reindexing via `Finset.sum_bij`/`Fin.sum_univ_eq_sum_range`).

#### M2. The approximate formula, as the tree gives it, specialised to vertical lines

**M2a** — available: `Zeta0EqZeta {N} (N_pos : 0 < N) {s} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
riemannZeta0 N s = riemannZeta s` and the definition `riemannZeta0` (`ZetaBounds.lean:520`). At
`s = σ + t*I` with `t ≥ 1` the hypotheses are `by simp; linarith` and `fun h => by have := congrArg
Complex.im h; simp at this; linarith`.

**M2b** (term bounds, `t ≥ 1`, `σ ≥ σ₁`) — to-prove, 60 lines / 2 h / low.
```lean
theorem approx_terms_bound {σ₁ σ t : ℝ} (h1 : 1/2 < σ₁) (hσ : σ₁ ≤ σ) (ht : 1 ≤ t)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(-(N : ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I))‖ ≤ (N : ℝ) ^ (1 - σ₁) / t ∧
    ‖(-(N : ℂ) ^ (-((σ:ℂ) + t * I))) / 2‖ ≤ 1 / 2 ∧
    ‖((σ:ℂ) + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ:ℂ) + t * I) + 1)‖
      ≤ (1 + 1 / σ₁) * t * (N : ℝ) ^ (-σ₁)
```
Ingredients: `Complex.norm_natCast_cpow_of_pos`, `‖1 - s‖ ≥ |Im| = t` (`Complex.abs_im_le_norm`
**(verify)**), `Real.rpow_le_rpow_of_exponent_le`/`Real.rpow_le_one` for `N^{1-σ} ≤ N^{1-σ₁}`,
`ZetaBnd_aux1b N hN (σpos)` for the tail, `‖s‖ ≤ σ + t`, and `(σ+t)/σ ≤ 1 + t/σ₁ ≤ (1+1/σ₁) t`.

**M2c** (four-term square) — to-prove, 10 lines / 0.5 h / low.
```lean
theorem norm_add4_sq_le (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2)
```
`norm_add_le` three times then `nlinarith [sq_nonneg (‖a‖-‖b‖), …]`.

**M2d** (the Dirichlet polynomial of `riemannZeta0` in M1d's shape) — to-prove, 50 lines / 2 h / medium.
```lean
theorem range_sum_eq_twist {σ t : ℝ} (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)
      = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-σ) : ℝ) * Complex.exp (-(t * Real.log n) * I)
```
`n = 0` term vanishes (`Complex.zero_cpow`, `s ≠ 0`), `Finset.range_eq_Ico` + shift, then
`Complex.cpow_def_of_ne_zero` (`Pow/Complex.lean:38`), `Complex.ofReal_log`, `Complex.exp_add`,
`Complex.ofReal_cpow`/`Real.rpow_neg`. (Alternative: prove M1d directly for `1/(n:ℂ)^s` summands —
same work moved.)

#### M3. The uniform mean square with the naive error (partial result (ii))

**M3a** (partial sums of `n^a`, `-1 < a ≤ 0`) — to-prove, 50 lines / 2 h / medium.
```lean
theorem sum_Icc_rpow_le {N : ℕ} {a : ℝ} (ha : -1 < a) (ha' : a ≤ 0) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ a ≤ 1 + (N : ℝ) ^ (a + 1) / (a + 1)
```
`AntitoneOn.sum_le_integral_Ico`/`AntitoneOn.sum_le_integral` (`SumIntegralComparisons.lean:104/117`)
with `f x := x ^ a` antitone on `Icc 1 N` (`Real.rpow_le_rpow_of_nonpos` **(verify)**; else via
`Real.rpow_le_rpow_left_iff`-style monotonicity), `integral_rpow` (`Integrals/Basic.lean:147`).
Also the diagonal: `∑ n ∈ Icc 1 N, (n:ℝ)^(-(2σ₁)) ≤ ∑' n, 1/(n:ℝ)^(2σ₁)` via
`Real.summable_one_div_nat_rpow.2` and `sum_le_tsum` **(verify exact name)**.

**M3b** (parametric mean square, `N` free) — to-prove, 120 lines / 5 h / medium.
```lean
theorem meanSquare_param {σ₁ σ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) (hσ : σ₁ ≤ σ)
    (N : ℕ) (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤
      4 * ( T * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * σ₁))
            + 52 * (1 + (N : ℝ) ^ (2 - 2 * σ₁) / (2 - 2 * σ₁))
            + (N : ℝ) ^ (2 - 2 * σ₁)
            + T / 4
            + 3 * T ^ 3 * (N : ℝ) ^ (-(2 * σ₁)) )
```
Proof: pointwise `t ∈ [1,T]`: M2a + M2d rewrite ζ as `D + P + Q + sJ`; M2c; integrate each square:
`∫|D|²` by M1d with `a n := n^{-σ}` (`‖a n‖² = n^{-2σ} ≤ n^{-2σ₁}`, `(n+1)n^{-2σ₁} ≤ 2 n^{1-2σ₁}`, M3a
with `a := 1-2σ₁`), `∫|P|² ≤ N^{2-2σ₁} ∫_1^T t^{-2} ≤ N^{2-2σ₁}`, `∫|Q|² ≤ T/4`,
`∫|sJ|² ≤ (1+1/σ₁)² N^{-2σ₁} ∫_1^T t² ≤ 9 N^{-2σ₁} T³/3`. Integral monotonicity:
`intervalIntegral.integral_mono_on` (`:1432`), integrability from continuity
(`ContinuousOn.intervalIntegrable`, ζ continuous on the segment: `differentiableAt_riemannZeta`).
Every bound is monotone in σ ≥ σ₁ — this is where uniformity comes from.

**M3c** (choose `N`; the partial result (ii)) — to-prove, 60 lines / 3 h / medium.
```lean
def MeanSquareUnifFrom (σ₁ : ℝ) : Prop := ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
    ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T

theorem meanSquareUnif_naive {σ₁ : ℝ} (h1 : 2 / 3 ≤ σ₁) (h2 : σ₁ < 1) : MeanSquareUnifFrom σ₁
```
Take `N := ⌊T ^ (1/σ₁)⌋₊ + 1`, so `T^{1/σ₁} ≤ N ≤ 2 T^{1/σ₁}` (`Nat.floor_le`, `Nat.lt_floor_add_one`,
`Real.rpow_natCast`, `Real.rpow_mul`); then `N^{-2σ₁} ≤ T^{-2}` kills the `T³` term and
`N^{2-2σ₁} ≤ 4 T^{(2-2σ₁)/σ₁} ≤ 4T` because `(2-2σ₁)/σ₁ ≤ 1 ⇔ σ₁ ≥ 2/3`. Constant
`C = 4(Z(2σ₁) + 52(1 + 4/(2-2σ₁)) + 4 + 1/4 + 3)`. (Lazy variant: `N := ⌊T⌋₊^2`, no `rpow` in `N`,
gives the same with `h1 : 3/4 ≤ σ₁`; ~20 lines cheaper; the planner recommends going straight to 2/3.)

#### M4. The two patches for the sorried statement

**M4a** (`[0,1]`, σ < 1) — to-prove, 40 lines / 1.5 h / low.
```lean
theorem meanSquare_zero_one {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    ∫ t in (0:ℝ)..1, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (9 / 2 + 1 / (1 - σ)) ^ 2
```
`Zeta23.RvM.norm_riemannZeta_le_of_re_pos` (`‖ζ s‖ ≤ 1/2 + 1/‖1-s‖ + ‖s‖/s.re`), `‖1 - s‖ ≥ 1-σ`,
`‖s‖ ≤ 2`, `σ > 1/2`; `intervalIntegral.norm_integral_le_of_norm_le_const` exactly as in
`meanSquare_gt_one`.

**M4b** (σ = 1 is junk) — to-prove, 50 lines / 3 h / medium.
```lean
theorem not_intervalIntegrable_zeta_one_sq {T : ℝ} (hT : 0 < T) :
    ¬ IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 + t * I)‖ ^ 2) volume 0 T
theorem meanSquare_one : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta ((1:ℝ) + t * I)‖ ^ 2 ≤ C * T
```
`riemannZeta_eq_inv_sub_add : riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s`, `differentiable_riemannZeta₀`
(`Harmonic/ZetaAsymp.lean:551`) gives `‖riemannZeta₀(1+it)‖ ≤ M` near 0, so
`‖ζ(1+it)‖² ≥ (1/|t| - M)² ≥ (4|t|)⁻¹` for small `t`, hence `(t - 0)⁻¹ =O[𝓝[≠] 0] ‖ζ(1+it)‖²` and
`not_intervalIntegrable_of_sub_inv_isBigO_punctured`; then `intervalIntegral.integral_undef` gives
`∫ = 0 ≤ 0 * T`. Watch the cast: the sorried statement has `(σ:ℂ)` with `σ = 1`, i.e. `((1:ℝ):ℂ)`.

**M5** (assembly for the pointwise, lower-limit-0 target) — to-prove, 40 lines / 1.5 h / low.
```lean
theorem meanSquare_strip_of_unif {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1)
    (hU : MeanSquareUnifFrom σ) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T
```
`intervalIntegral.integral_add_adjacent_intervals` (`:1095`) at `1`, M4a + `hU σ le_rfl T hT`,
`C := (9/2 + 1/(1-σ))² + C_U`. Then the verbatim target:
```lean
theorem meanSquare_strip {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T
```
= `if σ = 1 then M4b else meanSquare_strip_of_unif _ _ (M7 σ)`. **With M3c instead of M7 this
closes only for 2/3 ≤ σ ≤ 1**; the strip 1/2 < σ < 2/3 is blocked by M6.

#### M6. (C1) Approximate formula with bounded error for `N ≥ t + 3` — BLOCKED-BY block

The single deep tool. Sub-lemmas (all to-prove; none present in Mathlib/tree — `grep EulerMaclaurin`
over Mathlib is empty; the tree has first-order Euler–Maclaurin only, `ZetaSum_aux1`,
`sum_eq_int_deriv`, `sum_eq_integral_add_integral_deriv`):

**M6a** (second Euler–Maclaurin step for the tail) — 200–300 lines / 15–25 h / high.
```lean
noncomputable def B2per (x : ℝ) : ℝ := Int.fract x ^ 2 - Int.fract x + 1 / 6
theorem tail_second_step {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
      = s / 12 * (N : ℂ) ^ (-s - 1)
        - s * (s + 1) / 2 * ∫ x in Ioi (N : ℝ), (B2per x : ℂ) * (x : ℂ) ^ (-s - 2)
```
Route: on each unit interval `[k, k+1]` `B2per` is the polynomial `(x-k)² - (x-k) + 1/6` with
derivative `2(x-k) - 1 = -2(⌊x⌋ + 1/2 - x)`; integrate by parts on `[k,k+1]`
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `IntegrationByParts.lean:142`), telescope
(`B2per k = 1/6` at both ends), sum `k = N..M-1`, let `M → ∞`
(`MeasureTheory.intervalIntegral_tendsto_integral_Ioi`, `IntegralEqImproper.lean:658`; integrability
of both tails from `integrableOn_of_Zeta0_fun`-style arguments). This is the riskiest sub-lemma.

**M6b** (Fourier series of `B2per`) — 40 lines / 2 h / low-medium. Mathlib
`hasSum_one_div_nat_pow_mul_cos (hk : k ≠ 0) (hx : x ∈ Icc 0 1)` with `k = 1` gives
`HasSum (fun n => 1/(n:ℝ)^2 * cos(2π n x)) ((-1)^2 (2π)^2/2/2! · (bernoulli 2 poly).eval x)`; evaluate
`Polynomial.bernoulli 2 = X² - X + 1/6` (**verify** the available simp lemmas, e.g.
`Polynomial.bernoulli_two`-type) and extend from `Icc 0 1` to ℝ by periodicity (`Int.fract`).

**M6c** (first-derivative test) — 150–250 lines / 10–20 h / high.
```lean
theorem osc_integral_bound {N t σ : ℝ} (hN : t + 3 ≤ N) (ht : 0 ≤ t) (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k) :
    ‖∫ x in Ioi N, Complex.exp (((2 * π * k * x - t * Real.log x : ℝ) : ℂ) * I) * (x : ℂ) ^ (-(σ:ℂ) - 2)‖
      ≤ 2 * N ^ (-σ - 2) / (2 * π * k - 1)
```
(and the conjugate phase `-2πkx - t log x`). Phase derivative `2πk - t/x ≥ 2πk - 1` for `x ≥ N ≥ t`;
`g/φ' = x^{-σ-1}/(2πk x - t)` positive decreasing; one integration by parts on `[N, M]` then `M → ∞`.
Not in Mathlib; nothing in the tree.

**M6d** (swap `Σ_k` and `∫`, assemble) — 100 lines / 5 h / medium.
`MeasureTheory.integral_tsum_of_summable_integral_norm` (`DominatedConvergence.lean:111`) with the
dominating series `Σ_k k^{-2} N^{-σ-2}/(2k)`. Result:
```lean
theorem zeta_approx_bounded {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (ht : 0 ≤ t) {N : ℕ} (hN : t + 3 ≤ N) :
    ‖riemannZeta ((σ:ℂ) + t * I) - ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ ((σ:ℂ) + t * I)
        - (N : ℂ) ^ (1 - ((σ:ℂ) + t * I)) / (((σ:ℂ) + t * I) - 1)‖ ≤ 1
```

**M7** (full uniform mean square) — to-prove given M6, 80 lines / 4 h / medium.
```lean
theorem zetaMeanSquareUnif : ∀ σ₁ : ℝ, 1 / 2 < σ₁ → σ₁ < 1 → MeanSquareUnifFrom σ₁
```
Same proof as M3b/M3c with `N := ⌊T⌋₊ + 3` fixed on `[1,T]`, `‖sJ‖`-term replaced by `≤ 1`, so
`E_off ≤ 52(1 + (T+3)^{2-2σ₁}/(2-2σ₁)) = O(T)` for every σ₁ > 1/2 (`T^{2-2σ₁} ≤ T`). Also handles
σ ≥ 2 (where M6d's `σ ≤ 2` fails) by `Zeta23.RvM.norm_riemannZeta_le_of_two_le_re` (`‖ζ‖ ≤ π²/6`).

### Part J — Jensen on discs, averaged in `t` (route B)

**J0** (trivialities) — to-prove, 30 lines / 1 h / low.
```lean
theorem NRight_eq_zero_of_half_le {δ T : ℝ} (hδ : 1 / 2 ≤ δ) : NRight δ T = 0
theorem NRight_sub_eq {δ T : ℝ} (hT : 4 ≤ T) :
    (NRight δ T : ℝ) - NRight δ 4
      = ∑ᶠ ρ ∈ MNF.RH.zerosIn 4 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, (zeta_order ρ : ℝ)
```
First: the index set is empty (`is_nontrivial_zero ρ → ρ.re < 1`), `finsum_mem_empty`. Second:
`MNF.RH.zerosIn 0 T = zerosIn 0 4 ∪ zerosIn 4 T` (copy `Zeta23.zerosIn_union`, defeq sets), disjoint,
`finsum_mem_union` (already used in `NOff_eq_right_add_left`), `MNF.RH.zerosIn_finite`.

**J1** (Jensen counting inequality with the circle average retained) — to-prove, 40 lines / 2 h / low.
```lean
theorem AnalyticOnNhd.sum_divisor_mul_log_le {c : ℂ} {r R : ℝ} {f : ℂ → ℂ} (r_pos : 0 < r)
    (r_lt_R : r < R) (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) :
    (∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c r) u : ℝ)) * Real.log (R / r)
      ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
```
Literally the `calc` block of Mathlib's `AnalyticOnNhd.sum_divisor_le`
(`Analysis/Complex/JensenFormula.lean:390–440`, read above) with the `integral_bound` step deleted:
`h₁f.circleAverage_log_norm`, `finsum_le_finsum'`, `finsum_mul`,
`(divisor _ _).finiteSupport (isCompact_closedBall ..)`, `AnalyticOnNhd.divisor_apply`,
`h₁f.divisor_nonneg`; use `abs_of_pos` to match Mathlib's `|r|`, `|R|`.

**J2** (divisor of ζ = `zeta_order`) — to-prove, 25 lines / 1.5 h / low.
```lean
theorem divisor_riemannZeta_eq {c : ℂ} {r : ℝ} (h1 : (1 : ℂ) ∉ Metric.closedBall c r)
    {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall c r) :
    (MeromorphicOn.divisor riemannZeta (Metric.closedBall c r) ρ : ℝ) = (zeta_order ρ : ℝ)
```
`MeromorphicOn.AnalyticOnNhd.divisor_apply (Zeta23.RvM.analyticOnNhd_riemannZeta h1) hρ`,
`Zeta23.analyticOrderAt_riemannZeta_ne_top (hs : s ≠ 1)` (`Zeta23/Statement/Seam.lean:40`; MNF has
`MNF.RH.analyticOrderAt_riemannZeta_ne_top (hs : s.re < 1)`, `Core.lean:95`), then
`ENat.map_natCast` + `WithTop.untop₀_natCast` (or `Nat.cast_analyticOrderNatAt`); `zeta_order ρ` is
`(analyticOrderAt riemannZeta ρ).toNat` by `rfl`.

**J3** (geometry constants) — definitions + 30 lines / 1.5 h / low.
```lean
/-- outer radius, inner radius, half-window; valid for 1/2 < σ₁ < 1/2 + δ, δ ≤ 1/2 -/
noncomputable def Rout (σ₁ : ℝ) : ℝ := 2 - σ₁
noncomputable def rin (σ₁ δ : ℝ) : ℝ := (Rout σ₁ + (3 / 2 - δ)) / 2
noncomputable def hwin (σ₁ δ : ℝ) : ℝ := Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2
theorem geom_facts {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2) :
    0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧
    ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ →
      ρ ∈ Metric.closedBall (2 + t * I) (rin σ₁ δ)
```
Pure real arithmetic: `(2-β)² + (t-γ)² ≤ (3/2-δ)² + hwin² ≤ rin²`; `hwin² ≤ (9/4 - 1)/4 < 1`.
Also: `1 ∉ closedBall (2 + t*I) (Rout σ₁)` for `t ≥ 3` (`Im ≥ 3 - 3/2 > 0`), and
`closedBall (2+t*I) (Rout σ₁) ⊆ {s | σ₁ ≤ s.re}`.

**J4** (per-`t` count, log-average form) — to-prove, 90 lines / 5 h / medium.
```lean
theorem count_window_le {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {t : ℝ} (ht : 3 ≤ t) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, is_nontrivial_zero ρ ∧ δ ≤ ρ.re - 1 / 2 ∧ |t - ρ.im| ≤ hwin σ₁ δ) :
    (∑ ρ ∈ S, (zeta_order ρ : ℝ)) * Real.log (Rout σ₁ / rin σ₁ δ)
      ≤ Real.circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) (Rout σ₁) + Real.log 3
```
J1 at `c = 2 + t*I`, `f = riemannZeta` (`Zeta23.RvM.analyticOnNhd_riemannZeta`, `ζ(c) ≠ 0` from
`Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re`), `-log‖ζ c‖ ≤ log 3` from
`Zeta23.RvM.zeta_lower_bound_two`; `∑ ρ ∈ S ≤ ∑ᶠ u, divisor …` since `S ⊆ support` (J3, J2) and all
divisor values are `≥ 0` (`MeromorphicOn.AnalyticOnNhd.divisor_nonneg`):
`finsum_eq_sum_of_support_subset` + `Finset.sum_le_sum_of_subset_of_nonneg`.

**J5** (kill `log` at zeros; `L := ½ log(1+‖ζ‖²)`) — to-prove, 50 lines / 2.5 h / low-medium.
```lean
noncomputable def Lz (z : ℂ) : ℝ := Real.log (1 + ‖riemannZeta z‖ ^ 2) / 2
theorem Lz_nonneg (z : ℂ) : 0 ≤ Lz z
theorem log_norm_le_Lz (z : ℂ) : Real.log ‖riemannZeta z‖ ≤ Lz z
theorem continuousOn_Lz {U : Set ℂ} (hU : (1 : ℂ) ∉ U) : ContinuousOn Lz U
theorem circleAverage_log_le_Lz {t R : ℝ} (ht : 3 ≤ t) (hR : 0 < R) (hR' : R < 3 / 2) :
    Real.circleAverage (fun z => Real.log ‖riemannZeta z‖) (2 + t * I) R
      ≤ Real.circleAverage Lz (2 + t * I) R
```
`log x ≤ ½ log(1+x²)` for `x ≥ 0` (`x = 0`: `Real.log_zero`; else `Real.log_le_log` on `x² ≤ 1+x²` and
`Real.log_pow`/`Real.log_rpow`); `Real.circleAverage_mono` with
`MeromorphicOn.circleIntegrable_log_norm` and `ContinuousOn.circleIntegrable`.

**J6** (integrate the count over `t ∈ [3, T+3]`) — to-prove, 150 lines / 8 h / medium-high.
```lean
theorem count_le_integral {σ₁ δ : ℝ} (h1 : 1 / 2 < σ₁) (hδσ : σ₁ - 1 / 2 < δ) (hδ : δ ≤ 1 / 2)
    {T : ℝ} (hT : 4 ≤ T) :
    2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4)
      ≤ ∫ t in (3:ℝ)..(T + 3), (Real.circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3)
```
Let `Z := (zerosIn_finite 4 T).toFinset.filter (δ ≤ ·.re - 1/2)`; by J0 the left count is
`∑ ρ ∈ Z, zeta_order ρ`. For each `t`, J4+J5 with `S := Z.filter (|t - ·.im| ≤ hwin)` give
`∑ ρ ∈ Z, m(ρ) · indicator (Icc (ρ.im - h) (ρ.im + h)) 1 t · log(R/r) ≤ RHS(t)`. Integrate:
`intervalIntegral.integral_mono_on` (RHS integrable: `t ↦ circleAverage Lz (2+t*I) R` is continuous by
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` (`DominatedConvergence.lean:599`,
namespace verified) applied to `Real.circleAverage_def`; LHS: finite sum of step functions),
`intervalIntegral.integral_finsetSum`, and `∫_3^{T+3} indicator (Icc (γ-h) (γ+h)) 1 = 2h` because
`γ > 4 ≥ 3 + h` and `γ + h ≤ T + 1` (`intervalIntegral.integral_of_le`,
`MeasureTheory.integral_indicator`, `Real.volume_Icc`, `MeasureTheory.setIntegral_const`).
Main risk: finsum ↔ Finset ↔ filter bookkeeping; mitigate by stating J4 for a `Finset`.

**J7** (Fubini, shift, enlarge) — to-prove, 120 lines / 6 h / medium.
```lean
theorem integral_circleAverage_le {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {T : ℝ} (hT : 2 ≤ T) :
    ∫ t in (3:ℝ)..(T + 3), Real.circleAverage Lz (2 + t * I) (Rout σ₁)
      ≤ (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
          ∫ u in (1:ℝ)..(T + 5), Lz (((2 + Rout σ₁ * Real.cos θ : ℝ) : ℂ) + u * I)
```
`Real.circleAverage_def`, `circleMap c R θ = c + R * exp(θ I)` (`CircleMap.lean:31`), so
`circleMap (2+t*I) R θ = (2 + R cos θ) + (t + R sin θ) I` (`Complex.exp_mul_I`,
`Complex.ext_iff`); `intervalIntegral.integral_const_mul`;
`MeasureTheory.intervalIntegral_intervalIntegral_swap` (`Prod.lean:499`; integrability from
`ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)` via `continuousOn_Lz` on the
pole-free rectangle, then `IntegrableOn.mono_set` to `uIoc ×ˢ uIoc`);
`intervalIntegral.integral_comp_add_right` (`:954`) with `d = R sin θ`;
`intervalIntegral.integral_mono_interval` (`:1405`) with `Lz_nonneg` and
`[3 + R sin θ, T + 3 + R sin θ] ⊆ [1, T + 5]` (`R < 3/2`).

**J8'** (concavity on one vertical segment) — to-prove, 80 lines / 4 h / medium.
```lean
theorem integral_Lz_le {σ a b C : ℝ} (hab : a < b) (ha : 0 < a)
    (hms : ∫ u in a..b, ‖riemannZeta (σ + u * I)‖ ^ 2 ≤ C * (b - a)) :
    ∫ u in a..b, Lz (σ + u * I) ≤ (b - a) * Real.log (1 + C) / 2
```
`ConcaveOn.le_map_set_average` (`Convex/Integral.lean:188`) with `g := Real.log`, `s := Ici 1`
(`isClosed_Ici` **(verify)**, concavity `strictConcaveOn_log_Ioi.concaveOn.subset (fun x hx => by
linarith [mem_Ici.1 hx]) (convex_Ici 1)`, continuity `Real.continuousOn_log.mono`),
`t := Ioc a b` (`Real.volume_Ioc`), `f u := 1 + ‖ζ(σ+u*I)‖²` (continuous, `a > 0` keeps the pole out);
convert `⨍` with `MeasureTheory.setAverage_eq` and `intervalIntegral.integral_of_le`; finish with
`Real.log_le_log` and `(∫ 1 + ‖ζ‖²)/(b-a) ≤ 1 + C`.

**J8** (generic assembly, parametric in σ₁) — to-prove, 80 lines / 4 h / medium.
```lean
theorem rightHalf_of_meanSquareUnif {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1)
    (hms : MeanSquareUnifFrom σ₁) :
    ∀ δ : ℝ, σ₁ - 1 / 2 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T
```
WLOG `δ ≤ 1/2` (J0). For `T ≥ 4`: J6 → J7 → J8' for each θ with `a = 1`, `b = T+5`, `σ = 2 + R cos θ ≥ σ₁`,
`C := 2 C_ms` (since `C_ms (T+5) ≤ 2 C_ms (T+4)`); the θ-integral of a constant
(`intervalIntegral.integral_const`) returns `2π · (T+4) log(1+2C_ms)/2`, so
`2h log(R/r) (NRight δ T − NRight δ 4) ≤ (T+4) log(1+2C_ms)/2 + T log 3`; with `T + 4 ≤ 3T` and
`NRight δ 4 ≤ (NRight δ 4) T / 2`, the constant is
`C = NRight δ 4 / 2 + ((3/2) log(1 + 2 C_ms) + log 3) / (2 h log(R/r))`. For `2 ≤ T < 4`:
`NRight δ T ≤ NRight δ 4` (monotone in `T`, copy of `Zeta23.Ncount_mono`).

**J9** (partial result (i)) — to-prove, 25 lines / 1 h / low.
```lean
theorem rightHalf_gt_sixth : ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T
theorem bohrLandau_gt_sixth : ∀ δ : ℝ, 1 / 6 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T
```
`σ₁ := (2/3 + min (1/2 + δ) 1) / 2` satisfies `2/3 < σ₁ < 1` and `σ₁ - 1/2 < δ`; apply J8 with M3c.
Second from the first exactly as `bohrLandau_of_right` (`NOff_eq_right_add_left`, `NLeft_eq_NRight`).
This is the smallest δ₀ the naive tools allow: route B needs δ > σ₁ − 1/2 and the naive mean
square needs σ₁ ≥ 2/3, so δ₀ = 1/6 is sharp for this toolset (any δ > 1/6, not δ = 1/6).

**J10** (the verbatim sorried theorem) — to-prove given M7, 15 lines / 0.5 h / low.
```lean
theorem rightHalfBound_of_meanSquare (h : ZetaMeanSquare) : RightHalfBound := fun δ hδ =>
  -- h is not used; see Decision 2
  rightHalf_of_meanSquareUnif (σ₁ := 1 / 2 + min δ (1 / 2) / 2) (by …) (by …)
    (zetaMeanSquareUnif _ (by …) (by …)) δ (by …)
```

### Route A (Littlewood) — listed for completeness, NOT planned
Would use `h : ZetaMeanSquare` as given (pointwise at one σ₀ suffices), `Zeta23.RvM.backlund_horizontal`
(segment `[1/2,2]`; the sub-segment version needs `im_integral_logDeriv_le_aux`, `Backlund.lean:186`),
`re_riemannZeta_two_pos`, `zeta_lower_bound_two`, concavity as in J8'. Blocked-by: Littlewood's
lemma on a rectangle (`2π Σ m(ρ)(β_ρ − α) = ∫ log|f(α+it)| − ∫ log|f(β+it)| + ∫ arg f(σ+iT') − ∫ arg
f(σ+iT₁)`): absent from Mathlib and the tree; building it from `RectangleIntegral`/
`ResidueTheoremOnRectangleWithSimplePole` plus a branch of `log ζ` on a slit rectangle is 800+ lines /
40+ h / high. Only worth it if Joey insists on literally consuming `ZetaMeanSquare`.

## 4. Order of attack

Phase 1 — partial results (i) and (ii), fully sorry-free (two people can split M and J):

| step | lemma | lines | hours | risk |
|---|---|---|---|---|
| 1 | **J1** Jensen refactor | 40 | 2 | low |
| 2 | J2, J0, J3 | 85 | 4 | low |
| 3 | M1a, M1b, M1c, M2c | 90 | 3.5 | low |
| 4 | M1d (MV mean value) | 200 | 8 | medium |
| 5 | M2b, M2d, M3a | 160 | 6 | medium |
| 6 | M3b, M3c → `meanSquareUnif_naive` (σ₁ ≥ 2/3) | 180 | 8 | medium |
| 7 | J4, J5 | 140 | 7.5 | medium |
| 8 | J8' (concavity) | 80 | 4 | medium |
| 9 | J7 (Fubini) | 120 | 6 | medium |
| 10 | J6 (integrate the count) | 150 | 8 | medium-high |
| 11 | J8, J9 → `rightHalf_gt_sixth`, `bohrLandau_gt_sixth` | 105 | 5 | medium |
| 12 | M4a, M4b, M5 → `meanSquare_strip` verbatim for 2/3 ≤ σ ≤ 1 | 130 | 6 | medium |

Phase 1 total ≈ 1,500 lines, ≈ 70 focused hours (2–3 weeks part time, 1–1.5 weeks full time).
Expected overrun ×1.5 on steps 4, 6, 10 (Lean measure-theory/finsum friction). Deliverables after
Phase 1: `MeanSquareUnifFrom σ₁` for every σ₁ ≥ 2/3; `NRight δ T = O(T)` and `NOff δ 0 T = O(T)`
for every δ > 1/6; `meanSquare_strip` as stated for 2/3 ≤ σ ≤ 1. Neither sorry is removed verbatim
yet (`meanSquare_strip` still open on 1/2 < σ < 2/3; `rightHalfBound_of_meanSquare` still open for
δ ≤ 1/6).

Phase 2 — the blocked block M6 (C1), then M7, J10, M5-full:

| step | lemma | lines | hours | risk |
|---|---|---|---|---|
| 13 | M6b Fourier series of `B2per` | 40 | 2 | low-medium |
| 14 | M6a second Euler–Maclaurin step (improper IBP) | 250 | 20 | high |
| 15 | M6c first-derivative test | 200 | 15 | high |
| 16 | M6d swap + `zeta_approx_bounded` | 100 | 5 | medium |
| 17 | M7 `zetaMeanSquareUnif` (all σ₁ > 1/2) | 80 | 4 | medium |
| 18 | J10 + M5 with M7: both sorries closed verbatim | 30 | 1 | low |

Phase 2 total ≈ 700 lines, ≈ 47 hours nominal, realistically 60–90 hours because M6a and M6c are
oscillatory/improper-integral work with no Mathlib precedent. Grand total ≈ 2,200 lines,
≈ 120–160 hours. Confidence: Phase 1 ≈ 85 % as planned; Phase 2 ≈ 60 % (fallback if M6c stalls:
route (C2) of the route report, k-th order Euler–Maclaurin with `N = T^{1+ε}` — needs general-order
Euler–Maclaurin, not in Mathlib, comparable cost).

Downstream note: `MNF.RH.on_line_density_one_of_gap` consumes `BohrLandau` for *every* δ > 0, so
only Phase 2 feeds `Zeta23.BL.bohrLandau` unchanged; the Phase 1 result `bohrLandau_gt_sixth` is a
genuine but weaker theorem (zeros at distance > 1/6 from the line are O(T)) and should be reported
as such, not as Bohr–Landau.

## 5. The single best first lemma

**J1 `AnalyticOnNhd.sum_divisor_mul_log_le`** — 40 lines, 2 hours, low risk, and it is the pivot of
the whole J half: it is a transcription of Mathlib's `AnalyticOnNhd.sum_divisor_le` proof
(`JensenFormula.lean:390–440`) with one step removed, so it also validates the Jensen/divisor API
conventions (`|R|`, `finiteSupport`, `divisor_apply`, `divisor_nonneg`) that J2, J4, J6 all rely on.
File: `…/agents/<label>/J1_JensenCount.lean`, `import Zeta23.BohrLandau` only; compile with the
prescribed `lake env lean` command. Second lemma to write, in parallel: **M1d** (the MV mean value),
since it is the only medium-risk piece of the M half and determines the exact shape of the
Dirichlet-polynomial statement that M2d/M3b must match.
