# Prompt for Aristotle — close the mean square of ζ below σ = 2/3 (path to Bohr–Landau for every δ > 0)

Attached: `BohrLandauClosure.lean` (imports only Mathlib; typechecks at Lean v4.33.0-rc2 / Mathlib
commit 51e6992e with every proof `sorry`; the statements use only stable API: `riemannZeta`,
`intervalIntegral`, complex powers of positive reals, `Int.fract`, `HasSum`).

## What we have and what is missing

In a kernel-checked Lean tree on top of Anthropic's `zeta23` formalization we have proved, with
standard axioms only:

- the mean square ∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ C(σ₁)·T uniformly for σ ≥ σ₁, for every 2/3 ≤ σ₁ < 1;
- from any such uniform mean square on Re s ≥ σ₁, the Bohr–Landau bound: zeros with
  Re ρ − 1/2 ≥ δ, 0 < Im ρ ≤ T are O(T) for every δ > σ₁ − 1/2 (Jensen on discs centred 2 + it,
  averaged in t);
- hence Bohr–Landau for every δ > 1/6.

The restriction to σ₁ ≥ 2/3 comes from one place: the Euler–Maclaurin formula
ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2 − s∫_N^∞ ψ(u)u^{−s−1}du is used with the NAIVE
tail bound |s|N^{−σ}/σ. With N = T^a that forces 1/σ ≤ a ≤ 1/(2−2σ), which is possible only for
σ ≥ 2/3. Titchmarsh's Theorem 4.11 sharpens the tail to O(N^{−σ}) for N ≥ t, which lets N = ⌈T⌉
and closes the mean square for every σ > 1/2. Nothing else is missing: once
`meanSquareUnif_all` is proved, our tree derives Bohr–Landau for every δ > 0 with no further
analysis.

## The route in the file (prove in any order; any subset helps)

| target | content | depends on |
|---|---|---|
| A `first_derivative_test` | Titchmarsh Lemma 4.2: \|∫ₐᵇ e^{iF}\| ≤ 4/λ for F′ monotone, F′ ≥ λ > 0 | Mathlib only |
| A′ `first_derivative_test_amp` | Lemma 4.3: with a nonnegative decreasing amplitude G, ≤ 4G(a)/λ | A |
| B `B2per_fourier` | B₂({u}) = (1/π²) Σ_{ν≥1} cos(2πνu)/ν² (Mathlib: `Mathlib/NumberTheory/ZetaValues.lean`, the periodized Bernoulli Fourier series, k = 2) | Mathlib only |
| D `zeta_eq_euler_maclaurin` | the one-step Euler–Maclaurin identity for ζ (Re s > 0, s ≠ 1, N ≥ 1) | Mathlib only |
| E `tail_by_parts` | ∫_N^∞ ψ u^{−s−1} = (s+1)∫_N^∞ P u^{−s−2}, P the periodic antiderivative of ψ with P(N) = 0 | Mathlib only |
| C `tail_mode_bound` | one Fourier mode: \|∫_x^∞ e^{2πiνu} u^{−s−2}\| ≤ 8x^{−σ−2}/(πν) for x ≥ max(1, t/π) | A′ |
| F `tail_sharp` | \|s∫_N^∞ ψ u^{−s−1}\| ≤ C(σ₀) N^{−σ} for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N | B, C, E |
| G `zeta_approx_sharp` | Theorem 4.11 with x = N ≥ t: ζ = S_N + N^{1−s}/(s−1) + O(N^{−σ}) | D, F |
| H `dirichlet_mean_value`, `offdiag_pow_bound` | the Dirichlet-polynomial mean value (already proved in our tree; restated so the file is self-contained) | Mathlib only |
| I `meanSquareUnif_all` | the goal, for every σ₁ > 1/2 | G, H |

Suggested order: A, A′, B first (pure real analysis, no ζ); then D and E (identities); then
C, F, G; then I. If the full chain is out of reach, the most valuable single results are A/A′
(nothing like them exists in Mathlib) and G.

## Rules

- Keep every statement's name and conclusion; hypotheses may be weakened and constants improved.
- Mathlib only; no new axioms; no `native_decide`; leave `sorry` where a proof is not found and
  say which goals remain. A statement found to be false as written should be reported with the
  counterexample, not silently changed.
- Return the file with proofs filled in and a short note per target: proved / partial (what
  remains) / not attempted.

## Why this matters to us

Everything downstream is already formalized and Comparator-checked (Lean kernel and NanoDa,
sandboxed): the density consequences for the zeros, the reduction of Bohr–Landau to the
right half-strip, and the Jensen-disc count. This file is the last analytic input.
