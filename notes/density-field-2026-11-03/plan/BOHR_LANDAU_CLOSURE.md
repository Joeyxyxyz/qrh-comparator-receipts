# Bohr–Landau closed for every δ > 0 (2026-11-03, late)

A second plan-execution workflow (nine agents + merge) proved the chain that the Aristotle target
file `aristotle/BohrLandauClosure.lean` laid out, with the first-derivative test taken in its
smooth form (twice-differentiable phase, which is all ζ needs). Result: `Zeta23/BL/BohrLandauClosure.lean`
on the zeta23 tree, 64 theorems, no `sorry`, every declaration with axioms exactly
`[propext, Classical.choice, Quot.sound]` (re-checked by hand: `closure/AuditClosure.lean`), and
Comparator-accepted together with everything before it (334 theorems, 81 definitions compared by
body, Lean kernel and NanoDa: `comparator-precheck-v4.log`).

## The chain (all kernel-checked)

| step | theorem | content |
|---|---|---|
| A/A′ | `BLClosure.first_derivative_test_smooth`, `first_derivative_test_amp_smooth` | Titchmarsh Lemmas 4.2/4.3 for a twice-differentiable phase F with F″ ≥ 0, F′ ≥ λ > 0: \|∫ₐᵇ G e^{iF}\| ≤ 4G(a)/λ (G ≥ 0 decreasing); proof by one integration by parts (the proof gives 2G(a)/λ) |
| B | `B2per_fourier`, `P_fourier` | B₂({u}) = (1/π²) Σ cos(2πνu)/ν², from Mathlib's periodized-Bernoulli Fourier series; P = (B₂per − 1/6)/2 |
| D | `zeta_eq_euler_maclaurin` | ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2 − s∫_N^∞ ψ(u)u^{−s−1}du, from the tree's `Zeta0EqZeta` |
| E | `tail_by_parts` | ∫_N^∞ ψ u^{−s−1} = (s+1)∫_N^∞ P u^{−s−2} |
| C | `tail_mode_bound` | \|∫_x^∞ e^{2πiνu} u^{−s−2}\| ≤ 8x^{−σ−2}/(πν) for x ≥ max(1, t/π) |
| F | `tail_sharp` | \|s∫_N^∞ ψ u^{−s−1}\| ≤ C(σ₀) N^{−σ} for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N |
| G | `zeta_approx_sharp` | ζ(s) = S_N(s) + N^{1−s}/(s−1) + O(N^{−σ}) uniformly for σ₀ ≤ σ ≤ 2, 0 ≤ t ≤ N (Titchmarsh 4.11 with x = N ≥ t) |
| I | `meanSquareUnif_all` | for every σ₁ > 1/2: ∃ C, ∀ σ ≥ σ₁, ∀ T ≥ 2, ∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ C·T (Hardy–Littlewood) |
| close | `Zeta23.BL.rightHalf_all`, `rightHalfBound`, **`bohrLandau_full : MNF.RH.BohrLandau`** | via the tree's `rightHalf_of_meanSquareUnif` (Jensen on discs) and `bohrLandau_of_right` (reflection) |
| close | `Zeta23.BL.meanSquare_strip'`, `rightHalfBound_of_meanSquare'` | the two statements that `Zeta23/BohrLandau.lean` left as `sorry`, proved (the ∫₀ᵀ form at σ = 1 vacuous as before; the hypothesis of the second is unused) |
| close | `MNF.RH.reservoirDensityOne_unconditional`, **`MNF.RH.onLineDensityOne_of_gap_only`** | for every fixed δ > 0, density one within δ of the line, no hypothesis; a gap at any Δ > 0 gives density one on the line with no other hypothesis (for Δ ≥ 1/2 the gap is RH) |

## What changes in the ledger

Rows 5, 7, 8 of the field table are now PROVED: Bohr–Landau for every δ > 0, the mean square for
every σ > 1/2, and `ReservoirDensityOne` outright. Row 6 (`OnLineDensityOne`) is conditional on
the gap alone. Row 9 (`SpectralGapHyp`) is untouched: it is RH for Δ ≥ 1/2 and an open zero-free
strip for 0 < Δ < 1/2; nothing here bears on it. The Aristotle package is superseded (kept as the
statement of the contract that was met).
