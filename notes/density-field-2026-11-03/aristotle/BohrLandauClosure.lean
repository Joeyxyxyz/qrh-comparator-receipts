/-
BohrLandauClosure.lean — targets for Aristotle (Harmonic), 2026-11-03.

GOAL.  The mean square of the Riemann zeta function on vertical lines right of the critical
line, uniformly in σ ≥ σ₁ for every σ₁ > 1/2:

    ∃ C, ∀ σ ≥ σ₁, ∀ T ≥ 2,  ∫₁ᵀ ‖ζ(σ + it)‖² dt ≤ C · T        (theorem `meanSquareUnif_all`)

This is Hardy–Littlewood's mean-value theorem (Titchmarsh, *The theory of the Riemann
zeta-function*, Theorem 7.2(A), proved there for σ > 1/2 via the approximate formula of
Theorem 4.11).  In the author's Lean tree it is already proved for σ₁ ≥ 2/3 with the NAIVE
error term of the Euler–Maclaurin formula; the only missing ingredient for σ₁ ∈ (1/2, 2/3) is
the SHARPENED error term `zeta_approx_sharp` below (Theorem 4.11's O(x^{−σ})), and the only
missing ingredients for that are the first-derivative test (Titchmarsh Lemmas 4.2/4.3) and the
Fourier series of the periodic Bernoulli function B₂.  Once `meanSquareUnif_all` is proved, the
author's tree turns it, with no further analysis, into Bohr–Landau for every δ > 0
(zeros with |Re ρ − 1/2| ≥ δ are O(T)); today it has that only for δ > 1/6.

CONTRACT.  Every `sorry` below is a target.  The statements are the contract: prove them as
stated (hypotheses may be weakened, constants may be improved, but names and conclusions must
stay so that the author's tree can import this file).  Targets A, A′, B are Mathlib-only facts
with no ζ in them and can be attacked first and independently; D is a known identity; C, E, F,
G chain in that order; H is proved in the author's tree (restated here so the file is
self-contained; a proof is welcome but not required); I is the goal.  Any subset proved is
useful.  Use only Mathlib; no new axioms; `sorry` left where not proved.

CONVENTIONS.  `riemannZeta` is Mathlib's; s = σ + t·I with σ, t real; `(u : ℂ) ^ (-s - 1)` is
Mathlib's complex power of a positive real base; intervals are `∫ x in a..b` (intervalIntegral)
and `∫ u in Set.Ioi x` (Lebesgue on (x, ∞)).  ψ(u) = {u} − 1/2 is the sawtooth and
B₂per(u) = {u}² − {u} + 1/6 the periodic second Bernoulli function; P(u) := (B₂per u − 1/6)/2 is
the continuous periodic antiderivative of ψ (P' = ψ off the integers, P(n) = 0 at integers).
-/
import Mathlib

set_option maxHeartbeats 400000

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open scoped Real

namespace BLClosure

/-- the sawtooth ψ(u) = {u} − 1/2 -/
noncomputable def psi (u : ℝ) : ℝ := Int.fract u - 1 / 2

/-- the periodic second Bernoulli function B₂({u}) = {u}² − {u} + 1/6 -/
noncomputable def B2per (u : ℝ) : ℝ := Int.fract u ^ 2 - Int.fract u + 1 / 6

/-- P = (B₂per − 1/6)/2, the continuous periodic antiderivative of ψ with P(n) = 0 -/
noncomputable def P (u : ℝ) : ℝ := (B2per u - 1 / 6) / 2

/-- the Dirichlet polynomial S_N(s) = Σ_{n=1}^{N} n^{−s} -/
noncomputable def S (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

/-! ## A. The first-derivative test  (Titchmarsh Lemma 4.2)

If F is real, differentiable on [a, b], with F′ monotone and F′ ≥ λ > 0 there, then
|∫ₐᵇ e^{iF(x)} dx| ≤ 4/λ.  Classical proof: write e^{iF} = (F′ e^{iF})·(1/F′), integrate the
real and imaginary parts by the second mean value theorem (1/F′ is monotone), each is ≤ 2/λ. -/
theorem first_derivative_test {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (F F' : ℝ → ℝ)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (hmono : MonotoneOn F' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, lam ≤ F' x) :
    ‖∫ x in a..b, Complex.exp (I * (F x : ℂ))‖ ≤ 4 / lam := by
  sorry

/-! ## A′. The same with a nonnegative decreasing amplitude  (Titchmarsh Lemma 4.3)

|∫ₐᵇ G(x) e^{iF(x)} dx| ≤ 4 G(a)/λ for G ≥ 0 decreasing (second mean value theorem again). -/
theorem first_derivative_test_amp {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) (F F' G : ℝ → ℝ)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x) (hmono : MonotoneOn F' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, lam ≤ F' x) (hG : AntitoneOn G (Icc a b))
    (hG0 : ∀ x ∈ Icc a b, 0 ≤ G x) :
    ‖∫ x in a..b, (G x : ℂ) * Complex.exp (I * (F x : ℂ))‖ ≤ 4 * G a / lam := by
  sorry

/-! ## B. The Fourier series of B₂per  (absolutely convergent)

B₂({u}) = (1/π²) Σ_{ν ≥ 1} cos(2πνu)/ν² for every real u.  Mathlib has the Fourier
expansions of the periodized Bernoulli polynomials (`Mathlib/NumberTheory/ZetaValues.lean`,
`hasSum_one_div_nat_pow_mul_fourier` and its cos/sin forms); this is the k = 2 case unfolded. -/
theorem B2per_fourier (u : ℝ) :
    HasSum (fun ν : ℕ => Real.cos (2 * π * ((ν : ℝ) + 1) * u) / (π ^ 2 * ((ν : ℝ) + 1) ^ 2))
      (B2per u) := by
  sorry

/-! ## D. Euler–Maclaurin for ζ, one step  (Titchmarsh (2.1.5) / the tree's `Zeta0EqZeta`)

For Re s > 0, s ≠ 1 and N ≥ 1:
  ζ(s) = S_N(s) + N^{1−s}/(s − 1) − N^{−s}/2 − s ∫_N^∞ ψ(u) u^{−s−1} du. -/
theorem zeta_eq_euler_maclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = S N s + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
      - s * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  sorry

/-! ## E. The second Euler–Maclaurin step  (integration by parts with P)

Since P′ = ψ off the integers and P(N) = 0, for Re s > 0 and N ≥ 1:
  ∫_N^∞ ψ(u) u^{−s−1} du = (s + 1) ∫_N^∞ P(u) u^{−s−2} du. -/
theorem tail_by_parts {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ u in Ioi (N : ℝ), (P u : ℂ) * (u : ℂ) ^ (-s - 2) := by
  sorry

/-! ## C. One Fourier mode of the tail  (A′ with F(u) = 2πνu − t log u)

For ν ≥ 1, 0 < σ, 0 ≤ t and x ≥ max(1, t/π): F′(u) = 2πν − t/u ≥ 2πν − π ≥ πν on [x, ∞), and the
amplitude u^{−σ−2} decreases, so by A′ on [x, X] and X → ∞:
  |∫_x^∞ e^{2πiνu} u^{−s−2} du| ≤ 4 x^{−σ−2}/(πν)  (stated with the safe constant 8). -/
theorem tail_mode_bound {σ t x : ℝ} (hσ : 0 < σ) (hx1 : 1 ≤ x) (ht : 0 ≤ t) (hxt : t / π ≤ x)
    {ν : ℕ} (hν : 1 ≤ ν) :
    ‖∫ u in Ioi x, Complex.exp (2 * π * I * (ν : ℂ) * (u : ℂ)) * (u : ℂ) ^ (-(σ : ℂ) - t * I - 2)‖
      ≤ 8 / (π * ν) * x ^ (-σ - 2) := by
  sorry

/-! ## F. The sharpened tail  (B + C summed over ν, plus the constant term of P)

P(u) = Σ_{ν≥1} cos(2πνu)/(2π²ν²) − 1/12, so for σ₀ ≤ σ, 0 ≤ t and integer N ≥ max(1, t):
  |s ∫_N^∞ ψ(u) u^{−s−1} du| = |s(s+1)| |∫_N^∞ P(u) u^{−s−2} du| ≤ C(σ₀) N^{−σ}
(the factor |s(s+1)| ≤ (t+3)² ≤ (N+3)² is absorbed by the two extra powers of N; the −1/12
term contributes |s| N^{−σ−1}/12). -/
theorem tail_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      ‖((σ : ℂ) + t * I) * ∫ u in Ioi (N : ℝ), (psi u : ℂ) * (u : ℂ) ^ (-((σ : ℂ) + t * I) - 1)‖
        ≤ C * (N : ℝ) ^ (-σ) := by
  sorry

/-! ## G. The approximate formula with the sharp error  (Titchmarsh Theorem 4.11, x = N ≥ t)

ζ(s) = S_N(s) + N^{1−s}/(s−1) + O(N^{−σ}) uniformly for σ₀ ≤ σ ≤ 2, t ≥ 0, N ≥ max(1, t).
From D, F and |N^{−s}/2| = N^{−σ}/2. -/
theorem zeta_approx_sharp {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 → 0 ≤ t → ∀ N : ℕ, 1 ≤ N → t ≤ N →
      (σ : ℂ) + t * I ≠ 1 →
      ‖riemannZeta ((σ : ℂ) + t * I) - S N ((σ : ℂ) + t * I)
          - (N : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)‖
        ≤ C * (N : ℝ) ^ (-σ) := by
  sorry

/-! ## H. The Dirichlet-polynomial mean value  (proved in the author's tree; restated)

∫₀ᵀ |Σ aₙ n^{−it}|² dt ≤ T Σ |aₙ|² + Σ_{m≠n} |aₘ||aₙ| · 2/|log(n/m)|.  For aₙ = n^{−σ} with
σ > 1/2 the off-diagonal sum is ≤ C N^{2−2σ}(log N + 1) (the log-gap |log(n/m)| ≥ |n−m|/max(m,n)). -/
theorem dirichlet_mean_value (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (0:ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2
      ≤ T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log ((n : ℝ) / m)|)) := by
  sorry

/-- the off-diagonal sum for aₙ = n^{−σ}, σ > 1/2 -/
theorem offdiag_pow_bound {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if m = n then 0 else (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) * (2 / |Real.log ((n : ℝ) / m)|))
        ≤ C * (N : ℝ) ^ (2 - 2 * σ) * (Real.log N + 1) := by
  sorry

/-! ## I. The goal: the uniform mean square for every σ₁ > 1/2

Choose N = ⌈T⌉ (so N ≥ t on [1, T]); by G, ζ = S_N + N^{1−s}/(s−1) + E with |E| ≤ C N^{−σ} ≤ C;
then ∫₁ᵀ |ζ|² ≤ 3(∫|S_N|² + ∫ N^{2−2σ}/|s−1|² + C² T), with ∫₁ᵀ|S_N|² ≤ T ζ(2σ₁) + C N^{2−2σ}(log N+1)
by H and `offdiag_pow_bound`, and N^{2−2σ}(log N + 1) ≤ C′ T because 2 − 2σ < 1. -/
theorem meanSquareUnif_all {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T →
      ∫ t in (1:ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ C * T := by
  sorry

end BLClosure
