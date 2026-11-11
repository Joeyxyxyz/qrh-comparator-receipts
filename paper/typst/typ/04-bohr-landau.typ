= The density layer: counting vocabulary and the Bohr–Landau theorem <sec-the-density-layer-counting-vocabulary-and-the-bohrlandau-the>

Runs 7 to 9 added a Lean layer to the zeta23 tree, the checkout of Anthropic's zeta23 library checked in run 2~#cite(<anthropic-formal-math>).
The layer fixes a vocabulary for counting zeros by their distance from the critical line and proves, on that tree, the theorem of Bohr and Landau~#cite(<bohr-landau-1914>).
The theorem is classical; the contribution is its formalization and the receipted check.
Nothing in this section proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

The modules were first judged in run 7 (2026-11-03 UTC, 124 theorems), run 8 (2026-11-03, 270) and run 9 (2026-11-04, 334).
Each run was ACCEPTED by Comparator with the Lean kernel and NanoDa, and every axiom report lists only `propext`, `Quot.sound` and `Classical.choice`.
The layer's Lean files were produced with Claude Code~@claude-code under the author's direction, the two Bohr–Landau files by parallel agents from a written plan; the author set the goals, operated every run and is responsible for the claims.
The restatements and the reflection step delegate to supporting files that the author supplied on 2026-11-03; the record does not say which tool drafted them (see~@sec-authorship-and-use-of-ai-tools).

Theorem statements are quoted as Lean printed them in the run 11 bundle (those with a leading `@` from its `audit.out`), definitions from the sources of add-on v6.

== Counting functions and two notions of density <sec-counting-functions-and-two-notions-of-density>

The counting functions are those of~@sec-notation: each runs over the zeros with $0 < gamma <= T$ and weights a zero by $m(rho)$.

Two notions of density are kept apart (from `MNF/RH/Density.lean`, docstrings omitted):

```lean
def ReservoirDensityOne : Prop :=
  ∀ δ > 0, ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T

def OnLineDensityOne : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T
```

The first is density one within every fixed distance of the line, with $T_0$ depending on $delta$ and $epsilon$.
The word "reservoir" in its name is the author's word for zeros off the line (here, those closer to it than $delta$), not standard terminology.
The second is density one on the line itself.
The second implies the first, since $N_"off" (delta, T) <= N(T) - N_0(T)$ for $delta > 0$ (`Ncount_eq_near_add_off`, `N0_le_NNear`).
The first is not known to give the second: it places no constraint on zeros off the line whose distance from it tends to zero.
On the word "reservoir" the sources are not uniform: in `Density.lean` the $delta$-reservoir is the set of zeros with $0 < abs(beta - 1 slash 2) < delta$, in `ReservoirMass.lean` the reservoir is the set of all zeros off the line, and in `Cube.lean` the reservoir at threshold $Delta$ is the set with $abs(beta - 1 slash 2) >= Delta$.

Two facts are inherited from the tree and restated by delegation; neither is a result of this work.
The first, `MNF.RH.ncountSuperlinear`, says that $N(T) >= c T$ for every $c > 0$ and all large $T$.
It is derived from the main term of the zeta23 library's Riemann–von Mangoldt formula `riemannVonMangoldt_zeta` (classically~@von-mangoldt-1905).
The second is Theorem B of zeta23, which formalizes the theorem of Alpöge and Furman that for every $epsilon > 0$ and all large $T$ a proportion at least $2 slash 3 - epsilon$ of the zeros are simple and on the line~@alpoge-furman, read as an upper bound:

```lean
MNF.RH.offLine_le_one_third : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ↑(MNF.RH.NOffLine 0 T) ≤ (1 / 3 + ε) * ↑(MNF.RH.Ncount 0 T)
```

The left side is $N_(!=)(T)$.
The step from Theorem B is bookkeeping: $N(T)$ is the on-line count plus the off-line count, and the simple zeros on the line number at most the on-line count.
So the tree already bounds the proportion of zeros off the line by $1 slash 3 + epsilon$; the Bohr–Landau theorem is far stronger at each fixed distance and silent on zeros that approach the line.

== The Bohr–Landau theorem as formalized <sec-the-bohrlandau-theorem-as-formalized>

The statement is a definition of the library (`MNF/RH/GapDensity.lean`), a proposition that earlier runs carried only as a named hypothesis:

```lean
def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T
```

The theorem, as Lean prints it in the reports of runs 9 to 11:

```lean
Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau
```

In words: for every $delta > 0$ there is $C_delta$ such that $N_"off" (delta, T) <= C_delta T$ for all $T >= 2$.
The count is two-sided and with multiplicity, and the constant is existential; run 10 added an explicit dependence on $delta$ (`Zeta23.BL.bohrLandau_explicit`).
The declarations in `Zeta23.BL` cited here belong to this layer, not to Anthropic's library.
A similarly named declaration `Zeta23.BL.bohrLandau`, in a supporting file, rests on two `sorry` lemmas and is in no claim set.
The report of run 9 still says that Bohr–Landau is not proved; see~@sec-errata.

The theorem goes back to Bohr and Landau, who proved that $N(sigma, T) = O(T)$ for each fixed $sigma > 1 slash 2$; it is customarily cited to their two notes of 1914~@bohr-landau-1914 @bohr-landau-1914b, which were not consulted for this paper.
The source files cite Section 9.15 of~@titchmarsh for the classical proof.
The record describes the formal result as "Bohr–Landau 1914, formalized; not new mathematics".

The author is not aware of a prior Lean statement of the Bohr–Landau theorem in its two-sided form, as a count of the zeros with $abs(beta - 1 slash 2) >= delta$.
The searches behind this sentence were incomplete, and, according to the registry, the content of the theorem was available in Lean earlier: a zero-density estimate registered by Lewko on the Palomar registry~@palomar on 2026-10-11~@lewko-density-3917, on a different toolchain pin and not on the zeta23 tree, bounds $N(sigma, T)$ by a power of $T$ with exponent below 1 for each fixed $sigma > 1 slash 2$.
That implies the one-sided bound and, with the reflection of step 7, the two-sided one.
Earlier still, Fiori registered explicit zero-density bounds for short windows $(t - h, t + h]$ (Palomar entry of 2026-09-23, formalizing~@fiori-2026), proved by Jensen's formula and by Littlewood's lemma; according to the entry's abstract they include a two-sided corollary, that a positive proportion of the zeros in such a window have $alpha <= beta <= 1 - alpha$.
Those results are conditional on published explicit bounds and numerical certificates taken as hypotheses, were not re-checked here, and are not the Bohr–Landau theorem.

== Architecture of the formal proof <sec-architecture-of-the-formal-proof>

The proof has two halves: a mean square of $zeta$ on vertical lines to the right of $1 slash 2$, and a count of zeros by Jensen's formula on disks, which the plan chose over Littlewood's lemma on rectangles because the latter was in neither Mathlib nor the tree.
From the tree the proof takes the Euler–Maclaurin representation `Zeta0EqZeta`, a port from the PrimeNumberTheoremAnd project~@pnt-plus, the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen`~@montgomery-vaughan-1974, the lower bound $abs(zeta(2 + i t)) >= 1 slash 3$ and, for step 7, the reflection symmetry of the zeros with multiplicity (`zetaZeroConfig.reflect_mem`, `zetaZeroConfig.mult_reflect`); from Mathlib~@mathlib it takes Jensen's formula and a cosine series for Bernoulli polynomials.
The bulk is in `Zeta23/BL/BohrLandauPartial.lean` (139 theorems, run 8) and `Zeta23/BL/BohrLandauClosure.lean` (64 theorems, run 9).
Every lemma of the layer named below is in the claim set.

*Step 1. Euler–Maclaurin* (`zeta_eq_euler_maclaurin`, `tail_by_parts`).
From `Zeta0EqZeta`, for #box[$op("Re") s > 0$], $s != 1$ and every integer $N >= 1$,
$ zeta(s) = sum_(n <= N) n^(-s) + N^(1-s)/(s-1) - N^(-s)/2 - s integral_N^infinity psi(u) thin u^(-s-1) dif u, wide psi(u) = {u} - inline(1/2) . $
A second integration by parts replaces $psi(u) thin u^(-s-1)$ by $(s+1) psi_2(u) thin u^(-s-2)$, where $psi_2 = (B_2({u}) - 1/6) slash 2$ is the continuous periodic antiderivative of $psi$ that vanishes at the integers.

*Step 2. Fourier series of the second Bernoulli function* (`B2per_fourier`, `P_fourier`).
$B_2({u}) = sum_(nu >= 1) cos(2 pi nu u) slash (pi^2 nu^2)$, from Mathlib's series.

*Step 3. First-derivative test for smooth phases* (`first_derivative_test_amp_smooth'`).
If $F' >= lambda > 0$ on $[a, b]$ with $F''$ continuous, and $G >= 0$ is continuously differentiable with $G' F' - G F'' <= 0$, then $abs(integral_a^b G(x) e^(i F(x)) dif x) <= 4 G(a) slash lambda$.
With $F(u) = 2 pi nu u - t log u$ and $G(u) = u^(-sigma-2)$ it bounds the $nu$-th Fourier mode of the tail over $(x, infinity)$ by $8/(pi nu) x^(-sigma-2)$ when $t <= pi x$ (`tail_mode_bound'`); this is where the condition $t <= N$ enters.

*Step 4. Sharp approximate formula* (`tail_sharp`, `zeta_approx_sharp`).
Summing the modes: for every $sigma_0 > 0$ there is $C$ such that, for $s = sigma + i t != 1$ with $sigma_0 <= sigma <= 2$, $0 <= t <= N$ and $N >= 1$,
$ abs(zeta(s) - sum_(n <= N) n^(-s) - N^(1-s)/(s-1)) <= C thin N^(-sigma) . $
The source describes this as the shape of Theorem 4.11 of~@titchmarsh on a narrower range.

*Step 5. Mean square on vertical lines* (`M1.dirichlet_meanSquare_le`, `meanSquareUnif_all`).
The Dirichlet-polynomial mean value in Montgomery–Vaughan form, $integral_0^T abs(sum_(n <= N) a_n n^(-i t))^2 dif t <= T sum_(n <= N) abs(a_n)^2 + 26 sum_(n <= N) (n+1) abs(a_n)^2$, follows from the tree's inequality.
With $N = ceil(T)$ and step 4 it gives

```lean
@BLClosure.meanSquareUnif_all : ∀ {σ₁ : ℝ},
  1 / 2 < σ₁ →
    ∃ C, ∀ (σ : ℝ), σ₁ ≤ σ → ∀ (T : ℝ), 2 ≤ T → ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2 ≤ C * T
```

This is the $O(T)$ upper bound in the classical mean-value theorem for $abs(zeta(sigma + i t))^2$ on the lines $sigma > 1 slash 2$ (the source cites Section 7.2 of~@titchmarsh); the asymptotic formula $tilde zeta(2 sigma) thin T$ is not proved.

*Step 6. Jensen on disks centered at $2 + i t$, averaged in $t$* (`sum_divisor_mul_log_le`, `geom_facts`, `count_le_integral`, `rightHalf_of_meanSquareUnif`).
Fix $1 slash 2 < sigma_1 < 1$ and $sigma_1 - 1 slash 2 < delta <= 1 slash 2$.
For $t >= 3$ the disk of radius $R = 2 - sigma_1$ about $2 + i t$ lies in $op("Re") s >= sigma_1$ and misses the pole, and a zero with $beta >= 1 slash 2 + delta$ lies in a concentric disk of smaller radius $r$ for all $t$ within a fixed distance $h$ of $gamma$.
The disk inequality `sum_divisor_mul_log_le` (from Jensen's formula) at each $t$, integrated over $3 <= t <= T + 3$ for $T >= 4$, bounds $2 h log(R slash r) thin (N(1/2 + delta, T) - N(1/2 + delta, 4))$ by $T log 3$ plus the integral of the circle averages of $L = 1/2 log(1 + abs(zeta)^2) <= 1/2 abs(zeta)^2$, which Fubini's theorem and step 5 bound by a multiple of $T$.
Hence $N(1/2 + delta, T) = O(T)$ for every $delta > sigma_1 - 1 slash 2$.
For $0 < delta < 1 slash 2$ the choice $sigma_1 = 1 slash 2 + delta slash 2$ applies, and for $delta >= 1 slash 2$ the count is zero, which gives the right-half bound for every $delta > 0$ (`Zeta23.BL.rightHalf_all`).

*Step 7. Reflection* (`MNF.RH.NOff_eq_right_add_left`, `NLeft_eq_NRight`, `bohrLandau_of_right`).
The map $rho |-> 1 - overline(rho)$ preserves ordinate and multiplicity and exchanges the two half-strips, so $N_"off" (delta, T) = 2 N(1/2 + delta, T)$ for $delta > 0$, and a right-half bound with constant $C$ gives `BohrLandau` with constant $2 C$.

== The intermediate result for distances above one sixth <sec-the-intermediate-result-for-distances-above-one-sixth>

Run 8 had the Dirichlet-polynomial mean value and steps 6 and 7, but only the tree's bound for the Euler–Maclaurin tail, and reached

```lean
Zeta23.BL.bohrLandau_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ C * T
```

The obstacle is the error term: the tree bounds the tail of step 1 by $(sigma + t) N^(-sigma_1) slash sigma_1$ on #box[$sigma >= sigma_1$], which grows linearly in $t$.
Its square, integrated over $1 <= t <= T$, is of order $T^3 N^(-2 sigma_1)$, which is $O(T)$ only if $N$ is at least of order $T^(1 slash sigma_1)$.
The Montgomery–Vaughan term and the term #box[$N^(1-s) slash (s-1)$] are of order $N^(2 - 2 sigma_1)$, which is $O(T)$ only if $N$ is at most of order $T^(1 slash (2 - 2 sigma_1))$.
For #box[$N = T^a$] the window $1 slash sigma_1 <= a <= 1 slash (2 - 2 sigma_1)$ is nonempty exactly when $sigma_1 >= 2 slash 3$.
The proof takes #box[$a = 3 slash 2$] and obtains the mean square for $2 slash 3 <= sigma_1 < 1$ (`Zeta23.BL.M3.meanSquareUnif_explicit`); step 6 needs $delta > sigma_1 - 1 slash 2$, hence $delta > 1 slash 6$.
The source calls this "a limitation of this route, not a theorem about ζ".
Step 4 removes the factor $t$ from the error, after which $N = ceil(T)$ serves every $sigma_1 > 1 slash 2$.

== Corollaries <sec-corollaries>

```lean
MNF.RH.reservoirDensityOne_unconditional : MNF.RH.ReservoirDensityOne
@MNF.RH.onLineDensityOne_of_gap_only : ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
```

The first has no hypothesis and is the classical consequence of the Bohr–Landau theorem, formalized: within every fixed distance of the critical line the zeros have density one, by the bound $C_delta T$ and the superlinear growth of $N(T)$.

The second is conditional on the gap hypothesis $G(Delta)$, in Lean `SpectralGapHyp Δ` (see~@sec-the-mnf-rh-library-in-standard-terms).
Under it the zeros within $Delta$ of the line are exactly the zeros on it (`NNear_eq_N0_of_gap`), so the instance $delta = Delta$ of the first corollary is density one on the line; the hypothesis is used only there.

The hypothesis is not weakened: for $Delta >= 1 slash 2$ it is the Riemann hypothesis, and for $0 < Delta < 1 slash 2$ it is an unproved zero-free strip $1 slash 2 < op("Re") s < 1 slash 2 + Delta$.
The conclusion follows from the Riemann hypothesis and is not known to imply it: it allows infinitely many zeros off the line provided they number $o(N(T))$.
The implication itself is folklore, not new mathematics.
Neither corollary is progress on the Riemann hypothesis or on the gap hypothesis.
