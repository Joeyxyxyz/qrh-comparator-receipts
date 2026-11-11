// Line-break opportunities inside a long code name (the helper of typ/10-appendix-b.typ): after each occurrence of
// the given character the name may break. The empty box has no size and no text: nothing is inserted into the
// name, and a copied name stays intact.
#let breakable(it, after) = {
  let parts = it.text.split(after)
  for (i, p) in parts.enumerate() {
    if i + 1 < parts.len() { raw(p + after); box() } else { raw(p) }
  }
}

= A zero-density estimate, the displacement bound and the pair measure <sec-a-zero-density-estimate-the-displacement-bound-and-the-pair>

This section covers the modules first judged in run 10 (`Zeta23/Density/StripDensity.lean`, `MNF/RH/ReservoirMass.lean`) and in run 11 (`MNF/RH/Cube.lean`).
As in the previous section, the Lean statements are copied from the run 11 bundle, which re-judges the whole layer, those with a leading `@` from its `audit.out`.
The three files were written with Claude Code~@claude-code by parallel agents from written plans, under the author's direction (see~@sec-authorship-and-use-of-ai-tools); for the third, the idea of restating the gap hypothesis as the statement that distinct zeros near the line have distinct ordinates is the author's (in the words of `NOTICE`, "reading the strip through the simplicity of the projected zeros").
The analytic results formalize classical theorems with weaker exponents than the literature; the rest is bookkeeping over finite sums of zeros.
None of it proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

== The zero-density estimate <sec-the-zero-density-estimate>

```lean
@Zeta23.Density.density_single_window : ∀ {σ₁ δ : ℝ},
  1 / 2 < σ₁ →
    σ₁ - 1 / 2 < δ →
      δ ≤ 1 / 2 →
        ∃ C,
          ∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3
```

With $sigma = 1 slash 2 + delta$: for $1 slash 2 < sigma_1 < sigma <= 1$ there is $C = C(sigma_1, sigma)$ such that, for all $T >= 2$,
$ N(sigma, T) <= C thin T^(thin 1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)) thin (1 + log T)^3 . $

At $sigma_1 = 3 slash 4$ the exponent is $5 slash 6$: for each fixed $sigma > 3 slash 4$, $N(sigma, T) = O(T^(5 slash 6) (log T)^3)$.
Since #box[$sigma_1 < sigma$] is strict and $C$ depends on $sigma_1$, every saving below $(2 sigma - 1)^2 slash (2 sigma)$ is obtained and that value is not.
The statement counts zeros to the right of the line; the two-sided form over $N_"off"$ is not a theorem of the layer.
It is a count, not a zero-free region: it excludes no individual zero and says nothing about zeros closer than $delta$ to the line.

The result is classical in kind and weak in strength.
Carlson's theorem~@carlson-1920 gives $N(sigma, T) << T^(4 sigma (1 - sigma) + epsilon)$, and $4 sigma (1 - sigma) = 1 - (2 sigma - 1)^2$; the saving here is smaller than Carlson's by the factor $1 slash (2 sigma_1)$ (at $sigma_1 = 3 slash 4$: Carlson's exponent $3 slash 4$, against $5 slash 6$ here).
Ingham's exponent #box[$3 (1 - sigma) slash (2 - sigma)$]~@ingham-1940 is smaller still for $1 slash 2 < sigma < 1$.
Among the later improvements is the estimate $N(sigma, T) <= T^(30 (1 - sigma) slash 13 + o(1))$ of Guth and Maynard~@guth-maynard; Tao, Trudgian and Yang~@tao-trudgian-yang tabulate the known exponents and add new ones.
See also~#cite(<titchmarsh>).
Stronger estimates also exist in Lean.
Lewko registered four zero-density formalizations on the Palomar registry between 2026-10-07 and 2026-10-21~@lewko-density-34 @lewko-density-32 @lewko-density-3917 @lewko-density-improved; the statement file of~@lewko-density-3917, which was read, has Ingham's exponent near the line and a smaller exponent than the one above throughout (that its proof was accepted is the registry's report, not re-checked here; its Comparator configuration lists as holes the three definitions on which the statements rest, and the challenge and solution files at the registered commit define them identically).
Those statements are one-sided, on another toolchain pin, and not on the zeta23 tree.
Run 10 is an independent formalization of Carlson's method on that tree, with a weaker exponent, judged by Comparator with a published receipt.

The proof keeps the Jensen-disk argument of the Bohr–Landau proof (disks centered at $2 + i t$, averaged over $t$; see step 6 of~@sec-architecture-of-the-formal-proof) and changes what is averaged.
Below, $s = sigma + i t$ and $mu$ is the Möbius function.

+ Mollifier.
  Let $M_X (s) = sum_(n <= X) mu(n) n^(-s)$ and $f_X = zeta M_X$.
  For $op("Re") s > 1$, $f_X (s) - 1 = -zeta(s) sum_(n > X) mu(n) n^(-s)$, so $-log abs(f_X (2 + i t)) <= pi^2 slash (3 X)$ for $X >= 4$.
  Zeros of $zeta$ are zeros of $f_X$ of at least the same order, so the same disk inequality for $f_X$ counts them, and the center term, of order $T$ in the Bohr–Landau proof, becomes $O(T slash X)$.
+ Product polynomial.
  With $S_N (s) = sum_(n <= N) n^(-s)$, $S_N M_X = sum_(m <= N X) c_m m^(-s)$, where $c_1 = 1$, $c_m = 0$ for $1 < m <= X <= N$, and $abs(c_m) <= d_X (m)$, the number of divisors of $m$ not exceeding $X$.
+ Divisor bound.
  $sum_(m <= Y) d_X (m)^2 <= Y (1 + log X)^3$, by counting common multiples; this elementary bound is the origin of the factor $(1 + log T)^3$.
+ Window mean square.
  On a segment $t in [a, a + ell]$ of a line $op("Re") s = sigma >= sigma_1$, the mean square of $S_N M_X$ is bounded by the Montgomery–Vaughan inequality~@montgomery-vaughan-1974 (the weighted Hilbert inequality behind it is zeta23’s), and that of $(zeta - S_N) M_X$ by the sharp approximate formula of run 9, $abs(zeta(s) - S_N (s) - N^(1 - s) slash (s - 1)) <= C_G N^(-sigma)$ for $sigma_1 <= sigma <= 2$ and $0 <= t <= N$.
  The two are joined by $abs(u + v)^2 <= (1 + eta) abs(u)^2 + (1 + 1 slash eta) abs(v)^2$ with a free $eta > 0$.
+ $epsilon$-majorant.
  $log abs(f_X) <= 1/2 log(epsilon^2 + abs(f_X)^2)$, and Jensen's inequality for the concave logarithm bounds the average of this majorant over a segment of length $T$ by $1/2 (epsilon^2 + E)$ when the integral of $abs(f_X)^2$ over the segment is at most $T(1 + E)$.
  The Bohr–Landau proof used the majorant $1/2 log(1 + abs(zeta)^2) <= 1/2 abs(zeta)^2$, whose constant $1$ removes every saving.
+ Exponent arithmetic.
  With $X = floor(T^theta)$, $N = ceil(T) + 5$, $epsilon^2 = 1 slash X$ and $theta = (2 sigma_1 - 1) slash (2 sigma_1)$, the count is at most a constant times $T^(1 - kappa) (1 + log T)^3$, where $kappa = (2 sigma_1 - 1)^2 slash (2 sigma_1)$.

One approximate formula of length $N approx T$ serves the whole window, and this costs the exponent.
In the account of the proof plan (`strip/STRIP_PLAN.md` in the notes), the diagonal, off-diagonal and center terms balance at $X = T^(2 sigma_1 - 1)$, giving Carlson's exponent, only when $N approx t$ on each dyadic window.
With a single $N$ the term $N^(1 - s) slash (s - 1)$, multiplied by $M_X$, is large at small $t$; its cross term moves the balance to $X = T^theta$ and the saving to $kappa$.
The dyadic version, and with it Carlson's exponent, was a stretch target of the plan and is not proved.

== The displacement of the zeros from the line <sec-the-displacement-of-the-zeros-from-the-line>

Recall from~@sec-notation the total displacement of the zeros from the critical line, $D(T) = sum_(0 < gamma <= T) m(rho) thin abs(beta - 1 slash 2)$.
In Lean it is `MNF.RH.reservoirMass T`, the author's "reservoir mass", with "reservoir" as glossed in~@sec-counting-functions-and-two-notions-of-density.

```lean
MNF.RH.reservoirMass_eq_integral : ∀ (T : ℝ), MNF.RH.reservoirMass T = ∫ (δ : ℝ) in 0..1 / 2, ↑(MNF.RH.NOff δ 0 T)
MNF.RH.reservoirMass_le_rpow : ∃ A T₀, ∀ (T : ℝ), T₀ ≤ T → MNF.RH.reservoirMass T ≤ A * T * Real.log T ^ (3 / 5)
MNF.RH.meanDisplacement_tendsto_zero : Filter.Tendsto (fun T => MNF.RH.reservoirMass T / ↑(MNF.RH.Ncount 0 T))
  Filter.atTop (nhds 0)
```

These are the layer-cake identity $D(T) = integral_0^(1 slash 2) N_"off" (delta, T) dif delta$, the bound $D(T) <= A thin T (log T)^(3 slash 5)$ for $T >= T_0$ (a real power), and $D(T) slash N(T) -> 0$: the mean displacement, with multiplicity, tends to zero.

The input is the Bohr–Landau bound with its dependence on $delta$ made explicit (#breakable(`Zeta23.BL.bohrLandau_explicit`, ".")): there are $A_1, B_1 >= 0$ with $N_"off" (delta, T) <= (A_1 delta^(-5 slash 2) + B_1) thin T$ for $0 < delta <= 1 slash 2$ and $T >= 2$.
The exponent $-5 slash 2$ is $delta^(-1)$ from the mean-square constant times $delta^(-3 slash 2)$ from the disk geometry; the classical dependence on $delta$ is of order $delta^(-1)$ up to a logarithm (the zbMATH review of~@littlewood-1924 records $N(sigma, T) = O(T/(sigma - 1 slash 2) log 1/(sigma - 1 slash 2))$).
The bounds $c thin T log T <= N(T) <= C thin T log T$ for large $T$ are derived from zeta23’s Riemann–von Mangoldt statement.
Splitting the integral at $delta_0 = (log T)^(-2 slash 5)$, the head is at most $delta_0 N(T) << T (log T)^(3 slash 5)$ and the tail at most #box[$(2/3 A_1 delta_0^(-3 slash 2) + B_1 slash 2) thin T$]\; the lower bound for $N(T)$ then gives $D(T) <= A' (log T)^(-2 slash 5) N(T)$ with another constant $A'$ (`reservoirMass_le_Ncount_mul`).
The constants are named in the source; the receipted statements assert existence only.
The signed sum vanishes, $sum_(0 < gamma <= T) m(rho) (beta - 1 slash 2) = 0$ for every $T$ (`signedReservoir_eq_zero`), because the reflection $rho |-> 1 - overline(rho)$ in the critical line is a multiplicity-preserving bijection of the window that negates each term.

These bounds are far weaker than the classical ones.
The gain over the trivial $D(T) <= 1/2 N(T)$ is only the factor $(log T)^(-2 slash 5)$; Littlewood~@littlewood-1924 obtained $O(T log log T)$ for this sum, and Selberg's estimate $N(sigma, T) << T^(1 - (sigma - 1 slash 2) slash 4) log T$, uniform for $1 slash 2 <= sigma <= 1$~@selberg-1946, gives $O(T)$ on integration over $sigma$.
That the mean displacement tends to zero is a theorem, and already a consequence of Littlewood's bound; under RH it is trivial, since then $D(T) = 0$.
It restricts no individual zero, is consistent with infinitely many zeros off the line, and is silent on the gap hypothesis.
The author is not aware of a prior Lean formalization of a bound for $D(T)$; the searches behind that sentence were limited.

== The pair measure <sec-the-pair-measure>

For a real function $f$ of three real variables, the module defines
$ Pi_T (f) = sum_(rho) sum_(rho') m(rho) thin m(rho') thin f(beta - inline(1/2), thick beta' - inline(1/2), thick gamma - gamma'), $
the sum over ordered pairs of nontrivial zeros with $0 < gamma, gamma' <= T$ (Lean: `pairSum T f`).
The author calls the three coordinates "the cube"; in standard terms $Pi_T$ is a finite weighted pair sum.
Its marginals are rearrangements: $Pi_T (1) = N(T)^2$; a function $g$ of the first coordinate alone gives $N(T) sum_(rho) m(rho) thin g(beta - 1/2)$, so the indicator of $abs(a) >= delta$ gives $N(T) thin N_"off" (delta, T)$ and $g(a) = abs(a)$ gives $N(T) thin D(T)$.

The atom at ordinate difference zero, $Pi_T (bold(1) [u = 0])$ with $u$ the third coordinate, equals $sum_rho m(rho)^2 + P(T)$ (`coincidentMass_eq`), where $P(T)$ sums $m(rho) m(rho')$ over ordered pairs of distinct zeros with equal ordinates.
The diagonal part lies between $N(T)$ and $N(T)^2$, and each zero off the line contributes $m(rho)^2$ to $P(T)$ through its reflection $1 - overline(rho)$.
With $N_(!=) (T) = N(T) - N_0 (T)$ the count of zeros off the line,
$ P(T) <= N_(!=) (T) thin N(T) + N_0 (T) thin N_(!=) (T) $
(`offDiagonalCoincidentMass_le`).
With zeta23’s Theorem B~@anthropic-formal-math read as $N_(!=) (T) <= (1 slash 3 + epsilon) N(T)$ for large $T$, this gives $P(T) <= (5 slash 9 + epsilon) thin N(T)^2$ for large $T$ (`offDiagonalCoincidentMass_le_five_ninths`); $5/9 = 1/3 dot 1 + 2/3 dot 1/3$.
Under RH, $N_(!=) (T) = 0$ and the same inequality gives $P(T) = 0$; the constant $5 slash 9$ is bookkeeping on top of Theorem B and says nothing about whether $P(T)$ vanishes.

The plan (`cube/CUBE_PLAN.md` in the notes) had the bound $P(T) <= N_(!=) (T) thin N(T)$, hence the constant $1 slash 3 + epsilon$, on the ground that a zero on the line has no distinct partner at its ordinate.
The Claude Code agent assigned to that statement found it false as bookkeeping (`cube/NODE_REPORTS.md`): a double zero on the line sharing its ordinate with two simple zeros off the line, reflections of each other, gives $P = 10$ against $N_(!=) N = 2 dot 4 = 8$.
No such configuration is known for $zeta$, but nothing proved on the tree excludes it (RH would).
The statement was not admitted with a `sorry`; the bound above replaced it.
None of this concerns pair correlation: the small-distance law of the zeros is the prediction of Montgomery's conjecture~@montgomery-1973, not a theorem.

== Degenerate zeros and two equivalences <sec-degenerate-zeros-and-two-equivalences>

In the author's vocabulary a nontrivial zero is degenerate if it is multiple or shares its ordinate with another nontrivial zero.
A zero off the line is degenerate, its partner being $1 - overline(rho)$ (`degenerate_of_not_onLine`).
The gap hypothesis $G(Delta)$, in Lean `SpectralGapHyp Δ`, is in standard terms the zero-free strip $1 slash 2 < op("Re") s < 1 slash 2 + Delta$ (see~@sec-the-mnf-rh-library-in-standard-terms); it is RH for $Delta >= 1 slash 2$ and is unproved for every $Delta > 0$.

```lean
MNF.RH.noDegenerate_iff : (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ¬MNF.RH.Degenerate ρ) ↔
  (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → MNF.RH.OnLine ρ) ∧ MNF.RH.AllZerosSimple
MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ MNF.RH.OrdinatesInjectiveOn (MNF.RH.bandZeros Δ)
MNF.RH.spectralGapHyp_iff_bandCoincidentMass : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (T : ℝ), MNF.RH.bandCoincidentMass Δ T = 0
```

Lean prints three statements; the second and the third are two forms of one equivalence.
The first says that no nontrivial zero is degenerate if and only if every nontrivial zero is on the line (`OnLine ρ` is $beta = 1 slash 2$) and simple.
The second says that the gap hypothesis at $Delta$ holds if and only if no two distinct nontrivial zeros with $abs(beta - 1 slash 2) < Delta$ share an ordinate; the third restates this through the pair sum, as the vanishing for every $T$ of $P(T)$ restricted to such zeros.
The proofs use the reflection symmetry of the zeros, taken from the zeta23 library (`zetaZeroConfig.reflect_mem`), and elementary logic; the third also needs complex conjugation, for the zeros with negative ordinates, and the fact that no nontrivial zero is real, because the windows see positive ordinates only.
These equivalences relocate RH with simplicity, and the gap hypothesis, to statements about coincident ordinates.
Each side is as open as the other, and neither is proved.

== No real zeros in the interval (0,1) <sec-no-real-zeros-in-the-interval-0-1>

```lean
@MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo : ∀ {σ : ℝ}, 0 < σ → σ < 1 → riemannZeta ↑σ ≠ 0
```

// The paragraph and the display it introduces stay on one page (the block changes no spacing).
#block(breakable: false, above: 0.95em, below: 0.95em)[
For real $0 < sigma < 1$, $zeta(sigma) != 0$; hence every nontrivial zero has a nonzero ordinate (#breakable(`nontrivial_zero_im_ne_zero`, "_")).
The proof takes one term of Euler–Maclaurin, the tree's `Zeta0EqZeta` at $N = 1$ (a port from PrimeNumberTheoremAnd~@pnt-plus):
$ zeta(sigma) = sigma/(sigma - 1) - 1/2 + sigma J(sigma), wide J(sigma) = integral_1^infinity (floor(x) + 1/2 - x)/x^(sigma + 1) dif x, wide abs(J(sigma)) <= 1/(2 sigma) . $
]

A zero would require $sigma J(sigma) = 1 slash (1 - sigma) - 1 slash 2 > 1 slash 2$, against $abs(sigma J(sigma)) <= 1 slash 2$.

The fact is classical and elementary; the source records only that it was absent from the tree and not found in Mathlib at the pinned commit.
It is not new in Lean: AxiomMath's ZetaZerosV2~@axiom-zetazeros proved it by the same route in a file committed 2026-10-03, and goldbach-lean~@hubbard-goldbach-lean has it as well (both files were read for this paper; neither was built or re-checked here).
It concerns the real segment only, not the interior of the strip, and bears on neither RH nor the gap hypothesis.
