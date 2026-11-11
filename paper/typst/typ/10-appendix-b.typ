// rtable is defined in the template; #include does not pass the including file's imports on to this fragment,
// so it is imported here (the path is root-relative and resolves the same from the harness and from main.typ).
#import "/template.typ": rtable

// The same heading numbering as file 09. The counter is not reset: this heading follows Appendix A.
#set heading(numbering: (..n) => [Appendix #numbering("A", ..n).], supplement: [Appendix])

// Line-break opportunities inside long code: after a dot in a Lean name (lname), after a slash in a file path (lpath).
// The empty box has no size and no text: nothing is inserted into the name, and a copied name stays intact.
#let breakable(it, after) = {
  let parts = it.text.split(after)
  for (i, p) in parts.enumerate() {
    if i + 1 < parts.len() { raw(p + after); box() } else { raw(p) }
  }
}
#let lname(it) = breakable(it, ".")
#let lpath(it) = breakable(it, "/")

// The table has five columns, two of them long Lean names and module paths: it does not fit a portrait page,
// so the appendix is set on landscape pages, as Appendix A is. The table is not wrapped in a figure: it breaks
// across pages and repeats its header.
#page(flipped: true, margin: (x: 0.7in, y: 0.8in))[
= Principal Lean theorems <sec-appendix-b-principal-lean-theorems>

Names are as in the receipts.
Modules under `Zeta23/BL/` and `Zeta23/Density/`, and the names in `Zeta23.BL`, `Zeta23.Density`, `BLClosure`, `M1` and `DPMV` listed below, belong to the layer of this work and not to Anthropic's library, in whose tree they are compiled.
The readings use the symbols of~@sec-notation, among them $G(Delta)$, $D(T)$, $N_(!=)(T)$ and $P(T)$.
Constants such as $C$, $A$, $B$ and $T_0$ are asserted to exist, not given.
The tags are the register's: [PROVED], from Mathlib alone; [PROVED | 7/8], from Mathlib and OpenAI's theorem; [PROVED | this tree], on the zeta23 checkout, from Mathlib, the zeta23 library and sorry-free declarations of the layer (the supporting file `Zeta23/BohrLandau.lean` also holds two `sorry` lemmas, on which no claimed theorem depends: every axiom report lists only the three standard axioms); [CONDITIONAL], from explicit named hypotheses; [RESTATEMENT | zeta23], a theorem of zeta23 under the library's names, or (the two rows of run 7) a short consequence of one, derived in the supporting files `Zeta23/Superlinear.lean` and `Zeta23/OffLine.lean` of this layer; [EXTERNAL | run here], an artifact of others re-checked here.
For the two Mathlib-only lemmas of run 7, which the register does not list, the tag is that of the README of add-on v6.
The three statements of `Cube.lean` that carry the two equivalences (the second in two forms) are tagged [PROVED | this tree], because their proofs use the reflection lemma `zetaZeroConfig.reflect_mem` of the zeta23 library, and the third also the real-zero theorem; until its revision of 2026-11-11 the register printed [PROVED] for them.
"Run" is the first run that judged the statement.
For the two rows of run 3 that mention the gap hypothesis, run 3 compared the library's definitions as holes; their bodies were first compared in run 4.
No row proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

// A row is kept on one page.
#set table.cell(breakable: false)
#rtable(
  columns: (184pt, 120pt, 1fr, 112pt, auto),
  align: (left, left, left, left, center),
  size: 8.4pt,
  header: ([Lean name], [Module], [Reading], [Register tag], [Run]),
  lname(`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`), [#lname(`OAI.NumberTheory.DirichletL.Nonvanishing`) (OpenAI)], [$zeta(s) != 0$ for $op("Re") s > 7 slash 8$], [[EXTERNAL | run here]], [1],
  [`two_thirds_simple_on_critical_line`], [`Solution` (zeta23, Anthropic)], [for every $epsilon > 0$ and all large $T$, the simple zeros on the line with $T < gamma <= 2T$ number at least $(2 slash 3 - epsilon)$ times all zeros in that window, the latter counted with multiplicity], [[EXTERNAL | run here]], [2],
  lname(`MNF.RH.riemannHypothesis_iff_gap_half`), lpath(`MNF/RH/Gap.lean`), [for $Delta >= 1 slash 2$: RH $<==> G(Delta)$], [[PROVED]], [3],
  lname(`MNF.RH.riemannHypothesis_iff_gap_three_eighths`), lpath(`MNF/RH/Unconditional.lean`), [for $Delta > 3 slash 8$: RH $<==> G(Delta)$], [[PROVED | 7/8]], [3],
  lname(`MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths`), lpath(`MNF/RH/Unconditional.lean`), [RH $<==>$ $zeta$ has no zeros with $1 slash 2 < op("Re") s <= 7 slash 8$], [[PROVED | 7/8]], [3],
  lname(`MNF.RH.spectralGapHyp_iff_zeroFree_strip`), lpath(`MNF/RH/Hypotheses.lean`), [for every real $Delta$: $G(Delta) <==>$ $zeta$ has no zeros with #box[$1 slash 2 < op("Re") s < 1 slash 2 + Delta$]], [[PROVED]], [4],
  [`sturm_liouville_simple_eigenvalues`], lpath(`SturmLiouville/SimpleEigenvalues.lean`), [for continuous $V$ with $V(x) -> +infinity$ as $abs(x) -> infinity$, any two $L^2$ eigenfunctions of $-u'' + V u = lambda u$ are proportional (not a statement about $zeta$)], [[PROVED]], [5],
  lname(`MNF.RH.on_line_density_one_of_gap`), lpath(`MNF/RH/GapDensity.lean`), [if Bohr–Landau, the superlinear growth of $N(T)$ and $G(Delta)$ for some $Delta > 0$ are assumed, then $N_0(T) >= (1 - epsilon) N(T)$ for large $T$], [[CONDITIONAL]], [5],
  lname(`MNF.RH.twoThirdsSimpleOnLine`), lpath(`MNF/RH/Zeta23Restated.lean`), [zeta23’s `two_thirds_simple_on_critical_line` over the library's counting functions, by definitional unfolding], [[RESTATEMENT | zeta23]], [6],
  lname(`MNF.RH.ncountSuperlinear`), lpath(`MNF/RH/Density.lean`), [for every $c > 0$, $N(T) >= c T$ for large $T$ (from zeta23’s Riemann–von Mangoldt formula)], [[RESTATEMENT | zeta23]], [7],
  lname(`MNF.RH.offLine_le_one_third`), lpath(`MNF/RH/Density.lean`), [$N_(!=)(T) <= (1 slash 3 + epsilon) N(T)$ for large $T$ (zeta23’s Theorem B read as an upper bound)], [[RESTATEMENT | zeta23]], [7],
  lname(`DPMV.dirichlet_mean_value`), lpath(`Zeta23/BL/DPMV.lean`), [for $T > 0$: $integral_0^T abs(sum_(n <= N) a_n n^(-i t))^2 dif t <= T sum_n abs(a_n)^2 + sum_(m != n) 2 thin abs(a_m) thin abs(a_n) slash abs(log(n slash m))$ (the elementary form; the mean square of $zeta$ uses the Montgomery–Vaughan form `M1.dirichlet_meanSquare_le`, step 5 of~@sec-architecture-of-the-formal-proof)], [[PROVED]], [7],
  [`sum_divisor_mul_log_le`], lpath(`Zeta23/BL/JensenDisc.lean`), [for $f$ analytic near the closed disk of radius $R$ about $c$, #box[$f(c) != 0$], #box[$0 < r < R$]: the number of zeros within $r$ of $c$, counted with multiplicity, times $log(R slash r)$, is at most the average of $log abs(f)$ on the circle of radius $R$ minus $log abs(f(c))$], [[PROVED]], [7],
  lname(`Zeta23.BL.bohrLandau_gt_sixth`), lpath(`Zeta23/BL/BohrLandauPartial.lean`), [for every $delta > 1 slash 6$: $N_"off" (delta, T) <= C T$ for $T >= 2$], [[PROVED | this tree]], [8],
  lname(`BLClosure.zeta_approx_sharp`), lpath(`Zeta23/BL/BohrLandauClosure.lean`), [for $sigma_0 > 0$: $abs(zeta(s) - sum_(n <= N) n^(-s) - N^(1-s) slash (s-1)) <= C N^(-sigma)$ for #box[$s = sigma + i t != 1$] with $sigma_0 <= sigma <= 2$ and integers $N >= 1$ with #box[$0 <= t <= N$]], [[PROVED | this tree]], [9],
  lname(`BLClosure.meanSquareUnif_all`), lpath(`Zeta23/BL/BohrLandauClosure.lean`), [for $sigma_1 > 1 slash 2$: $integral_1^T abs(zeta(sigma + i t))^2 dif t <= C T$ for all $sigma >= sigma_1$ and $T >= 2$], [[PROVED | this tree]], [9],
  lname(`Zeta23.BL.bohrLandau_full`), lpath(`Zeta23/BL/BohrLandauClosure.lean`), [the Bohr–Landau theorem: for every $delta > 0$ there is $C_delta$ with $N_"off" (delta, T) <= C_delta T$ for $T >= 2$], [[PROVED | this tree]], [9],
  lname(`MNF.RH.reservoirDensityOne_unconditional`), lpath(`Zeta23/BL/BohrLandauClosure.lean`), [for every $delta > 0$ and $epsilon > 0$: $N_"off" (delta, T) <= epsilon N(T)$ for large $T$], [[PROVED | this tree]], [9],
  lname(`MNF.RH.onLineDensityOne_of_gap_only`), lpath(`Zeta23/BL/BohrLandauClosure.lean`), [if $G(Delta)$ holds for some $Delta > 0$, then $N_0(T) >= (1 - epsilon) N(T)$ for large $T$], [[CONDITIONAL] on the gap alone], [9],
  lname(`Zeta23.BL.bohrLandau_explicit`), lpath(`MNF/RH/ReservoirMass.lean`), [$N_"off" (delta, T) <= (A thin delta^(-5 slash 2) + B) thin T$ for $0 < delta <= 1 slash 2$ and $T >= 2$], [[PROVED | this tree]], [10],
  lname(`MNF.RH.reservoirMass_eq_integral`), lpath(`MNF/RH/ReservoirMass.lean`), [$D(T) = integral_0^(1 slash 2) N_"off" (delta, T) dif delta$], [[PROVED] bookkeeping], [10],
  lname(`MNF.RH.reservoirMass_le_rpow`), lpath(`MNF/RH/ReservoirMass.lean`), [$D(T) <= A thin T thin (log T)^(3 slash 5)$ for $T >= T_0$], [[PROVED | this tree]], [10],
  lname(`MNF.RH.meanDisplacement_tendsto_zero`), lpath(`MNF/RH/ReservoirMass.lean`), [$D(T) slash N(T) -> 0$ as $T -> infinity$], [[PROVED | this tree]], [10],
  lname(`Zeta23.Density.density_single_window`), lpath(`Zeta23/Density/StripDensity.lean`), [for $1 slash 2 < sigma_1$ and $sigma_1 - 1 slash 2 < delta <= 1 slash 2$: #box(inset: (top: 1.5pt))[$N(1 slash 2 + delta, T) <= C thin T^(1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)) thin (1 + log T)^3$] for $T >= 2$], [[PROVED | this tree]], [10],
  lname(`MNF.RH.noDegenerate_iff`), lpath(`MNF/RH/Cube.lean`), [no nontrivial zero is degenerate (multiple, or sharing its ordinate with another nontrivial zero) $<==>$ every nontrivial zero is simple and has $beta = 1 slash 2$], [[PROVED | this tree]; an equivalence], [11],
  lname(`MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`), lpath(`MNF/RH/Cube.lean`), [for every real $Delta$: $G(Delta) <==>$ no two distinct nontrivial zeros with $abs(beta - 1 slash 2) < Delta$ share an ordinate], [[PROVED | this tree]; an equivalence], [11],
  lname(`MNF.RH.spectralGapHyp_iff_bandCoincidentMass`), lpath(`MNF/RH/Cube.lean`), [for every real $Delta$: $G(Delta) <==>$ for every $T$, the part of $P(T)$ from pairs with both zeros in $abs(beta - 1 slash 2) < Delta$ is $0$], [[PROVED | this tree]; an equivalence], [11],
  lname(`MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo`), lpath(`MNF/RH/Cube.lean`), [$zeta(sigma) != 0$ for real $0 < sigma < 1$], [[PROVED | this tree]], [11],
  lname(`MNF.RH.offDiagonalCoincidentMass_le_five_ninths`), lpath(`MNF/RH/Cube.lean`), [$P(T) <= (5 slash 9 + epsilon) thin N(T)^2$ for large $T$], [[PROVED | this tree]], [11],
)

The first two rows are theorems of OpenAI and of Anthropic and Alpöge–Furman; runs 1 and 2 repeat checks of them and are not first verifications.
The Bohr–Landau theorem~@bohr-landau-1914 and the absence of real zeros in $(0,1)$ are classical; the zero-density estimate follows Carlson's method~@carlson-1920 with a weaker exponent than Carlson's, and the displacement bound is far weaker than those of Littlewood~@littlewood-1924 and Selberg~#cite(<selberg-1946>).
Lean formalizations of stronger zero-density estimates~@lewko-density-3917 and of the absence of real zeros~@axiom-zetazeros @hubbard-goldbach-lean were public earlier.
The equivalences in the rows of runs 3, 4 and 11 relocate the Riemann hypothesis, simplicity or the gap hypothesis; each side is as open as the other.
]
