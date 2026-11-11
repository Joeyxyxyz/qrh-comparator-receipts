// rtable is not visible through #include (an included file has its own scope), so it is imported here;
// the path is root-relative, so it resolves the same from typ/ and from a file in the typst/ folder.
#import "/template.typ": rtable

= Introduction <sec-introduction>

This paper reports eleven runs of Comparator~@comparator, the Lean FRO's proof judge, made on one laptop between 2026-10-27 and 2026-11-11 (UTC) under a pinned, sandboxed protocol, each with a published receipt.
Two runs re-check public machine-checked Lean 4~@lean4 proofs about the zeros of the Riemann zeta function $zeta$.
Nine judge Lean files placed on top of the two verified trees: the author's library `MNF.RH`, and a further layer that includes formalizations of classical theorems on the zeros.
The receipts, the scripts and the Lean sources are in a public repository, called _the record_ below.

A machine-checked proof moves trust from the argument to the statement file, the kernel, the permitted axioms and the build.
A reader who cannot follow 486,490 lines of Lean can still read a nine-line statement file and ask whether the kernel accepted the proof against exactly that statement, and from which sources.
An ordinary build does not settle this, because it believes the compiled files it imports; Comparator compares statements and definitions, checks the axioms, and replays the exported proof through the kernel.
A second party who repeats that check from pinned sources leaves a receipt that others can audit: a record, not a cryptographic proof.

== The artifacts and what was added <sec-the-artifacts-and-what-was-added>

The first artifact is OpenAI's theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`~@openai-math #cite(<openai-qrh>): $zeta(s) != 0$ for $op("Re") s > 7 slash 8$.
The second is zeta23~@anthropic-formal-math, Anthropic's formalization of the theorem of Alpöge and Furman~@alpoge-furman that more than two thirds of the zeros of $zeta$ are simple and on the critical line; its statement file holds 17 theorems.
The arXiv listing of~@alpoge-furman states that the proof was discovered autonomously by Claude (Anthropic) and verified and communicated by the listed authors; OpenAI's repository describes its manuscripts and proof artifacts as produced by an internal OpenAI model.
Runs 1 and 2 started from trees in which nothing of the challenge or of the proof had been compiled (the compiled dependencies, Mathlib's prebuilt cache among them, were in place; see~@sec-the-trust-base) and ended with the verdict PASS.

Runs 3 to 6 judge `MNF.RH`, the library of the author's "Messina Nullification Framework" (MNF), on each verified tree.
MNF is the author's name for the framework these Lean files are written for; its "nullification" is the thresholding map $x |-> x dot bold(1) [abs(x) >= Delta]$ on real numbers.
The library's central notion, the "spectral gap hypothesis" at threshold $Delta$, says that every nontrivial zero #box[$rho = beta + i gamma$] has $beta = 1 slash 2$ or $abs(beta - 1 slash 2) >= Delta$; the library proves that this is exactly the absence of zeros with $1 slash 2 < op("Re") s < 1 slash 2 + Delta$.
Runs 7 to 11 judge a further layer on the zeta23 tree; run 11 names 534 theorems.
These counts are of theorem names in the Comparator configuration, auxiliary lemmas included; 75 of the 124 of run 7, for instance, are bookkeeping for the author's operators, with "no analytic content" in the words of the record's register (`DEPOSIT_MAP.md`).
Runs 3 to 11 reuse compiled files of the verified trees and report ACCEPTED, the add-ons' word; the kit's protocol reserves PASS for runs in which nothing of the challenge or the proof was compiled beforehand and would call these runs warm (see~@sec-cold-and-warm-runs).
This paper keeps the two words apart.

== Contributions <sec-contributions>

The counting functions are those of~@sec-notation below.
Counts are with multiplicity $m(rho)$, over nontrivial zeros with $0 < gamma <= T$: $N(sigma, T)$ counts those with $beta >= sigma$, and $N_"off" (delta, T)$ those with #box[$abs(beta - 1 slash 2) >= delta$].

+ *A protocol and its receipts*: a kit that pins sources, statement files, toolchain and checker by commit or sha256 hash and runs Comparator unprivileged and sandboxed; 21 control projects, run with the checker of run 1; and a script, `verify_deposit.sh`, that re-checks the sha256 of every deposited tarball, re-reads every verdict from the bundles and compares the judged Lean sources of runs 3 to 5 and 7 to 11 with the add-on tarballs (@sec-verifying-the-record-offline says what it covers and what it does not).
+ *Two replications*: cold PASS verdicts for both external artifacts.
+ *The `MNF.RH` library and its register* (the file `DEPOSIT_MAP.md` of the record) of what is proved, conditional, open, and withdrawn: 40, 43 and 87 theorems on OpenAI's tree and 62 on the zeta23 tree.
  The gap hypothesis is equivalent to the Riemann hypothesis (RH) for $Delta >= 1 slash 2$ and, given OpenAI's theorem, for $Delta > 3 slash 8$; the zero-free strip it asks for is known for no $Delta > 0$.
+ *Formalizations of classical results* on the zeta23 tree, judged with both kernels.
  The Bohr–Landau theorem~#cite(<bohr-landau-1914>): for every $delta > 0$ there is $C_delta$ with $N_"off" (delta, T) <= C_delta T$ for all #box[$T >= 2$] (run 9).
  A zero-density estimate with a power saving, by Carlson's method~#cite(<carlson-1920>): for $1 slash 2 < sigma_1 < sigma <= 1$ there is $C$ with $N(sigma, T) <= C thin T^(1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)) (1 + log T)^3$ for all #box[$T >= 2$] (run 10).
  A bound for the total displacement of the zeros from the critical line: #box[$sum_(0 < gamma <= T) m(rho) thin abs(beta - 1 slash 2) <= A thin T (log T)^(3 slash 5)$] for all large $T$ (run 10).
  The absence of real zeros: $zeta(sigma) != 0$ for real $0 < sigma < 1$ (run 11).
+ *Two equivalences* from the pair-measure module, which is bookkeeping about sums over ordered pairs of zeros (run 11): every nontrivial zero is simple and on the critical line if and only if no nontrivial zero is multiple or shares its ordinate with another nontrivial zero; and the gap hypothesis at $Delta$ holds if and only if no two distinct zeros with $abs(beta - 1 slash 2) < Delta$ share an ordinate.

== What is not claimed <sec-what-is-not-claimed>

- Nothing in this work proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.
  A zero-density estimate is a count and excludes no individual zero.
- The two external theorems belong to OpenAI and to Anthropic and Alpöge–Furman.
  Runs 1 and 2 repeat a check that both repositories ship and that Anthropic reports having run; they are not first verifications.
  A PASS means exactly that the pinned Lean proof was accepted by the Lean kernel (and by NanoDa~@nanoda in run 2) against the pinned statement file, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.
  No result here combines the two theorems.
- The Bohr–Landau theorem (1914), Carlson's zero-density theorem (1920) and the absence of real zeros in $(0,1)$ are classical.
  The contribution is their formalization and receipted checking, with a weaker exponent than Carlson's and a far weaker displacement bound than those of Littlewood~@littlewood-1924 and Selberg~#cite(<selberg-1946>).
  Lean zero-density estimates with stronger exponents were registered earlier by Mark Lewko~@lewko-density-34 @lewko-density-32 @lewko-density-3917 @lewko-density-improved, and earlier Lean proofs of the absence of real zeros exist~@axiom-zetazeros #cite(<hubbard-goldbach-lean>).
- The equivalences of the pair-measure module and of `MNF.RH` relocate RH, simplicity and the gap hypothesis; each side is as open as the other.
  "MNF", "spectral gap hypothesis", "nullification", "reservoir", "cube" and "degenerate" are the author's words, not standard terminology; each is defined in standard terms in the section that uses it.
- The numerical experiments on the first 400 zeros are exploratory, reproduce known behavior of the kind predicted by the Gaussian unitary ensemble (GUE) of random matrix theory~@montgomery-1973 @odlyzko-1987, and prove nothing.
- No unaided authorship is claimed.
  The Lean files of runs 7 to 11, except four supporting files supplied by the author, the additions to `MNF.RH` listed in~@sec-authorship-and-use-of-ai-tools, the scripts and the documents, this paper's text included, were produced with Claude Code~@claude-code, Anthropic's coding agent, under the author's direction; the author conceived the MNF framework, set the goals, operated every run, and is responsible for the claims.

== Plan of the paper <sec-plan-of-the-paper>

@sec-the-checking-protocol describes Comparator, the trust base, the sandbox, the receipts and the lessons learned.
@sec-the-first-six-runs-and-the-mnf-rh-library reports the two replications and the library with its register.
@sec-the-density-layer-counting-vocabulary-and-the-bohrlandau-the and~@sec-a-zero-density-estimate-the-displacement-bound-and-the-pair present the layer of runs 7 to 11, citing earlier Lean work where each result is stated.
@sec-a-numerical-illustration-limitations-and-errata gives exploratory numerics on the first 400 zeros, the limitations of the work and the errata of the record.
@sec-reproducing-and-verifying-the-record says how to verify the deposited files and how to repeat a run, and~@sec-authorship-and-use-of-ai-tools states who and what produced each part.
Appendix~A tabulates the eleven runs, and Appendix~B lists the principal Lean theorems with their register tags.

== Notation <sec-notation>

Throughout, $rho = beta + i gamma$ is a nontrivial zero of $zeta$, so that $0 < beta < 1$, and $m(rho)$ is its multiplicity.
The critical line is $op("Re") s = 1 slash 2$; a zero is on the line if $beta = 1 slash 2$ and off the line otherwise.
Every counting function runs over the zeros with $0 < gamma <= T$ and weights each zero by $m(rho)$.

#figure(
  rtable(columns: 3, align: (left, left, left),
    header: ([Notation], [Lean], [Zeros counted]),
    [$N(T)$], [`MNF.RH.Ncount 0 T`], [all],
    [$N_0(T)$], [`MNF.RH.N0 0 T`], [$beta = 1 slash 2$],
    [$N_(!=)(T)$], [`MNF.RH.NOffLine 0 T`], [$beta != 1 slash 2$],
    [$N_"off" (delta, T)$], [`MNF.RH.NOff δ 0 T`], [$abs(beta - 1 slash 2) >= delta$],
    [$N(sigma, T)$, $sigma = 1 slash 2 + delta$], [`NRight δ T`, in `MNF.RH` and with the same body in `Zeta23.BL`], [$beta >= sigma$],
  ),
)

Thus $N(T) = N_0(T) + N_(!=)(T)$.
Three further symbols are used.
$G(Delta)$ is the spectral gap hypothesis at threshold $Delta$ defined above (Lean: `MNF.RH.SpectralGapHyp Δ`).
$D(T) = sum_(0 < gamma <= T) m(rho) thin abs(beta - 1 slash 2)$ is the total displacement of the zeros from the critical line (Lean: `MNF.RH.reservoirMass T`).
$P(T)$ is the sum of $m(rho) thin m(rho')$ over ordered pairs of distinct zeros with equal ordinates in $0 < gamma <= T$ (Lean: `MNF.RH.offDiagonalCoincidentMass T`).
RH is the Riemann hypothesis; in Lean statements it is Mathlib's proposition `RiemannHypothesis`.
In the proof sketches, $N$ without an argument is the length of a Dirichlet polynomial.

In Lean each of these counts is a sum `∑ᶠ` of the multiplicity (`zeta_order`) over the zeros of the window, and $D(T)$ and $P(T)$ are sums `∑ᶠ` of the same kind.
Mathlib's `∑ᶠ` is 0 by convention when infinitely many of its terms are nonzero; in the words of `Counting.lean`, such a count "would be vacuously 0 on an infinite set".
The reading as a count therefore needs the fact that a window contains finitely many zeros.
That fact is the theorem `MNF.RH.zerosIn_finite`, judged in runs 5 and 6.
In runs 7 to 11 it is not in the claim set; the claimed proofs that use it depend on it, and the kernel replay covers what the claimed proofs depend on (see~@sec-comparator-and-what-an-acceptance-means).
The statement file of zeta23 says of its own counting function that finiteness "is proved on the solution side, not assumed"; no statement of finiteness is among the 17 theorems of run 2.

Lean statements are printed verbatim.
In them `↑` is a coercion (from natural to real numbers, or from real to complex numbers).
The statements quoted from the report of run 5 are in signature form, with named binders; in those quoted from the run 11 bundle a leading `@` appears where the first argument of the theorem is implicit.
Times are UTC.
Run numbers are the record's and are not chronological (Appendix~A).
