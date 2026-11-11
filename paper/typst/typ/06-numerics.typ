// The harness pulls this file in with #include, which does not pass on the template's definitions; rtable needs this import.
#import "/template.typ": rtable

= A numerical illustration, limitations and errata <sec-a-numerical-illustration-limitations-and-errata>

== A numerical illustration <sec-a-numerical-illustration>

The first 400 ordinates ($gamma_1 = 14.134725$ to $gamma_(400) = 679.742198$) were recomputed in double-precision Python (scripts written with Claude Code~@claude-code under the author's direction; no interval arithmetic) from sign changes of Hardy's function, by the Riemann–Siegel formula and then Euler–Maclaurin summation.
The scan found 414 zeros below height 700, against 414.557 from the smooth term of the Riemann–von Mangoldt formula; eleven ordinates agree, to within #box[$3.3 times 10^(-10)$], with tabulated values (the public tables of Odlyzko and the LMFDB); the comparison values are constants in the script, which was written with Claude Code and marks them "as recalled", and they were not read from the tables for this work.

The normalized spacings $s_n = (gamma_(n+1) - gamma_n) log(gamma_n slash 2 pi) slash (2 pi)$, $1 <= n <= 399$, have mean 0.99744, standard deviation 0.3709 (Wigner surmise, the approximation $(32 slash pi^2) thin s^2 e^(-4 s^2 slash pi)$ to the GUE spacing density: 0.4220) and minimum 0.2434.

#align(center, block(breakable: false, rtable(
  columns: 4,
  align: (left, right, right, right),
  header: ([$x$], [spacings with $s_n < x$], [expected, exact GUE law], [expected, Poisson (spacing density $e^(-s)$)]),
  [0.2], [0], [3.4], [72.3],
  [0.3], [4], [11.0], [103.4],
  [0.5], [29], [45.1], [157.0],
  [1], [224], [213.0], [252.2],
)))

The Kolmogorov–Smirnov distance of the spacings is 0.0508 from the exact GUE spacing law ($p approx 0.247$) and 0.3285 from Poisson (#box[$p approx 2.7 times 10^(-38)$]).
Log-log slopes fitted on $0.25 <= x <= 0.75$ are 4.52 (bootstrap 16–84% band $[4.07, 5.05]$) for the fraction of the total spacing length lying in spacings below $x$ and 3.71 ($[3.26, 4.23]$) for their number, against 3.62 and 2.67 for GUE and 1.71 and 0.79 for Poisson.
The fitted slopes exceed the GUE values on this window; the notes rate this "a \~2-2.5 sigma effect on 400 zeros", in the direction expected for low zeros, and it is not presented here as a finding.
Ordered pairs of distinct zeros at normalized distance at most 0.5 number 0.145 per zero (GUE 0.2263, Poisson 1).

#page(flipped: true, margin: (x: 0.8in, y: 0.9in))[
  #figure(
    image("/figures/cascade-relabeled.svg", width: 100%),
    caption: [(exploratory; proves nothing). Normalized spacings of the first 400 zeros. Panel A: fraction of the total spacing length in spacings below a threshold $x$, against GUE and Poisson; panel B: histogram of the spacings. Panel A uses the exact GUE spacing law and panel B the Wigner surmise, which is why the expected number of spacings below 0.2 reads 3.4 in one and 3.3 in the other. The ordinates are uncertified; "re-located" means found again by a second formula, without error bounds. The threshold $x$ acts on spacings of ordinates: it is unrelated to the threshold $Delta$ of the gap hypothesis, which concerns real parts, and to any zero-free strip. The image is `numeric/cascade.svg` of the record's notes with its text labels edited for this paper; the plotted data are unchanged.],
  ) <fig-cascade>
]

#page(flipped: true, margin: (x: 0.8in, y: 0.9in))[
  #figure(
    image("/figures/cube-relabeled.svg", width: 90%),
    caption: [(exploratory; proves nothing). The pair measure of the first 400 zeros (the author's "cube"); in the image delta1 and delta2 are the values of #box[$beta - 1 slash 2$] for the two zeros of a pair. Panel A is a schematic: the data lie on one axis and the shaded zones contain no data. The zone labels give the status of statements about all zeros and are not results of this computation: the zone #box[$abs(beta - 1 slash 2) > 3 slash 8$] contains no zeros by OpenAI's theorem and the reflection symmetry; the bound $O(T^(1-c))$ for the zeros with #box[$abs(beta - 1 slash 2) >= Delta$] is Carlson's classical theorem, of which run 10 formalizes a weaker form for the right half; that the band #box[$0 < abs(beta - 1 slash 2) < Delta$] is empty is the gap hypothesis, which is unproved. The ticks marked D stand for $plus.minus Delta$. That all 400 zeros are simple and on the line rests on the uncertified computation described above. Panel B: pairs per zero within normalized distance $x$, against GUE, Poisson and a cubic reference; the cubic law is a GUE prediction, not a theorem. The image is `numeric/cube.svg` of the record's notes with its text labels edited for this paper; the plotted data are unchanged.],
  ) <fig-cube>
]

These computations are exploratory and prove nothing.
They concern spacings of ordinates on the critical line, not real parts, and bear on none of RH, the simplicity of the zeros, or a zero-free strip.
GUE statistics for the zeros are conjectural~@montgomery-1973, and the repulsion seen is known behavior~#cite(<odlyzko-1987>).
With no spacing below 0.243, the small-$x$ exponents of the GUE law (4 and 3) are not observable; the slopes are finite-window values.
The bands and $p$-values treat the spacings as independent and are indicative only.
The ordinates are uncertified, and the completeness of the list rests on the count above, not on a Turing-style argument.
That the zeros at these heights are on the critical line is known from rigorous computation~#cite(<platt-trudgian-2021>).

== Limitations <sec-limitations>

_Mathematics._ Nothing here proves, or is evidence for, RH, the simplicity of the zeros, or a zero-free strip next to the critical line.
The gap hypothesis stays open for every $Delta > 0$; the equivalences of the MNF library and of the pair-measure module only relocate it, or RH with simplicity.
The Bohr–Landau theorem, the zero-density estimate and the displacement bound are counts and averages: they exclude no individual zero and are compatible with infinitely many zeros off the line.
They are also weak: the density exponent $1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)$, receipted for the right half only, falls short of Carlson's $4 sigma_1 (1 - sigma_1) = 1 - (2 sigma_1 - 1)^2$~@carlson-1920 and of Lean estimates registered earlier~@lewko-density-3917; the displacement bound $O(T (log T)^(3 slash 5))$ falls short of the classical $O(T log log T)$~@littlewood-1924 and $O(T)$~@selberg-1946; and the receipted statements of all three are existential in their constants.

_Checks._ Each tree is pinned (Lean v4.34.1 with Mathlib `d13f23b7`; Lean v4.33.0-rc2 with Mathlib `51e6992e`); the results are statements about those versions.
One operator made all eleven runs on one laptop in a single boot (@sec-authorship-and-use-of-ai-tools says what the record tells about the operation), and a receipt is a record, not a cryptographic proof.
Every acceptance depends on everything listed in~@sec-the-trust-base, and no tool checks that a Lean statement matches its English reading.
Runs 3 to 11 reuse the compiled trees of runs 1 and 2, and runs 7 to 11 also the modules of this work compiled by the runs before them; they are reported as ACCEPTED, and under the kit's protocol, which reserves PASS for cold runs, they are warm runs, for which the kit closes none of the exposures it lists.
Most of the receipted runs repeated an acceptance already obtained on the author's own account, and the challenges of runs 3 to 11 are generated from the solutions' own sources (see~@sec-cold-and-warm-runs and~@sec-challenges-as-module-for-module-mirrors).
The 21 controls were run with one of the two checkers only, and run 2 was launched by an add-on version other than the deposited one (see~@sec-receipts-and-the-verifier).
All eleven runs used the standalone Comparator after its repository had been archived; its README says that only the Lake commands are guaranteed to receive further security and performance improvements.

== Errata <sec-errata>

_The run 9 report._ Its block "How to read this", fixed prose of the report generator, says "Bohr–Landau itself is NOT proved", which was true for runs 7 and 8.
For run 9 it is false: the same report prints `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau` and lists it with the three standard axioms.
Verdict, audit and hashes are unaffected.
The generator was corrected in add-on v5, the reports of runs 10 and 11 carry the corrected prose, the register and the README record the erratum, and the bundle was not altered.

_A bound corrected before it was claimed._ The plan of the pair-measure module had the bound $P(T) <= N_(!=)(T) thin N(T)$, hence an eventual constant $1 slash 3 + epsilon$.
It is false as bookkeeping; @sec-the-pair-measure gives the counterexample.
The error was found during the formalization, and the false statement is in no Lean declaration or receipt.
Run 11 judged the corrected bound #box[$P(T) <= N_(!=)(T) thin (N(T) + N_0(T))$] (`MNF.RH.offDiagonalCoincidentMass_le`), with the eventual constants $2 slash 3 + epsilon$ and $5 slash 9 + epsilon$.

_Found while preparing this paper._ The "What was proved" block of the run 11 report prints only 255 of the 534 judged statements: its generator drops those that Lean prints with a leading `@`, `Zeta23.Density.density_single_window` among them; all 534 are in the axiom table and in `audit.out`.
The reports of runs 4 to 11 say that the definitions of the challenge were "all compared by name, type and body"; the number they give counts `def` lines, and Comparator compares those that a claimed statement refers to (see~@sec-runs-3-to-6-the-library-judged and Appendix~A).
The notes give the standard deviation of the normalized spacing for GUE as 0.4221 (`numeric/RESULTS.md`); that value is a constant typed into `mnf_analysis.py` as "exact GUE sd", the Wigner surmise gives 0.4220, and a recomputation of the exact law made while this paper was reviewed gave 0.4243 (`numeric/gue_sd.py` in the notes).

_A provisional priority claim in the notes._ The working notes of run 10 (`strip/STRIP_PLAN.md`, `strip/STRIP_SCOPE_REPORTS_2026-11-04.md`) call its target "the first kernel-checked zero-density estimate with a power saving", subject to reading Lewko's Palomar entries.
The registry entries have since been read, and the statement file of one of them (see~@sec-the-zero-density-estimate); the description does not hold, and this paper makes no such claim.

_Corrected in the record while this paper was prepared._ Up to commit `f03aaa9`, which added run 11, the register and the README carried statements that this paper does not repeat.
They were corrected at the commit cited in~@sec-availability, and the register lists them (its section 10, errata of 2026-11-11); the reports inside the bundles are unchanged.
The reports of runs 3 to 5 say that `gap_below_bound_insufficient` "says a gap at Δ #text(font: "New Computer Modern Math", weight: 450)[≤] 3/8 cannot give it" (RH), and the register called the gap hypothesis "insufficient for every Δ #text(font: "New Computer Modern Math", weight: 450)[≤] 3/8" and the threshold "exact".
The Lean statement concerns an abstract symmetric set of real numbers, not the zeros of $zeta$; whether $G(Delta)$ implies RH for such $Delta$ is not decided by it (if RH holds, the implication holds trivially), and~@sec-the-mnf-rh-library-in-standard-terms says only where the argument stops.
The README said that both authors report Comparator runs of their own; for OpenAI the files read show a configuration and an instruction, not a reported run.
The register called runs 7 to 11 cold and said that every definition was compared by body; the receipts record warm runs, and the definition counts are upper bounds.
The README and the register attributed the mean-square bound to Hardy and Littlewood; that attribution was not checked and is not made here.
The README called the real-zero theorem a "new unconditional fact", meaning new to the tree; the fact is classical and has earlier Lean proofs (see~@sec-no-real-zeros-in-the-interval-0-1).

== What would strengthen the work <sec-what-would-strengthen-the-work>

The plan's route to Carlson's exponent, approximate formulas of length $N approx t$ on dyadic windows, was a stretch target and was not carried out.
Porting the layer to current Lean and Mathlib and re-judging it with the `lake comparator` that ships with Lean 4.35.0~@lean-4-35 would end the dependence on two frozen pins and on the standalone Comparator, whose repository is now archived~#cite(<comparator>).
A certified computation of the first 400 ordinates (interval arithmetic with a Turing-type completeness check, or a Lean-checked verification), which the record lacks, would replace the uncertified list of zeros behind the illustration and make its finite counts rigorous; the comparison with GUE would remain statistical, and nothing would follow beyond that height.
Numerically, RH is verified up to height #box[$3 dot 10^(12)$]~#cite(<platt-trudgian-2021>).
The controls could be repeated with the second checker, Mathlib compiled from source inside the sandbox, and the runs repeated by another operator on another machine.
A cold run of the complete layer, on a fresh checkout in which Comparator compiles the zeta23 library and the layer together, would remove the warm status of runs 6 to 11; the same holds for the library on OpenAI's tree, at the cost of compiling OpenAI's proof again (1 h 54 min 37 s in run 1).
