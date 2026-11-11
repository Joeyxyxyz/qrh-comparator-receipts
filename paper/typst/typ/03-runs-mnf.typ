// #include does not pass the including file's imports to this fragment, so rtable is imported here (root-relative path).
#import "/template.typ": rtable

= The first six runs and the MNF.RH library <sec-the-first-six-runs-and-the-mnf-rh-library>

Runs 1 and 2 repeat the Comparator checks of the two external theorems; runs 3 to 6 judge the author's Lean library `MNF.RH` on the two verified trees.
Nothing in this section proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

== Runs 1 and 2: the two replications <sec-runs-1-and-2-the-two-replications>

Run 1 (label `qrh-main`) checked one theorem of OpenAI's repository~@openai-math at commit `adc7f124`, the Lean theorem that accompanies the manuscript~#cite(<openai-qrh>).
Its challenge file states, in the namespace `OAI`:

```lean
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  sorry
```

The receipt gives the proof's size as 2,924 project files and 486,490 lines, third-party files apart, on Lean v4.34.1.
The run was cold (nothing of the proof had been compiled on the machine before), started at 2026-10-27T17:43:45Z, took 1 h 54 min 37 s, and ended with exit code 0 and the verdict PASS.
Only Lean's kernel replayed the proof.

Run 2 (label `zeta23-main`) checked the 17 statements of Anthropic's zeta23~@anthropic-formal-math at commit `16a5ce41`, which formalizes the theorem of Alpöge and Furman~#cite(<alpoge-furman>): eleven statements about $zeta$ and six about Dirichlet $L$-functions, each a proportion in $epsilon$-form.
For example, `two_thirds_simple_on_critical_line` says that for every $epsilon > 0$ and all large $T$, at least $(2 slash 3 - epsilon)(N(2T) - N(T))$ zeros with $T < gamma <= 2T$ are simple and on the critical line.
The words "more than two thirds" are the title of~#cite(<alpoge-furman>): in the statements judged here the constants are $2 slash 3 - epsilon$ and $5 slash 6 - epsilon$ and, in the statements with `montgomery_taylor` in their names, symbolic constants whose decimal values (0.67250 and 0.83625) are, in the register's words, "docstrings, not statements".
The proof is 316 files and 102,265 lines, on Lean v4.33.0-rc2.
The run was cold, started at 2026-10-28T11:08:56Z, took 21 min 1.5 s, and ended with exit code 0 and the verdict PASS.
Lean's kernel and NanoDa~@nanoda replayed the proof.

What a PASS certifies is stated in~@sec-comparator-and-what-an-acceptance-means: the pinned proof was accepted by the Lean kernel (and by NanoDa in run 2) against the pinned statement file, using only the axioms `propext`, `Quot.sound` and `Classical.choice`.
Neither run is a first verification (see~@sec-the-two-artifacts-under-test-and-their-trusted-statement-fil).

== The MNF.RH library in standard terms <sec-the-mnf-rh-library-in-standard-terms>

The library `MNF.RH` consolidates the files on RH of the author's earlier Lean collection (the "corpus").
Its vocabulary is the author's, not standard terminology.
In standard terms:

- the "shifted zero spectrum" `ShiftedZeroSpectrum` is the set $S$ of the real numbers $beta - 1 slash 2$ (no operator is involved);
- the spectral gap hypothesis $G(Delta)$ of the Introduction is `SpectralGapHyp Δ`, defined as `SpectralGapProperty ShiftedZeroSpectrum Δ`: every point of $S$ is $0$ or has absolute value at least $Delta$;
- "nullification" at threshold $Delta$, `nullify Δ`, sends a real number $x$ to $x$ if $abs(x) >= Delta$ and to $0$ otherwise; by `gap_iff_nullify_id`, $G(Delta)$ says that this map fixes every point of $S$.

`RiemannHypothesis` is Mathlib's own proposition~#cite(<mathlib>).
The record's register tags each statement: `[PROVED]`, kernel-checked from Mathlib alone; `[PROVED | 7/8]`, from Mathlib plus OpenAI's theorem, hence exactly as reliable as run 1; `[CONDITIONAL]`, proved from explicit named hypotheses; `[LITERATURE]`, a published theorem stated as a hypothesis, not formalized; `[OPEN]`; `[WITHDRAWN]`.
The statements below are as Lean prints them in the report of run 5.

The gap hypothesis is equivalent to a zero-free strip (the equivalence is tagged `[PROVED]`; neither side is proved):

```lean
MNF.RH.spectralGapHyp_iff_zeroFree_strip {Δ : ℝ} :
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 / 2 + Δ → riemannZeta s ≠ 0
```

For every real $Delta$, $G(Delta)$ holds if and only if $zeta$ has no zeros with $1 slash 2 < op("Re") s < 1 slash 2 + Delta$.

For $Delta >= 1 slash 2$ the hypothesis is equivalent to RH, with no input beyond Mathlib (the equivalence is `[PROVED]`; the right-hand side is `SpectralGapHyp Δ` unfolded):

```lean
MNF.RH.riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1 / 2 ≤ Δ) :
  RiemannHypothesis ↔ MNF.RH.SpectralGapProperty MNF.RH.ShiftedZeroSpectrum Δ
```

and for $Delta > 3 slash 8$ it is equivalent to RH given OpenAI's theorem (the equivalence is `[PROVED | 7/8]`):

```lean
MNF.RH.riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3 / 8 < Δ) : RiemannHypothesis ↔ MNF.RH.SpectralGapHyp Δ
```

The reason is that $abs(beta - 1 slash 2) < 1 slash 2$ at every nontrivial zero, and $abs(beta - 1 slash 2) <= 3 slash 8$ given OpenAI's theorem.
The argument does not reach $Delta = 3 slash 8$: by `spectralGapHyp_three_eighths_iff` (`[PROVED | 7/8]`), $G(3 slash 8)$ holds if and only if every nontrivial zero has $beta in {1 slash 2, 1 slash 8, 7 slash 8}$, and OpenAI's theorem leaves the line $op("Re") s = 7 slash 8$ open.
This does not show that $G(3 slash 8)$ fails to imply RH; it shows only where the argument from the bound $abs(beta - 1 slash 2) <= 3 slash 8$ stops.
The threshold $3 slash 8$ is relative to that theorem: the register lists smaller boundaries, announced as parameter refinements of OpenAI's argument (about $0.874957$ by Liu~#cite(<liu-2026>)), as read and not run here, and none is used in this work.
RH implies $G(Delta)$ for every $Delta$ (`gap_of_rh`).
For smaller $Delta > 0$, $G(Delta)$ is a zero-free strip next to the critical line, in the register's words "not known for any Δ > 0".

The conditional density theorem (`[CONDITIONAL]`):

```lean
MNF.RH.on_line_density_one_of_gap (hBL : MNF.RH.BohrLandau) (hN : MNF.RH.NcountSuperlinear) {Δ : ℝ} (hΔ : 0 < Δ)
  (hgap : MNF.RH.SpectralGapHyp Δ) (ε : ℝ) : ε > 0 → ∃ T₀, ∀ T ≥ T₀, (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0 0 T)
```

`BohrLandau` says that for every $delta > 0$ some $C$ gives $N_"off" (delta, T) <= C T$ for all $T >= 2$~@bohr-landau-1914; `NcountSuperlinear` says that $c T <= N(T)$ for every $c > 0$ and all large $T$.
In run 5 both propositions are `[LITERATURE]` hypotheses, never asserted; on the zeta23 tree they become theorems in runs 7 and 9 (see~@sec-the-density-layer-counting-vocabulary-and-the-bohrlandau-the).
The conclusion, $(1 - epsilon) N(T) <= N_0(T)$ for all large $T$, follows from RH and is not known to imply it.
The register calls the implication "folklore, not new mathematics", and the hypothesis $G(Delta)$ is open.

Most other statements are multiplicity lemmas (for instance $m(rho) = 1$ if and only if $zeta'(rho) != 0$, and $m(1 - rho) = m(rho)$), bookkeeping for counting functions, and equivalences that rewrite hypotheses of the corpus.
Each equivalence relocates RH, simplicity or the gap hypothesis; each side is as open as the other.
The register's summary: "Not RH, not simplicity, and no new technique toward either"; and, in one line, "the nullification framework re-expresses RH; it does not reduce it."

== What is open and what was withdrawn <sec-what-is-open-and-what-was-withdrawn>

The register lists as open: $G(Delta)$, for each $Delta > 0$; the simplicity of the zeros (`AllZerosSimple`); and two realization hypotheses of Hilbert–Pólya type, namely a symmetric operator, or a Schrödinger operator with a confining potential, having every $(rho - 1 slash 2) slash i$ as an eigenvalue.
RH follows at once from either (`rh_of_symmetric_operator`, `rh_of_realization`, both `[CONDITIONAL]`); of the first the register says that the route "has no content short of constructing the operator".
Speiser's theorem~#cite(<speiser-1934>), that RH holds if and only if $zeta'$ has no zeros with $0 < op("Re") s < 1 slash 2$, is, per the register, not in Mathlib and is kept as a named `[LITERATURE]` hypothesis.

Five items of the corpus were withdrawn: (1) an axiom on double zeros, cited to Levinson and Montgomery~#cite(<levinson-montgomery-1974>), which the citation does not support (with Speiser's theorem it would give that RH implies the simplicity of all zeros, which is not a known theorem) and which survives only as an explicit hypothesis of `allZerosSimple_of_speiser_and_double_zero_hyp`; (2) an axiom #box[$zeta'(1 - s) = -F(s) zeta'(s)$] throughout the strip, where $zeta(1 - s) = F(s) zeta(s)$, which is false as stated (the product rule leaves a term $zeta(s) F'(s)$) and is replaced by the proved `deriv_reflect` at zeros; (3) statements over placeholder functions fixed by `Classical.choice`, which "say nothing about ζ"; (4) two hypotheses, withdrawn as such because they are now theorems; (5) the description of $G(1 slash 2)$ as "a physical input", since it is RH verbatim.

== Runs 3 to 6: the library judged <sec-runs-3-to-6-the-library-judged>

#figure(
  rtable(columns: (auto, 1fr, auto, auto, 41.5pt, auto, 51pt, auto), align: (center, left, center, left, left, left, right, left), size: 7.6pt,
    header: ([Run], [Label], [Theorems], [Definitions], [Kernels], [Start (UTC)], [Wall clock (min:s)], [Result]),
    [3], [`mnf-library`], [40], [17, as holes], [Lean], [2026-10-28T00:20:02Z], [12:43.44], [`MNF_LIBRARY=ACCEPTED`],
    [4], [`mnf-library-v2`], [43], [17, none a hole], [Lean], [2026-10-28T03:25:44Z], [13:28.87], [`MNF_LIBRARY=ACCEPTED`],
    [5], [`mnf-library-v3`], [87], [41, none a hole], [Lean], [2026-10-29T05:56:47Z], [14:00.38], [`MNF_LIBRARY=ACCEPTED`],
    [6], [`zeta23-mnf`], [62], [23, none a hole], [Lean and NanoDa], [2026-10-29T02:06:38Z], [5:55.36], [`MNF_ZETA23=ACCEPTED`],
  ),
)

In each run Comparator~@comparator judged the library against a challenge with the same statements and every proof replaced by `sorry`; all exit codes are 0, and every axiom report lists only the three standard axioms.

Run 3 listed its 17 definitions as holes, so their bodies were not compared (see~@sec-comparator-and-what-an-acceptance-means).
Run 4 added three theorems, among them the strip equivalence above, and listed no holes: it is the first run in which the library's definition bodies were compared.
The definition counts are the `def` declarations of the challenge sources, as the report generator counts them.
From run 4 on Comparator compares by name, type and body every definition that a claimed statement refers to; a counted definition that no claimed statement refers to (`MNF.RH.Counter` is one) was not compared, so each count is an upper bound for the bodies compared.
Run 5 added five files (`Counting`, `Reduction`, `Schrodinger`, `GapDensity` and the Sturm–Liouville file below); eight of its 87 theorems are the `[PROVED | 7/8]` statements of `Unconditional.lean`, the only file that imports OpenAI's library.

Run 6 judged, on the zeta23 tree, the 36 statements of `Core`, `Gap` and `Hypotheses`, the 13 of `Counting`, and 13 in `Zeta23Restated.lean`, tagged `[RESTATEMENT | zeta23]`: eleven restate zeta23’s statements about $zeta$ over the library's counting functions and two rewrite them.
In the report's words they "hold by definitional unfolding and are exactly as reliable as the zeta23 receipt", and "a proportion of zeros, however large, is not a statement about every zero".
The `[PROVED | 7/8]` statements are absent, since that tree has another Lean and Mathlib pin and no OpenAI library.

The result word of these runs is ACCEPTED, not PASS; @sec-cold-and-warm-runs gives the reason and the recorded status of each run.
The numbering is the record's: run 6 ended before run 5 began.

Outside the eleven runs, the record mentions two further acceptances for which it holds no receipt.
The register says that the injection and ejection algebra of the author's "MNF2" package (in the layer, the file `MNF/Extension/InjectionEjection.lean`) was "also ACCEPTED at the OpenAI pin on 2026-11-03", and the README that the Sturm–Liouville file, as a standalone project with its own Comparator challenge, was "accepted again on 2026-11-03, Lean kernel and NanoDa".
They are not results of this paper.
Run 1’s bundle also holds `BRIDGE.md`, the report of an ordinary sandboxed compile of two earlier files of the author on OpenAI's tree (in its words, "it is not a second Comparator run"); according to the register, `Unconditional.lean`, judged in runs 3 to 5, has the same content as the second of them, restated over the library's definitions.

== The Sturm–Liouville file and its co-authorship <sec-the-sturmliouville-file-and-its-co-authorship>

Run 5 also judged `SturmLiouville/SimpleEigenvalues.lean` (581 lines; four definitions, four statements), which concerns one-dimensional Schrödinger operators, not $zeta$.
Its main statement (`[PROVED]`) is

```lean
sturm_liouville_simple_eigenvalues (V : ℝ → ℝ) (hV : IsConfiningPotential V) (eigval : ℝ) : IsSimpleEigenvalue V eigval
```

that is: if $V$ is continuous on $RR$ with $V(x) -> +infinity$ as $abs(x) -> infinity$, then for every real $lambda$ any two eigenfunctions of $-u'' + V u = lambda u$ in $L^2(RR)$ are proportional.
The result is classical (the limit-point case of Weyl's theory).
The library uses it only in `Schrodinger.lean`: in a hypothetical Schrödinger realization every level is a simple eigenvalue, but by `multiplicityDictionary_iff` the link from simple eigenvalues to $m(rho) = 1$ is then equivalent to `AllZerosSimple`, so the theorem gives no shortcut to simplicity.

The record's `NOTICE` states that this file was "co-authored by Aristotle (Harmonic)" on 2026-03-03, consolidated by the author, and ported to the Mathlib pin of OpenAI's tree with "proof-internal changes only".
This paper takes "Aristotle (Harmonic)" to be the system of~@aristotle; the record does not say so.
The authorship of the rest of the library is given in~@sec-authorship-and-use-of-ai-tools.
