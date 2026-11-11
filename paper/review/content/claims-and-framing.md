# Review record: claims and framing (adversarial pass on WORK/paper.md)

Reviewed 2026-11-10 (local). Lens: overclaiming, novelty, "first" claims, equivalences read as
results, numerics read as evidence, external theorems read as first verifications, vague or
inflated words, the author's vocabulary, the authorship and AI-use statement. Compared with
REPO/DEPOSIT_MAP.md sections 4 to 6 and 10, REPO/NOTICE, REPO/README.md, the fact sheets in
WORK/facts/ and the two figures in WORK/figures/. The paper was not edited. Nothing outside WORK
was modified.

Abbreviations: PAPER = WORK/paper.md; REPO = /home/joeyxyxyz/repos/qrh-comparator-receipts;
FACTS = WORK/facts.

## Verdict

The text keeps the binding non-claims: the sentence "Nothing here proves, or is evidence for, the
Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line"
is in the abstract, the Introduction, the head of each results section, the Limitations and
Appendix B, unsoftened. The two external theorems are attributed and the runs are called
repetitions, not first verifications; PASS and ACCEPTED are kept apart; the classical status of
Bohr-Landau, Carlson and the real-zero fact is stated with the earlier Lean work (Lewko, AxiomMath,
goldbach-lean); the two "not aware of a prior Lean formalization" sentences are the two that
FACTS/literature.md section 5.5 allows, each with its caveat; none of the excluded hype words
occurs. No sentence was found that claims progress on RH, on the gap hypothesis or on simplicity.

Three problems are major (false or misleading as printed), and all three are local:
(1) the authorship paragraph understates what NOTICE attributes to Claude Code in MNF.RH, including
the headline theorem `spectralGapHyp_iff_zeroFree_strip`;
(2) Figure 1 carries, inside the image, the phrase "reservoir empty up to D = 0.243" and the title
"read through the MNF threshold cascade", which in the paper's own vocabulary reads as a numerical
confirmation of the gap hypothesis;
(3) Contribution 1 says the verifier "re-derives every hash the record cites", which the paper
itself contradicts.
Eighteen minor items follow. Outside this lens, noted only: the DOI placeholder
"10.5281/zenodo.XXXXXXX" in *Availability* must be filled before print.

## Major

### M1. Authorship: Claude Code's share of MNF.RH is understated

- Location: *Authorship and use of AI tools*, "(among them `Counting`, `Zeta23Restated`,
  `GapDensity` and the port of the Sturm–Liouville file) were written with Claude Code" and, two
  sentences on, "For the six corpus files and for these four supporting files, the record does not
  say which tool, if any, drafted them."
- Problem: NOTICE lists two more items as written with Claude Code, and both sit inside the "six
  corpus files": the three gap theorems added in run 4, and the proposition forms of
  `GapMechanism` and `SchrodingerRealization`. One of the three is
  `spectralGapHyp_iff_zeroFree_strip`, which the paper presents as the library's central
  identification ("The gap hypothesis is a zero-free strip"), and another is
  `spectralGapHyp_three_eighths_iff`. For these the record does say which tool wrote them, so the
  second quoted sentence is false as it stands, and "among them" hides the most prominent case.
- Evidence: REPO/NOTICE: "the Comparator add-on scripts and the additions of 2026-10-28/29
  (Counting.lean, Zeta23Restated.lean, GapDensity.lean, the three spectral-gap theorems of v2, the
  Prop forms of GapMechanism and SchrodingerRealization, the port of the Sturm–Liouville file) were
  written with Claude Code (Anthropic) under Joey's direction". FACTS/mnf.md section 1: "v1 to v2:
  three theorems added, `spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of`,
  `spectralGapHyp_three_eighths_iff`". REPO/sources/qrh-mnf-addon-v3/MNF/RH/Hypotheses.lean line 85
  ("theorem spectralGapHyp_iff_zeroFree_strip") and line 114; Unconditional.lean line 53.
- Replacement (for the two sentences): "It attributes six files of `MNF.RH` (`Core`, `Gap`,
  `Hypotheses`, `Unconditional`, `Reduction` and `Schrodinger`) to the author's earlier corpus,
  consolidated on 2026-10-27/28, and says that the additions of 2026-10-28/29 were written with
  Claude Code: the files `Counting`, `Zeta23Restated` and `GapDensity`; the three gap theorems
  added in run 4 (`spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of` and
  `spectralGapHyp_three_eighths_iff`, which sit in `Hypotheses` and `Unconditional`); the
  proposition forms of `GapMechanism` and `SchrodingerRealization`; and the port of the
  Sturm–Liouville file. [...] For the rest of the six corpus files, the consolidation of
  2026-10-27/28 with its re-proved lemmas included, and for these four supporting files, the record
  does not say which tool, if any, drafted them."

### M2. Figure 1: in-image labels read as numerical evidence for the gap hypothesis

- Location: *A numerical illustration*, Figure 1 and its caption, "\"Reservoir\", \"hidden mass\"
  and \"trace\" in the figure are the author's labels for these spacing statistics".
- Problem: the image (copied unchanged from the record) is titled "First 400 nontrivial zeros of
  zeta, read through the MNF threshold cascade", panel A is headed "Hidden (reservoir) mass below
  the threshold", and its annotation reads "reservoir empty up to D = 0.243". The paper defines
  "reservoir" as the author's word for zeros off the line, and in the record "the Δ-reservoir is
  empty" is the gap hypothesis. A reader who knows the text's vocabulary therefore reads the
  annotation as "no zeros off the line up to a threshold, observed". One caption sentence does not
  cancel a headline inside the image, "threshold cascade" is not defined anywhere in the paper, and
  the same image says the ordinates were "verified by Euler-Maclaurin" while the text calls them
  "uncertified". (The image also says "Hover the dots and bars for the counts", which does nothing
  in a PDF.)
- Evidence: WORK/figures/cascade.svg, text nodes: "First 400 nontrivial zeros of zeta, read through
  the MNF threshold cascade"; "A. Hidden (reservoir) mass below the threshold, h_D / sum s";
  "reservoir empty up to D = 0.243:"; "Ordinates by Riemann-Siegel (C0 term), verified by
  Euler-Maclaurin." PAPER, *Counting functions and two notions of density*: "The word \"reservoir\"
  in its name is the author's word for zeros off the line". REPO/DEPOSIT_MAP.md section 10: "under
  a gap at Δ the Δ-reservoir is empty". FACTS/numerics.md F4.3: "avoid the word \"reservoir\" for
  spacings, or define it once and say it is unrelated to the real-part quantity"; R3: "The word
  \"certifies\" in C3 is too strong".
- Replacement: preferred, make an edited copy of the figure in WORK/figures (the record's file
  stays as it is) with neutral labels: title "Normalized spacings of the first 400 zeros of zeta";
  panel A "Fraction of the total spacing length in spacings below x"; annotation "no spacing below
  0.243"; "re-located by Euler-Maclaurin"; drop "Trace delta*" and the "Hover" line. If the image
  cannot be changed, replace the caption's last sentence by: "The phrases in the image are the
  author's working labels and are not the terms of the text: \"MNF threshold cascade\" is the table
  of these spacing statistics over a list of thresholds; \"hidden (reservoir) mass\" is the total
  length of the spacings below the threshold; \"reservoir empty up to D = 0.243\" says only that no
  normalized spacing is below 0.243; \"trace\" is the largest spacing; \"verified\" means
  re-located by a second formula, without error bounds. The threshold D acts on spacings of
  ordinates. It is unrelated to the \"reservoir\" of the text (zeros off the line), to the
  threshold Δ of the gap hypothesis (a distance of real parts from 1/2), and to any zero-free
  strip."

### M3. Contribution 1: "re-derives every hash the record cites" is false

- Location: *Contributions*, item 1, "a script, `verify_deposit.sh`, that re-derives every hash the
  record cites and re-reads every verdict from the deposited bundles".
- Problem: the phrase repeats the header comment of the script, but the paper itself reports hashes
  the script does not and cannot re-derive: run 2's recorded add-on manifest hash matches no
  deposited file, the sources hashed in run 6 are not compared, `README.md`, `sources/` and
  `notes/` are not in the checksum file, and the toolchain, Mathlib and checker pins are checked
  only for two statement files and only with network access.
- Evidence: REPO/verify_deposit.sh line 2: "# Re-derive every hash this record cites and re-read
  every verdict from the receipt bundles." PAPER, *Receipts and the verifier*: "One gap remains:
  run 2's receipt records an add-on manifest hash (`a20b1b1d…`) other than that of the deposited
  add-on"; *Verifying the record offline*: "`README.md`, `sources/` and `notes/` are not listed"
  and "(not for run 6)". FACTS/runs.md D9 and D10 ("No receipt bundle contains the sha256 of any
  kit or add-on tarball").
- Replacement: "and a script, `verify_deposit.sh`, that re-checks the sha256 of every deposited
  tarball, re-reads every verdict from the bundles and compares the judged Lean sources of runs 3
  to 5 and 7 to 11 with the add-on tarballs (*Verifying the record offline* says exactly what it
  covers and what it does not)."

## Minor

### m1. "The second threshold is exact"

- Location: *The MNF.RH library in standard terms*, "The second threshold is exact: by
  `spectralGapHyp_three_eighths_iff`".
- Problem: "exact" says that the equivalence with RH fails at Δ = 3/8. That is not proved and is
  false if RH holds. What is proved is that the argument from the bound |β − 1/2| ≤ 3/8 stops
  there.
- Evidence: FACTS/mnf.md section 11, item 2: "the paper should say that the squeeze argument does
  not close below the bound, not that the gap at small Δ is known not to imply RH"; section 4.1:
  "it is not proved, and could not be without settling RH, that G(Δ) fails to imply RH for ζ".
- Replacement: "The proof does not reach Δ = 3/8: by `spectralGapHyp_three_eighths_iff`
  (`[PROVED | 7/8]`), G(3/8) holds if and only if every nontrivial zero has β ∈ {1/2, 1/8, 7/8},
  and OpenAI's theorem leaves the line Re s = 7/8 open. This does not show that G(3/8) fails to
  imply RH; it shows only where the argument from the bound |β − 1/2| ≤ 3/8 stops."

### m2. Abstract: three qualifiers of the framing rules are missing

- Location: *Abstract*, "The analytic theorems are classical, and stronger zero-density estimates
  exist in Lean." and "The layer's Lean files, the scripts and this text were produced with Claude
  Code under the author's direction."
- Problem: the abstract is what a Zenodo reader sees. It lists the displacement bound without
  "far weaker than Littlewood and Selberg" (rule 3), the two equivalences without "relocate, prove
  neither" (rule 4), the real-zero fact and Bohr-Landau without the earlier Lean work that covers
  them, and the AI-use sentence without Anthropic, without the author's responsibility (rule 7:
  "wherever authorship is discussed") and without the Claude Code parts of MNF.RH.
- Evidence: PAPER, *What is not claimed* (third to sixth bullets) has each of these; FACTS/
  literature.md section 5.2: "the content of Bohr–Landau was available in Lean, as a corollary not
  stated as such, before runs 8 and 9"; section 5.3 heading: "YES, prior Lean proofs exist";
  REPO/NOTICE (quoted in M1).
- Replacement (from "Nine further accepted runs" to the end): "Nine further accepted runs judge
  Lean files added to the verified trees: the author's library MNF.RH, and a layer formalizing the
  Bohr–Landau theorem, a zero-density estimate with a power saving weaker than Carlson's, a bound
  for the zeros' total displacement from the critical line that is far weaker than Littlewood's and
  Selberg's, two equivalences that restate, and do not prove, the Riemann hypothesis with
  simplicity and the author's gap hypothesis, and the absence of real zeros of zeta in (0,1). The
  analytic results are classical or weaker than classical ones; zero-density estimates with
  stronger exponents, which imply the Bohr–Landau bound, and proofs of the absence of real zeros
  existed in Lean before. Nothing here proves, or is evidence for, the Riemann hypothesis, the
  simplicity of the zeros, or a zero-free strip next to the critical line. The layer's Lean files,
  parts of MNF.RH, the scripts and this text were produced with Claude Code, Anthropic's coding
  agent, under the direction of the author, who conceived the MNF framework, operated every run and
  is responsible for the claims."

### m3. A register tag placed where it reads as "RH [PROVED]"

- Location: *The MNF.RH library in standard terms*, "For $\Delta\ge 1/2$ it is RH, with no input
  beyond Mathlib (`[PROVED]`" and, above it, "The gap hypothesis is a zero-free strip
  (`[PROVED]`):".
- Problem: the tag belongs to the equivalence. Next to "it is RH" and "a zero-free strip" it can be
  read, or quoted, as a tag on RH or on the strip.
- Evidence: REPO/DEPOSIT_MAP.md section 4: "`SpectralGapHyp Δ` for any Δ > 0 [...] not known for
  any Δ > 0"; section 3 note on `rh_of_gap`: "the hypothesis is RH itself".
- Replacement: "The gap hypothesis is equivalent to a zero-free strip (the equivalence is tagged
  `[PROVED]`; neither side is proved):" and "For Δ ≥ 1/2 the hypothesis is equivalent to RH, with
  no input beyond Mathlib (the equivalence is `[PROVED]`; the right-hand side is `SpectralGapHyp Δ`
  unfolded):" and "for Δ > 3/8 it is equivalent to RH given OpenAI's theorem (the equivalence is
  `[PROVED | 7/8]`):".

### m4. "More than two thirds" is the title of the source paper, not a Lean statement judged in run 2

- Location: *Runs 1 and 2: the two replications*, "eleven statements about $\zeta$ and six about
  Dirichlet $L$-functions, each a proportion in $\varepsilon$-form"; also *Abstract* and
  *Acknowledgments*.
- Problem: the PASS is described next to "more than two thirds", while the 17 judged statements
  have the constants 2/3 − ε and 5/6 − ε, and the strict excess over 2/3 is a decimal in docstrings.
- Evidence: REPO/DEPOSIT_MAP.md section 8: "The decimal constants quoted for it (0.67250, 0.83625)
  are docstrings, not statements." FACTS/mnf.md section 10: "the strict excess over 2/3 comes from
  Theorem D's 2 − 1/c₁*, whose decimal value (0.67250…) is in docstrings only".
- Replacement (add after the example in that paragraph): "The words \"more than two thirds\" are
  the title of [@alpoge-furman]. In the statements judged here the constants are $2/3-\varepsilon$
  and $5/6-\varepsilon$, and in the Montgomery–Taylor statements a symbolic constant whose decimal
  value (0.67250) appears only in docstrings, which Comparator does not compare."

### m5. A theorem said to be "not known to imply anything about" RH

- Location: *The displacement of the zeros from the line*, "A vanishing mean displacement follows
  from RH, is not known to imply anything about it".
- Problem: D(T)/N(T) → 0 is a theorem here (and classically). A proved statement cannot be "not
  known to imply" RH in any useful sense; the sentence suggests the result sits between nothing and
  RH.
- Evidence: PAPER, same subsection: `MNF.RH.meanDisplacement_tendsto_zero` (receipted, run 10);
  REPO/DEPOSIT_MAP.md section 10: "compatible with infinitely many zeros off the line and silent on
  the gap".
- Replacement: "That the mean displacement tends to zero is a theorem, and already a consequence of
  Littlewood's bound; under RH it is trivial, since then D(T) = 0. It restricts no individual zero,
  is consistent with infinitely many zeros off the line, and is silent on the gap hypothesis."

### m6. "would turn the illustration into a theorem for that range"

- Location: *What would strengthen the work*, "would turn the illustration into a theorem for that
  range".
- Problem: vague, and it ties the spacing numerics to "simple and on the line". A certified zero
  list would make the finite counts rigorous and nothing else.
- Evidence: FACTS/numerics.md section 12: "May not say: [...] that any of this bears on real parts,
  RH, the simplicity of the zeros in general, or a zero-free strip"; C4: "not on a Turing-style
  proof".
- Replacement: "A certified computation of the first 400 ordinates (interval arithmetic with a
  Turing-type completeness check, or a Lean-checked one), which the record lacks, would make the
  finite counts of the illustration rigorous and would say nothing beyond that height. That the
  zeros up to height $3\cdot 10^{12}$ are on the line is known from rigorous computation
  [@platt-trudgian-2021]."

### m7. "Milestone"

- Location: heading "The milestone for distances above one sixth".
- Problem: an inflated word for a partial result that the next run superseded and that the source
  calls a limitation.
- Evidence: PAPER, same subsection: "The source calls this \"a limitation of this route, not a
  theorem about ζ\"."
- Replacement: "The intermediate result for distances above one sixth".

### m8. "the most recent improvement is due to Guth and Maynard"

- Location: *The zero-density estimate*, "and the most recent improvement is due to Guth and
  Maynard [@guth-maynard]".
- Problem: the same paragraph cites a registry entry whose stated exponent is smaller than Guth and
  Maynard's, so the paper contradicts its own sources (39/17 = 2.294 < 30/13 = 2.308).
- Evidence: FACTS/literature.md, `lewko-density-3917`: "`global_uniform` gives one constant for all
  σ in [1/2, 1] with exponent (39/17)(1−σ)+ε"; `guth-maynard`: "N(σ, T) ≤ T^{30(1−σ)/13+o(1)}".
- Replacement: "and a recent improvement in the published literature is due to Guth and Maynard
  [@guth-maynard]".

### m9. "One gap remains"

- Location: *Receipts and the verifier*, "One gap remains: run 2's receipt records an add-on
  manifest hash".
- Problem: says there is one gap; the paper lists others (run 6 sources not compared by the
  verifier, pre-check logs not deposited, no run type in runs 3 to 5, controls with one checker).
- Evidence: PAPER, *Limitations*, *Lessons learned* ("The logs of these two pre-checks are not
  deposited") and Appendix A ("The verifier does not compare the sources hashed in run 6").
- Replacement: "A gap in provenance: run 2's receipt records [...]".

### m10. Theorem counts without saying what is counted

- Location: *The artifacts and what was added*, "Runs 7 to 11 judge a further layer on the zeta23
  tree; run 11 names 534 theorems."
- Problem: the counts (40, 43, 87, 62, 124, ..., 534) read as a measure of content. Most entries
  are auxiliary lemmas, and a large block has no analytic content.
- Evidence: REPO/DEPOSIT_MAP.md section 10: "Strip.lean (19), MNF/Extension/InjectionEjection.lean
  (56) | [PROVED] bookkeeping, operator algebra | [...] no analytic content"; FACTS/density.md
  section 12, item 8: "(75 of the 124 theorems of run 7) are operator bookkeeping in the author's
  vocabulary with no statement about ζ beyond restating the gap".
- Replacement: "Runs 7 to 11 judge a further layer on the zeta23 tree; run 11 names 534 theorems.
  The counts are of named declarations in the Comparator configuration, most of them auxiliary
  lemmas; 75 of the 124 of run 7, for instance, are algebraic bookkeeping for the author's
  operators with no analytic content."

### m11. Who made the "adversarial reviews"

- Location: *Authorship and use of AI tools*, "merged, and corrected after adversarial reviews of
  the prose".
- Problem: a reader takes "adversarial reviews" for review by people. The record says they were
  made by agents and by "model reviewers".
- Evidence: REPO/notes/density-field-2026-11-03/DENSITY_LEDGER.md: "An adversarial reviewer
  (workflow agent; `plan/REVIEW_2026-11-03.md`)"; REPO/NOTICE: "reviewed by independent model
  reviewers before each Comparator run".
- Replacement: "merged, and corrected after adversarial reviews of the prose, themselves made by
  Claude Code agents (the ledger speaks of \"an adversarial reviewer (workflow agent)\"; NOTICE of
  \"independent model reviewers\")." If the author confirms it, add: "No mathematician other than
  the author has reviewed the Lean files or this text."

### m12. The toolmaker of the re-check is the maker of one artifact

- Location: *The two artifacts under test and their trusted statement files*, "run 2's receipt
  calls that run \"an independent repetition of a check Anthropic reports having run itself\"";
  *Authorship and use of AI tools*.
- Problem: zeta23 is Anthropic's and, per its README, its Lean code was written by Claude; the
  scripts that re-ran the check and this text were produced with Claude Code, Anthropic's agent.
  The paper states both facts in different places and never together, while quoting
  "independent". A hostile reader will connect them.
- Evidence: FACTS/literature.md, `anthropic-formal-math`: "the README states that all Lean code was
  written by Claude (Anthropic)"; `alpoge-furman`: "the proof was discovered autonomously by Claude
  (Anthropic) and verified and communicated by the listed authors"; PAPER: "Claude Code
  [@claude-code], Anthropic's coding agent".
- Replacement (add to *Authorship and use of AI tools*): "One of the two artifacts re-checked,
  zeta23, is Anthropic's, and according to its README its Lean code was written by Claude; the
  scripts that repeated its check, and this text, were produced with Claude Code, a product of the
  same company. \"Independent\" in run 2's receipt means another machine, operator and launcher.
  The acceptance itself is the output of Comparator and of Lean's kernel, which are the Lean FRO's
  [@comparator; @lean4], and of NanoDa, an external checker by another author [@nanoda]." If true,
  add: "The author has no affiliation with OpenAI or Anthropic."

### m13. "the simplicity of the projected zeros"

- Location: head of *A zero-density estimate, the displacement bound and the pair measure*,
  "reading the strip through the simplicity of the projected zeros is the author's idea".
- Problem: NOTICE's phrase, unquoted and undefined. "Simplicity" here means that distinct zeros
  have distinct ordinates, which is not the "simplicity of the zeros" (multiplicity one) of every
  other sentence in the paper.
- Evidence: REPO/NOTICE: "reading the strip through the simplicity of the projected zeros is Joey
  Messina's idea"; PAPER, *Degenerate zeros and two equivalences*: "no two distinct nontrivial
  zeros with |β − 1/2| < Δ share an ordinate".
- Replacement: "for the third, the idea of restating the gap hypothesis as the statement that
  distinct zeros near the line have distinct ordinates is the author's (NOTICE: \"reading the strip
  through the simplicity of the projected zeros\")".

### m14. The vocabulary sentence promises more than the text does

- Location: *What is not claimed*, "each is defined once, in standard terms, where it is first
  used".
- Problem: "MNF" is expanded but never defined in standard terms; "nullification" is first used in
  the Introduction and defined two sections later; "reservoir" and "Cube" first occur in Lean names
  in *Notation* and *Lessons learned*.
- Evidence: PAPER, *The artifacts and what was added*: "the library of the author's \"Messina
  Nullification Framework\" (MNF)"; FACTS/density.md section 8: "MNF | [...] the author's
  framework; the name of the library namespace `MNF`" and "nullification [...] the hard threshold
  x ↦ x·1[|x| ≥ Δ] on real numbers".
- Replacement: "each is defined in standard terms in the section that uses it." And in *The
  artifacts and what was added*: "the library of the author's \"Messina Nullification Framework\"
  (MNF), a collection of Lean files built around the thresholding map $x \mapsto x\cdot
  \mathbf{1}[\lvert x\rvert \ge \Delta]$ on real numbers, which the author calls nullification".

### m15. A non-claim of the register is not carried over

- Location: *The MNF.RH library in standard terms*, "The register's summary: \"the nullification
  framework re-expresses RH; it does not reduce it.\""
- Problem: the register's sentence before that one is the stronger non-claim and is absent from
  the paper.
- Evidence: REPO/DEPOSIT_MAP.md section 6, item 3: "Not RH, not simplicity, and no new technique
  toward either."
- Replacement: "The register's summary: \"Not RH, not simplicity, and no new technique toward
  either\"; and, in one line, \"the nullification framework re-expresses RH; it does not reduce
  it.\""

### m16. The first corollary is the classical statement

- Location: *Corollaries*, "The first is unconditional: within every fixed distance of the critical
  line the zeros have density one".
- Problem: under the author's name `reservoirDensityOne_unconditional` and the word
  "unconditional", the classical consequence of Bohr and Landau reads as a result of this work.
- Evidence: FACTS/literature.md, `bohr-landau-1914`: "for fixed σ > 1/2, N(σ, T) = O(T), so all but
  a vanishing proportion of the zeros lie in any strip |Re s − 1/2| < δ".
- Replacement: "The first has no hypothesis and is the classical consequence of the Bohr–Landau
  theorem, formalized: within every fixed distance of the critical line the zeros have density
  one".

### m17. The departure from GUE is reported without its qualification

- Location: *A numerical illustration*, "against 3.62 and 2.67 for GUE and 1.71 and 0.79 for
  Poisson".
- Problem: the bands [4.07, 5.05] and [3.26, 4.23] exclude the GUE values and 0.145 is set against
  0.2263, so the paragraph reads as a measured departure from GUE. The notes say it is not a
  finding.
- Evidence: FACTS/numerics.md C7: "it is a ~2-2.5 sigma effect on 400 zeros and is in the direction
  expected for low zeros (section 6), not a different universality class"; section 12: "May not
  say: [...] that the deviation from GUE is a finding (C1, C7)".
- Replacement (add after that sentence): "The spacings are somewhat more rigid than the GUE limit;
  the notes rate this a modest effect at this sample size, in the direction known for low zeros,
  and it is not a finding."

### m18. The 5/9 bound without the conjectured value

- Location: *The pair measure*, "this gives $P(T) \le (5/9 + \varepsilon)\, N(T)^2$ for large $T$".
- Problem: stated bare, the constant reads as a result on coincident ordinates. Under RH the same
  inequality gives P(T) = 0, so the bound is bookkeeping on Theorem B and far from the expected
  truth.
- Evidence: PAPER, same subsection: "$P(T) \le N_{\neq}(T)\, N(T) + N_0(T)\, N_{\neq}(T)$";
  REPO/DEPOSIT_MAP.md section 10: "[PROVED] bookkeeping; [PROVED | this tree] for the eventual
  bound".
- Replacement (add): "Under RH, $N_{\neq}(T) = 0$ and the same inequality gives $P(T) = 0$; the
  constant $5/9$ is bookkeeping on top of Theorem B, far from that expected value and not a step
  toward it."

### m19. Figure 2: labels that contradict or outrun the text

- Location: *A numerical illustration*, Figure 2 caption, "the shaded zones contain no data; their
  labels give the status of statements".
- Problem: the image labels the far zone "reservoir |delta| >= Delta: O(T^(1-c)) zeros, proved".
  The text glosses "reservoir" as zeros closer to the line than δ, the opposite set, and says the
  two-sided count "is not a theorem of the layer"; "proved" carries no attribution to Carlson. The
  label "the 0.0e zone" is defined nowhere, and "7/8 face" does not say whose theorem it is. The
  image also asserts "All 400 zeros [...] are simple and on the line" from a computation the text
  calls uncertified.
- Evidence: WORK/figures/cube.svg, text nodes: "reservoir |delta| >= Delta: O(T^(1-c)) zeros,
  proved"; "line delta = 0 (the 0.0e zone): the s axis, carries all the mass"; "7/8 face |delta|
  >= 3/8"; "All 400 zeros (zeros.tsv, Euler-Maclaurin column) are simple and on the line". PAPER,
  *The zero-density estimate*: "the two-sided form over $N_{\mathrm{off}}$ is not a theorem of the
  layer". FACTS/numerics.md, figure handling notes: "including \"the 0.0e zone\", which neither
  `N/RESULTS.md` nor `N/CUBE_NUMERIC.md` defines"; FACTS/density.md section 8: "The word
  \"reservoir\" is used with three different meanings in the layer".
- Replacement (caption, after "status of statements"): "In the image, \"reservoir\" means the zeros
  at distance at least Δ from the line, not the sense of the text; \"O(T^(1-c)) zeros, proved\"
  refers to Carlson's classical theorem, of which run 10 formalizes a weaker, right-half form;
  \"7/8 face\" marks the region that OpenAI's theorem excludes; \"the 0.0e zone\" is the author's
  label for the critical line. The image's sentence that all 400 zeros are simple and on the line
  rests on the uncertified computation described above; that the zeros at these heights are on the
  line is known from rigorous computation [@platt-trudgian-2021]." Better, relabel an edited copy
  of the figure in WORK/figures in these terms.
