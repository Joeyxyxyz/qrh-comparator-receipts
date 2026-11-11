# Assembly notes for WORK/paper.md

Assembled 2026-11-10 (local date) from WORK/sections/01 to 07 with WORK/review/_assemble/assemble.py.
Every edit to a draft is an exact-string or anchored-span replacement that stops the script if its
anchor is missing or ambiguous, so text that was not edited is byte-identical to the drafts. Nothing
outside WORK was modified. The two figures were copied, unchanged (sha256 equal), from
REPO/notes/density-field-2026-11-03/numeric/ to WORK/figures/.

## Title

Chosen (24 words):
"Receipted Comparator Checks of Two Lean Proofs on Zeros of the Riemann Zeta Function, with
Formalizations of the Bohr–Landau Theorem and a Zero-Density Estimate"

Alternatives:
1. "Eleven Receipted Comparator Runs on the Zeros of the Riemann Zeta Function: Two Replications and
   Lean Formalizations of Classical Zero-Counting Theorems" (21 words)
2. "Sandboxed, Hash-Receipted Re-Checks of Two Machine-Checked Theorems on the Zeta Zeros, with a Lean
   Formalization of the Bohr–Landau Theorem" (19 words)

## Structure of paper.md

Title block (four consecutive lines: title, Author, Date, Repository); Abstract (218 words);
Keywords; Introduction (with a new last subsection "Notation"); The checking protocol; The first six
runs and the MNF.RH library; The density layer: counting vocabulary and the Bohr–Landau theorem; A
zero-density estimate, the displacement bound and the pair measure; A numerical illustration,
limitations and errata; Reproducing and verifying the record; Authorship and use of AI tools;
Acknowledgments; Appendix A; Appendix B; References (37 entries, sorted by key).

Word counts (whitespace tokens, `wc -w` convention): 14261 for the whole file; 13425 without the
References; 11601 for the main text before the appendices; 10663 for the main text without code blocks
and table rows.

## What was added

- Title, abstract, keywords.
- Introduction: one sentence defining "the record"; a gloss of "register" as `DEPOSIT_MAP.md`; a
  rewritten "Plan of the paper" that names every later section and both appendices; the subsection
  "Notation" (the table of counting functions with their Lean names, moved from section 04 and
  extended by N_≠(T) = `NOffLine 0 T`; the symbols G(Δ), D(T), P(T) with their Lean names; how to
  read `↑` and a leading `@`; times are UTC; run numbers are not chronological).
- References, built from WORK/facts/literature.md for the 37 keys actually cited.

Facts used in the new text and where they come from: `NRight` exists in `MNF.RH` and with the same
body in `Zeta23.BL` (density.md section 3); N = N_0 + N_≠ is `MNF.RH.Ncount_eq_N0_add_NOffLine`
(run 11 `audit.out`, line 2491); `SpectralGapHyp Δ := SpectralGapProperty ShiftedZeroSpectrum Δ` and
`SpectralGapProperty S Δ := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ` (add-on v3, `Hypotheses.lean` line 47 and
`Gap.lean` line 34); P(T) is `MNF.RH.offDiagonalCoincidentMass T` (density.md 4.19); the reading of
`↑` and of the leading `@` (density.md section 0).

## Notation and wording unified

- En dashes in compound names in prose (Bohr–Landau, Montgomery–Vaughan, Riemann–von Mangoldt,
  Euler–Maclaurin, Hardy–Littlewood); "disk" for "disc". Code spans, Lean blocks and file names
  (`JensenDisc.lean`) are untouched. The heading of section 04 now has the en dash.
- Absolute values in prose mathematics are written `\lvert … \rvert` throughout.
- "zeta23" is set in plain type as the project's name; paths and Lean names stay in code type.
- G(Δ) is the one symbol for the gap hypothesis (sections 03, 04, 05, Appendix B); N_≠(T) for the
  zeros off the line (04, 05, 06, Appendix B); D(T) and P(T) as in the drafts.
- "RH" is defined once (Introduction, Contributions item 3); the later "(RH)" re-definitions in
  sections 03, 05 and 06 were removed.
- The author's vocabulary is defined once each: MNF and the spectral gap hypothesis in the
  Introduction; nullification in "The MNF.RH library in standard terms"; reservoir in "Counting
  functions and two notions of density"; cube and degenerate in section 05. The Introduction no longer
  defines "cube" and "degenerate" (it says "pair-measure module" and states the equivalence in plain
  terms). Captions and Appendix B keep one-clause reminders.
- Cross-references are by section or subsection title in italics; the checker confirms that all 33
  point to an existing heading (21 distinct headings).
- Figure 1 caption: "($D$ in the figure)" became "$x$ (labeled D in the figure, which is not the
  $D(T)$ of the text)", because D(T) is the displacement sum.
- Lewko is named in full at the first mention (Introduction); the Palomar registry is cited at its
  first mention (section 04).

## Duplication removed (the content remains in the place named)

- Section 02, opening: the sentence on who produced the scripts (now a pointer to "Authorship and use
  of AI tools").
- Section 02, "Receipts and the verifier": the detailed list of what `verify_deposit.sh` checks and
  the `VERIFY=OK` sentence (kept in "Verifying the record offline").
- Section 02, last lesson: the details of the run 9 erratum (kept in "Errata").
- Section 03, runs 1 and 2: the repeated "not a first verification" argument and receipt quotation
  (kept in section 02); the meaning of PASS is kept in one sentence.
- Section 03: the second definition of the gap hypothesis; the gloss of `N0 0 T`; the hole-comparison
  rule; the cold/warm status of runs 3 to 6 (kept in "Cold and warm runs"); the NOTICE attributions
  for the rest of the library (merged into "Authorship and use of AI tools", which now lists the file
  names).
- Section 04: the notation paragraph and table (moved to "Notation"); the second definition of the
  gap hypothesis in "Corollaries".
- Section 05: the sentence on where `@` statements are printed; the second definitions of "reservoir"
  and of the gap hypothesis; the Lean name of N_≠.
- Section 06: the trust-base list in "Limitations" (pointer to "The trust base"); the counterexample
  to the planned bound in "Errata" (kept in "The pair measure"); the second gloss of the register.
- Appendix B: the definitions of G, D, N_≠ and P in its header (pointer to "Notation").

No technical statement, Lean block, table row, number or non-claim was dropped. One edit of the first
pass was reverted: in section 04 the inequality N_off(δ,T) ≤ N(T) − N_0(T) is left as drafted, since
the two lemmas cited for it give exactly that form.

## Checks run on the final file (WORK/review/_assemble/check.py, check_lean.py)

- All 18 code blocks are byte-identical to code blocks of the drafts; none was dropped. Each of the
  17 Lean blocks was found again verbatim, whole or statement by statement, in run 1's RECEIPT.md,
  run 5's MNF_LIBRARY.md, run 11's MNF_DENSITY.md or audit.out, or the add-on v6 sources.
- 37 keys cited, 37 reference entries, all defined in literature.md, all with status VERIFIED.
- Appendix A (11 rows) and the table of runs 3 to 6 agree with the master table of WORK/facts/runs.md
  on label, theorem and definition counts, kernels, UTC start and end, wall clock, verdict word and
  both tarball hash prefixes. Every time stamp, duration and hexadecimal string in the paper occurs in
  runs.md, except the repository commit `f03aaa9`, which is in method.md.
- No "we", no HTML, no footnotes, none of the excluded hype words, no hyphenated proper-name
  compounds, no British spellings found by the patterns used; table rows have consistent cell counts;
  `$` and backticks are balanced on every line.
- Not checked by machine: that the Markdown renders in the target converter (none was available);
  the per-row readings of Appendix B (checked by the section author).

## Citations: UNVERIFIED and PARTLY VERIFIED entries

- No entry marked UNVERIFIED is cited. `openai-announcement` (the only UNVERIFIED entry) is not cited.
- No entry marked PARTLY VERIFIED is cited (`selberg-1942`, `vallee-poussin-1896`, `qr-tracker`).
- Caveats that literature.md attaches to cited VERIFIED entries, and how the reference list handles
  them: `lean4`, the LNCS volume number is omitted (the sheet says it is from memory);
  `carlson-1920` is printed as "F. Carlson … (1920/21)" (zbMATH has 1921; the text says 1920, as the
  framing rule does); `speiser-1934` is printed with 1934 (Crossref dates the issue 1935);
  `hardy-littlewood-1918` with 1918 (Crossref 1916, zbMATH 1917); `landrun` "version 0.1.18" in the
  text is the record's label, not checked upstream; `hubbard-goldbach-lean` was read on its default
  branch, not at a pinned commit; `openai-qrh`, the PDF was not opened. The attributions of results
  to `bohr-landau-1914`, `littlewood-1924`, `selberg-1946` (the O(T) consequence),
  `hardy-littlewood-1918`, `von-mangoldt-1905`, `speiser-1934` and the section numbers of
  `titchmarsh` are the standard ones and were not read in the originals.

## Left for the author to settle before the deposit

1. Placeholder: "The Zenodo record of this paper has the DOI 10.5281/zenodo.XXXXXXX" (Availability).
2. "The text of this paper is under CC BY 4.0" comes from the section brief, not from a file of the
   record.
3. "Run at commit `f03aaa9` … `VERIFY=OK`" and "27 listed files" go stale if the repository changes
   before the deposit (README, `zenodo-metadata.json`, adding the paper); rerun `verify_deposit.sh`.
4. Stale documents in the repository, not touched: README header ("seventeen artifacts, eight
   receipts", dates), its `sources/` list and "Who did what"; `zenodo-metadata.json` (runs 1 to 6
   only); DEPOSIT_MAP section 10 calls runs 7 to 11 "cold" where the receipts record "warm" (the
   paper follows the receipts and says so in one parenthesis).
5. Run 2's receipt records add-on manifest hash `a20b1b1d…`; the deposited add-on has `0c37cc13…`.
   The paper says "another, presumably earlier, version launched run 2"; no document explains it.
6. Authorship: NOTICE does not say which tool drafted the four supplied files of the layer or the six
   corpus files, and the paper states that beside framing rule 7; the identification of "Aristotle
   (Harmonic)" with arXiv:2510.01346 is flagged in the text as the paper's reading; whether the
   Aristotle prompt for the run 9 step was ever sent is not stated in the record and not mentioned in
   the paper.
7. OpenAI: literature.md found no sentence in OpenAI's repository reporting the outcome of its own
   Comparator run, so the paper says only that the repository ships the configuration and an
   instruction (the record's README says more).
8. The two hedged sentences "the author is not aware of a prior Lean …" (two-sided Bohr–Landau
   statement; a bound for the displacement sum) rest on incomplete searches, as the text says.
9. Figures: the SVGs carry hover-only text, ASCII labels and an undefined "0.0e zone", and panel A of
   Figure 2 is titled "its support under RH"; captions are in the image alt text; no SVG-to-PDF
   converter was available to test the rendering.
10. The "What was proved" block of the run 11 report holds 255 of 534 statements; the paper says so
    under "Errata". A note in the repository README may be wanted.
11. Section lengths: several drafts were above their targets; only duplicated material was removed.
12. Title block: the three lines after the title are consecutive lines, as specified; a Markdown
    renderer will join them into one paragraph unless the converter treats them as metadata.
13. Date line 2026-11-11 is the UTC date of run 11; the assembly was done on 2026-11-10 local time.
