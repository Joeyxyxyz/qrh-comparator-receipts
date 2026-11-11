# Review: references and cross-references (main.pdf, 34 pages, built 2026-11-10 20:29)

Verdict: no major problem. Every citation number, every section number, both figure numbers, the outline
and the metadata are correct. Twelve minor points follow, each with a fix that was test-built in a scratch
copy (34 pages kept in every case; no source file was edited, the scratch copies were removed).

## What was checked and found correct

- Rebuilt main.typ with the prescribed command: the text of the rebuild is identical to main.pdf, so the
  PDF matches the sources.
- References: 39 entries printed, [1] to [39], one for each key of md/99-references.md, numbered in order
  of first citation. Token-by-token comparison of each printed entry with its md entry: every title, venue,
  volume, number, year, page range, arXiv identifier, registry entry number, commit hash (10), date, DOI (13)
  and URL (19) is present and unaltered. The 32 link targets (19 URLs, 13 https://doi.org/ links) equal the
  md strings character for character, also where the printed URL wraps. Pages 32 to 34 use only New Computer
  Modern (no fallback font for the Greek letters, the minus sign or the centred dot).
- Citations: paper.md has 103 citation groups; the Typst sources have the same 103 groups with the same keys
  in the same order, and the PDF prints 103 bracket groups whose numbers equal the cited keys at each place
  (checked against the words before and after each one). Groups print as "[3], [4]". All 39 keys are cited.
  key -> number: comparator 1, lean4 2, openai-math 3, openai-qrh 4, anthropic-formal-math 5, alpoge-furman 6,
  bohr-landau-1914 7, carlson-1920 8, nanoda 9, littlewood-1924 10, selberg-1946 11, lewko-density-34 12,
  lewko-density-32 13, lewko-density-3917 14, lewko-density-improved 15, axiom-zetazeros 16,
  hubbard-goldbach-lean 17, montgomery-1973 18, odlyzko-1987 19, claude-code 20, mathlib 21, lean4export 22,
  lean-4-35 23, landrun 24, liu-2026 25, speiser-1934 26, levinson-montgomery-1974 27, aristotle 28,
  von-mangoldt-1905 29, bohr-landau-1914b 30, titchmarsh 31, palomar 32, fiori-2026 33, pnt-plus 34,
  montgomery-vaughan-1974 35, ingham-1940 36, guth-maynard 37, tao-trudgian-yang 38, platt-trudgian-2021 39.
- Cross-references: paper.md has 50 italic heading titles used as references; the Typst sources have 50
  `@sec-...` with the matching labels in the same order; all 50 print the number of the named heading
  (for example The trust base -> Section 2.3, Notation -> Section 1.5, Errata -> Section 6.3, Authorship and
  use of AI tools -> Section 8), and the link targets are the pages of those headings. The 16 other italic
  phrases of paper.md are emphasis and were kept as emphasis. All 47 headings carry the label of LABELS.md.
  "Section 9.15 of [31]" and "Section 7.2 of [31]" are Titchmarsh's sections, literal in the source.
- Figures: the two figures print as Figure 1 (cascade, page 22) and Figure 2 (cube, page 23), as in paper.md.
  paper.md has no reference to a figure in running text and the Typst sources have no `@fig-...`.
- Appendix A / Appendix B: four mentions (three on page 4, in Plan of the paper and in Notation; one on page 25), literal text as in
  paper.md; they agree with the printed headings "Appendix A. The eleven runs" (page 29) and
  "Appendix B. Principal Lean theorems" (page 30). Literal text is right here: `@sec-appendix-a-the-eleven-runs`
  would print "Appendix Appendix A." with the appendix numbering function.
- Outline: 48 bookmarks = the 47 headings of paper.md plus References, correct nesting and numbers
  (1 to 8 with their subsections, then Acknowledgments, Appendix A., Appendix B., References unnumbered at top level).
- Metadata (pdfinfo): Title = the title of paper.md; Author = Joey Messina; Keywords = the ten keywords of
  paper.md in order.

## Findings (all minor)

1. typ/03-runs-mnf.typ line 85, page 11. `(see~@sec-the-density-layer-counting-vocabulary-and-the-bohrlandau-the).`
   prints as "(see Sec-" / "tion 4)": the word Section of the reference is hyphenated across a line.
   Fix: `(see~#box[@sec-the-density-layer-counting-vocabulary-and-the-bohrlandau-the]).`
   Tested: "(see Section 4)" on one line; only that paragraph reflows (still four lines).

2. typ/01-introduction.typ line 72, page 4. `Appendix A tabulates the eleven runs, and Appendix B lists`
   breaks as "... and Appendix" / "B lists ...". Fix: `Appendix~A tabulates the eleven runs, and Appendix~B lists`;
   for the same reason `(Appendix~A).` in line 110 and `and Appendix~A).` in typ/06-numerics.typ line 78.
   Optional: make them clickable like the section references, `#link(<sec-appendix-a-the-eleven-runs>)[Appendix~A]`
   and `#link(<sec-appendix-b-principal-lean-theorems>)[Appendix~B]` (tested, targets pages 29 and 30).

3. typ/06-numerics.typ lines 28 to 40, pages 22 and 23. The captions print "Figure 1: (exploratory; proves nothing)."
   and "Figure 2: (exploratory; proves nothing)."; paper.md has "Figure 1 (exploratory; proves nothing)." without a colon.
   Fix: insert the line `#set figure.caption(separator: [ ])` before the first
   `#page(flipped: true, margin: (x: 0.8in, y: 0.9in))[` (line 28). Tested: "Figure 1 (exploratory; ...".

4. refs.real.bib lines 32 and 277, page 32, entries [5] and [4]. The md entries refer to other entries:
   "(Lean 4 formalization of the theorem of [alpoge-furman])" and "paper.pdf in [openai-math]". The bib file
   replaces them by words: `of the theorem of Alpöge and Furman)` and `paper.pdf in OpenAI, openai/math`.
   Fix: `of the theorem of [6])` and `paper.pdf in [3]` (tested: prints "[6]" and "[3]"); add a comment that
   the two numbers follow the order of first citation.

5. refs.real.bib lines 48, 179, 300, pages 33 [16], 32 [12], 34 [34]. Three invisible WORD JOINER characters
   (U+2060) after `ZetaZeros`, `PALOMAR` and `PrimeNumberTheoremAnd` are in the PDF text: a reader who copies
   the path `ZetaZeros/Analytic/RealSegment.lean` or the entry number gets a hidden character, and a search
   for "PALOMAR-2026-10-07-000009" misses the entry. They are no longer needed: with
   `#show bibliography: set text(hyphenate: false)` in main.typ the build without them has identical line breaks.
   Fix: delete the three characters and the last three lines of the header comment.

6. refs.real.bib, 19 entries, pages 32 to 34. Given names are reduced to initials by the ieee style
   ("L. Alpöge and R. Furman" for "Levent Alpöge and Ralph Furman"), while [28] prints full names.
   Entries: alpoge-furman, bohr-landau-1914, bohr-landau-1914b, fiori-2026, guth-maynard, hubbard-goldbach-lean,
   landrun, lean4, levinson-montgomery-1974, lewko-density-32, -34, -3917, -improved, liu-2026,
   platt-trudgian-2021, pnt-plus, selberg-1946, speiser-1934, tao-trudgian-yang.
   Fix, if the names are to print as in paper.md: write the author field as in the aristotle entry, in double braces
   with the md text, for example `author = {{Levent Alpöge and Ralph Furman}},`,
   `author = {{Alex Kontorovich and Terence Tao (organizers)}},`, `author = {{Terence Tao, Tim Trudgian and Andrew Yang}},`.
   Tested: all 19 print as in the md. Otherwise keep the initials as the convention of the style.

7. main.typ line 40, pages 32 to 34. The justified reference list has very loose lines where a 40-digit hash,
   a path or a URL cannot break: [4] lines 1 and 2, [5] lines 1 and 2, [12] line 1, [16] line 1, [17] lines 1 and 3,
   [25] line 1. Fix: add after line 40 `#show bibliography: set par(justify: false)`. Tested: even word spacing.

8. main.typ (style output), pages 32 to 34. Doubled word space, measured as twice the neighbouring gaps:
   [2] "Springer,  2021", [18] "American Mathematical Society,  1973", [33] and [38] "[Online].  Available:".
   Fix: add after line 40
   `#show bibliography: it => {` / `  show regex("[ ]{2,}"): [ ]` / `  it` / `}`. Tested: single spaces.

9. main.typ, pages 32 and 33, entry [13]. The entry is split by the page break (its URL is on page 33).
   Fix: add after line 40 `#show bibliography: set grid.cell(breakable: false)`. Tested: [13] moves whole to page 33.

10. refs.real.bib / main.typ, pages 32 and 33. The 15 items that md/99-references.md has in backticks (10 commit
    hashes, 3 file paths, `zeta23/`, `riemannZeta_real_neg`) print in the text font, not in the code font used
    for inline code elsewhere. Optional fix, inside the show rule of point 8, before `it`:
    `show regex("(commit|commits|and|file|project|theorem) ([0-9a-f]{40}|[^ ]+\\.lean|[^ ]+\\.pdf|zeta23/|riemannZeta_real_neg)"): m => {`
    / `  let i = m.text.position(" ")` / `  [#m.text.slice(0, i) #raw(m.text.slice(i + 1))]` / `}`.
    Tested together with points 7 and 8: the 15 items are in the code font, the URLs are untouched.

11. refs.real.bib line 289, page 34, entry [39]. `3·10^12` prints with a caret glyph, "3·10ˆ12". This is the
    literal text of md/99-references.md, so it is faithful; if a superscript is wanted, write `3·10¹²`
    (tested: New Computer Modern has the glyphs, punctuation unchanged). `$3 dot 10^12$` also works but
    moves the comma outside the closing quote.

12. main.typ line 12, page 1 (noticed while checking the metadata; outside the lens proper).
    `date: [11 November 2026],` prints "11 November 2026"; paper.md has "Date: 2026-11-11 (UTC)".
    Fix: `date: [2026-11-11 (UTC)],`.
