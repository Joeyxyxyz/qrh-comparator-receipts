# Text-fidelity review of main.pdf against paper.md

Reviewed: `main.pdf` (34 pages, built 2026-11-10 20:29) from `main.typ`, `typ/*.typ`, `refs.real.bib`,
against `../paper.md` (and its split in `md/`). No source file was edited. Scratch scripts and a
scratch copy with every proposed fix applied are in `review-tf/` (safe to delete).

## Verdict

The text is faithful. 0 major, 7 minor findings.

Every paragraph, list item, table cell and code block of paper.md is in the Typst sources and in the PDF,
once, in order, with the same words. No stray markup is visible. The findings are differences of
form: one date format, slash against built fraction in two section files, the figure-caption
separator, and four points in the bibliography and the code blocks.

## What was compared, and the result

1. Typst sources against Markdown, section by section (`review-tf/norm.py`): both sides reduced to a
   token stream (headings, list items, bold, emphasis, cross-references by label, citations by key,
   table rows and cells; code and math replaced by placeholders and compared separately).
   Result for all ten section files: prose tokens identical; 432 inline code spans identical in order
   and bytes; 18 code blocks byte-identical including their fences; 597 formulas paired one to one.
   The only token differences are wrappers (`#import`, `#figure(`, `#page(`, `#box[`, appendix numbering).
2. Formulas (`review-tf/mathcmp.py`): each TeX formula against its Typst counterpart by symbols, letters
   and numbers in order, plus counts of `^`, `_`, primes, commas, slashes and fractions. All 597 agree in
   symbols and numbers; 35 differ in slash against fraction (finding 2).
3. Headings and references: 47 headings carry the label of LABELS.md; all 50 italic-title references of
   paper.md print the section number of the heading they name (checked number by number); the two
   literal "Section 9.15" / "Section 7.2" (of Titchmarsh) are unchanged.
4. PDF text against Markdown (`review-tf/pdfcmp2.py`, word alignment of 17,594 source words): the body
   from the abstract to the end of Appendix B aligns with no dropped, changed or duplicated word; the
   only differences are the title-block labels and date (finding 1), cell order inside tables as
   pdftotext reads wrapped cells, and the text inside the two figure images.
5. Tokens: every inline code span, every code-block line, every number, date, time, version and hash of
   the source occurs in the PDF text at least as often as in the source (the three apparent misses are
   names broken across table-cell lines or a code block split over pages 13/14).
6. Markup residue in the PDF text: no `$`, backslash, `[@`, `##`, `**`, `sec-`, backtick, `#cite`,
   `#box`; `*`, `#`, `@`, `~`, `|` occur only where the source has them (Lean code, `#check`,
   `#print axioms`, `~AF_UNIX`, "~2-2.5 sigma", `[PROVED | 7/8]`). 172 straight double quotes of the
   body became 86 opening and 86 closing quotes, none reversed; 228 apostrophes became 228.
7. Front matter: title, abstract (315 words) and the ten keywords identical to md/00-front.md.
8. References: 39 entries in the source, 39 in the PDF; compared entry by entry. All 20 URLs and 13 DOIs
   of the source are link targets in the PDF, and the PDF has no other link.
9. Pages: word boxes of all 34 pages checked for text outside the margins or overprinting (none), and
   pages 1, 4, 5, 11 to 24, 28 to 33 read as images.

## Findings

All line numbers are those of the current files.

### 1. minor: main.typ, title block (page 1): the date is reworded

Source: `Date: 2026-11-11 (UTC)`. Typst: `  date: [11 November 2026],` (main.typ line 12). The PDF prints
"11 November 2026": another format than the ISO dates of the rest of the paper, and "(UTC)" is dropped.

Fix: `  date: [2026-11-11 (UTC)],`

### 2. minor: typ/04-bohr-landau.typ and typ/06-numerics.typ (pages 14 to 17, 23 to 25): an inline slash of the source is set as a built fraction, 35 formulas

Where paper.md writes a slash inside a formula (`$\sigma>1/2$`), files 01, 03, 05, 09, 10 and main.typ
write `slash` and print "1/2". Files 04 and 06 write `/`, which Typst builds into a stacked fraction.
The meaning is the same, but (a) the symbols differ from the source and from the other sections: page 17
has "for Δ ≥ ½" (Section 4.5, stacked) a few lines above "for 1/2 < σ₁ < σ ≤ 1" (Section 5.1); (b) the
distinction the source makes between `1/2` and `\tfrac12` is lost in these two files; (c) the extracted
PDF text reads "12", "23", "13", "16", "32" for 1/2, 2/3, 1/3, 1/6, 3/2 (for example "|𝛽 − 12 | ≥ Δ"), so
these numbers of the source cannot be found by search or copied; (d) on page 24 the inline exponent
"1 − (2σ₁−1)²/(2σ₁)" becomes a stacked fraction with a superscript in running text.
The formulas where the source has `\tfrac`/`\frac` are correct as they are and are not listed.

Fix: in exactly these formulas replace `/` by ` slash ` (list also in `review-tf/slashfix.json`;
applied and compiled in `review-tf/t/typ/`, still 34 pages):

typ/04-bohr-landau.typ

| line | page | now | fix |
|---|---|---|---|
| 34 | 14 | `$0 < abs(beta - 1/2) < delta$` | `$0 < abs(beta - 1 slash 2) < delta$` |
| 34 | 14 | `$abs(beta - 1/2) >= Delta$` | `$abs(beta - 1 slash 2) >= Delta$` |
| 39 | 14 | `$2/3 - epsilon$` | `$2 slash 3 - epsilon$` |
| 47 | 14 | `$1/3 + epsilon$` | `$1 slash 3 + epsilon$` |
| 69 | 14 | `$sigma > 1/2$` | `$sigma > 1 slash 2$` |
| 73 | 15 | `$abs(beta - 1/2) >= delta$` | `$abs(beta - 1 slash 2) >= delta$` |
| 74 | 15 | `$sigma > 1/2$` | `$sigma > 1 slash 2$` |
| 81 | 15 | `$1/2$` | `$1 slash 2$` |
| 82 | 15 | `$abs(zeta(2 + i t)) >= 1/3$` | `$abs(zeta(2 + i t)) >= 1 slash 3$` |
| 113 | 16 | `$sigma > 1/2$` | `$sigma > 1 slash 2$` |
| 116 | 16 | `$1/2 < sigma_1 < 1$` | `$1 slash 2 < sigma_1 < 1$` |
| 116 | 16 | `$sigma_1 - 1/2 < delta <= 1/2$` | `$sigma_1 - 1 slash 2 < delta <= 1 slash 2$` |
| 117 | 16 | `$beta >= 1/2 + delta$` | `$beta >= 1 slash 2 + delta$` |
| 119 | 16 | `$delta > sigma_1 - 1/2$` | `$delta > sigma_1 - 1 slash 2$` |
| 120 | 16 | `$0 < delta < 1/2$` | `$0 < delta < 1 slash 2$` |
| 120 | 16 | `$sigma_1 = 1/2 + delta/2$` | `$sigma_1 = 1 slash 2 + delta slash 2$` |
| 120 | 16 | `$delta >= 1/2$` | `$delta >= 1 slash 2$` |
| 136 | 16 | `$sigma_1 >= 2/3$` | `$sigma_1 >= 2 slash 3$` |
| 137 | 16 | `$a = 3/2$` | `$a = 3 slash 2$` |
| 137 | 16 | `$2/3 <= sigma_1 < 1$` | `$2 slash 3 <= sigma_1 < 1$` |
| 137 | 16 | `$delta > sigma_1 - 1/2$` | `$delta > sigma_1 - 1 slash 2$` |
| 137 | 16 | `$delta > 1/6$` | `$delta > 1 slash 6$` |
| 139 | 16 | `$sigma_1 > 1/2$` | `$sigma_1 > 1 slash 2$` |
| 153 | 17 | `$Delta >= 1/2$` | `$Delta >= 1 slash 2$` |
| 153 | 17 | `$0 < Delta < 1/2$` | `$0 < Delta < 1 slash 2$` |
| 153 | 17 | `$1/2 < op("Re") s < 1/2 + Delta$` | `$1 slash 2 < op("Re") s < 1 slash 2 + Delta$` |

typ/06-numerics.typ

| line | page | now | fix |
|---|---|---|---|
| 38 | 23 (caption of Figure 2) | `$beta - 1/2$` | `$beta - 1 slash 2$` |
| 38 | 23 | `$abs(beta - 1/2) > 3/8$` | `$abs(beta - 1 slash 2) > 3 slash 8$` |
| 38 | 23 | `$abs(beta - 1/2) >= Delta$` | `$abs(beta - 1 slash 2) >= Delta$` |
| 38 | 23 | `$0 < abs(beta - 1/2) < Delta$` | `$0 < abs(beta - 1 slash 2) < Delta$` |
| 55 | 24 | `$1 - (2 sigma_1 - 1)^2/(2 sigma_1)$` | `$1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)$` |
| 55 | 24 | `$O(T (log T)^(3/5))$` | `$O(T (log T)^(3 slash 5))$` |
| 72 | 24 | `$1/3 + epsilon$` | `$1 slash 3 + epsilon$` |
| 75 | 25 | `$2/3 + epsilon$` | `$2 slash 3 + epsilon$` |
| 75 | 25 | `$5/9 + epsilon$` | `$5 slash 9 + epsilon$` |

### 3. minor: typ/06-numerics.typ lines 29 to 32 and 36 to 39 (pages 22, 23): "Figure 1:" for the source's "Figure 1"

Source: `![Figure 1 (exploratory; proves nothing). Normalized spacings ...` and
`![Figure 2 (exploratory; proves nothing). The pair measure ...`.
Typst: `caption: [(exploratory; proves nothing). Normalized spacings ...`; the PDF prints
"Figure 1: (exploratory; proves nothing). ..." and "Figure 2: (exploratory; proves nothing). ...": a colon
that the source does not have, in front of a parenthesis.

Fix (tested: prints "Figure 1 (exploratory; proves nothing). Normalized ..."): in typ/06-numerics.typ,
directly after `#import "/template.typ": rtable`, add

    #show figure.where(kind: image): set figure.caption(separator: [ ])

### 4. minor: refs.real.bib lines 48, 179, 300 (references [16] p. 33, [12] p. 32, [34] p. 34): three invisible characters inside identifiers

`file ZetaZeros⁠/Analytic/RealSegment.lean`, `entry PALOMAR⁠-2026-10-07-000009` and
`(PrimeNumberTheoremAnd⁠)` each contain a WORD JOINER (U+2060) that paper.md does not have. It reaches the
PDF text: a search for `PALOMAR-2026-10-07-000009` or `ZetaZeros/Analytic/RealSegment.lean` does not find
references [12] and [16], and a copied identifier carries the hidden character. The header of the file
gives the reason (to keep Typst from hyphenating these names); main.typ now has
`#show bibliography: set text(hyphenate: false)`, which does that for the whole list.

Fix: delete the three U+2060 characters and the three header lines that describe them (lines 15 to 17).
Tested: no hyphenation in the reference list, the three identifiers stay whole, 34 pages.

### 5. minor: refs.real.bib lines 32 and 277 (references [5] and [4], page 32): two cross-references of the source are replaced by words

Source, anthropic-formal-math: "(Lean 4 formalization of the theorem of [alpoge-furman])"; the PDF has
"(Lean 4 formalization of the theorem of Alpöge and Furman)".
Source, openai-qrh: "file `preprints/.../paper.pdf` in [openai-math]"; the PDF has
"... paper.pdf in OpenAI, openai/math".

Fix: write the reference numbers, which are fixed by the order of first citation in the final text
(alpoge-furman is [6], openai-math is [3]): line 32 `... formalization of the theorem of [6]). GitHub repository, ...`,
line 277 `... /paper.pdf in [3]},`. Tested: prints "theorem of [6])" and "paper.pdf in [3]." If a number
in a .bib field is judged too fragile, leave both as they are; the wording is then a paraphrase, not an error.

### 6. minor: refs.real.bib, author fields (pages 32 to 34): given names are reduced to initials

The reference list of paper.md gives full names where it has them ("Levent Alpöge and Ralph Furman",
"Harald Bohr and Edmund Landau", "Mark Lewko", "Atle Selberg", ...); the "ieee" style prints "L. Alpöge
and R. Furman", "H. Bohr and E. Landau", "M. Lewko", "A. Selberg". 28 given names in 19 entries
([2], [6], [7], [11] to [15], [17], [24] to [27], [30], [33], [34], [37] to [39]) are affected; [28] keeps
its names because its author field is already literal. This is the convention of the chosen style, and
no name is wrong; it is listed because the conversion rule is that names do not change.

Fix, if the full names are wanted: make the author fields literal, as `aristotle` already is, e.g.
`author = {{Levent Alpöge} and {Ralph Furman}}`, `author = {{Mark Lewko}}`,
`author = {{Alex Kontorovich} and {Terence Tao (organizers)}}` (which also removes the
`Tao, (organizers), Terence` workaround). A complete tested version is `review-tf/t/refs.names.bib`
(findings 4 and 5 applied as well; it prints all 39 entries with the names of paper.md, 34 pages).
For [38] the style still adds a comma ("Terence Tao, Tim Trudgian, and Andrew Yang"); a single literal
`{{Terence Tao, Tim Trudgian and Andrew Yang}}` gives the source's wording.

### 7. minor: 15 lines of Lean code are longer than the block and wrap without a mark (pages 11, 13, 14, 16, 17, 19, 20)

The code blocks are byte-identical to the source, but the template sets them at 7.8pt, about 90
characters to the line, and these source lines are longer. The continuation starts at the left edge, so a
one-line statement reads as two lines, and the reader cannot tell a wrap from a line break of the source
("Lean statements are printed verbatim"):
typ/03-runs-mnf.typ lines 67, 80, 81, 139; typ/04-bohr-landau.typ lines 42, 54, 110, 130, 145;
typ/05-density-cube.typ lines 17, 69, 70, 71, 119, 137.
Examples: page 14 `... (NOff δ 0 T : ℝ) ≤ C *` / `T`; page 19 `... in 0..1 /` / `2, ↑(MNF.RH.NOff δ 0 T)`;
page 20 `... ¬MNF.RH.Degenerate ρ)` / `↔`.

Fix (tested on the whole paper: same text, 34 pages; wrapped continuations are indented 2.4em, source
indentation, blank lines and highlighting are kept; the template is not edited): in main.typ, after the
`#show: paper.with(...)` call and before the first `#include`, add

    #show raw.where(block: true): it => block(
      width: 100%, fill: luma(245), inset: (x: 7pt, y: 6pt), radius: 2pt, breakable: true,
      {
        set text(font: "DejaVu Sans Mono", size: 7.8pt)
        set par(justify: false, hanging-indent: 2.4em, leading: 0.62em, spacing: 0.62em)
        for l in it.lines { if l.text == "" { par(hide[x]) } else { par(l.body) } }
      },
    )

(`review-tf/t/main-raw.typ` has it in place.) If the layout review prefers the plain wrap, no change is
needed for fidelity: no character is lost.

## Seen and not counted as problems

- Citations print as IEEE numbers in order of first citation, several as "[12], [13], [14], [15]"; the
  reference list is therefore in citation order, not in the key order of paper.md. Titles are in quotation
  marks, "DOI" prints as "doi:", "In:" as "in", volume and pages get "vol." and "pp.", a URL is introduced by
  "[Online]. Available:". These come from the style; every word, number, hash, URL and DOI of each of the
  39 source entries is present (apart from findings 4 to 6).
- Hashes, file paths and the theorem name that the source's reference list has in backticks are set in the
  text font in the bibliography; a .bib field cannot carry code formatting. The characters are the same.
- "Keywords." with a closing period, the running head "Receipted Comparator checks" and the omitted labels
  "Author:", "Date:", "Repository:" come from the template.
- The two figure images carry their own lettering; `figures/*.svg` differs from `../figures/*.svg` only in
  the `font-family` attribute.
- A code block is split between pages 13 and 14 at its blank line; long Lean names in Appendix B break
  after a dot without a hyphen. Nothing is lost in either case.
