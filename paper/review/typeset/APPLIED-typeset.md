# Review findings applied to the typeset paper

Build: `main.typ` -> `main.pdf`, 34 pages (as before), 0 compiler warnings. `template.typ` is unchanged.
Files edited: `main.typ`, `refs.real.bib`, `typ/01-introduction.typ`, `typ/03-runs-mnf.typ`, `typ/04-bohr-landau.typ`,
`typ/05-density-cube.typ`, `typ/06-numerics.typ`, `typ/08-authorship.typ`. Derived files refreshed from the new PDF:
`main.txt` (`pdftotext -layout`) and `pages/p-01.png` to `p-34.png` (80 dpi). The files as they were before this step are in
`out/apply/backup/`.

42 findings: 38 APPLIED, 4 REJECTED. Findings are numbered lens.position in the order of the review JSON
(lens 0 text fidelity, 1 math fidelity, 2 layout, 3 references and cross-references).

## Lens 0, text fidelity

| # | Finding | Result | Reason and what was done |
|---|---|---|---|
| 0.1 | Date printed "11 November 2026" | APPLIED | paper.md has `Date: 2026-11-11 (UTC)`. `main.typ`: `date: [2026-11-11 (UTC)]`. Page 1 prints "2026-11-11 (UTC)". |
| 0.2 | 26 formulas of `typ/04-bohr-landau.typ` set a slash of the source as a stacked fraction | APPLIED | Checked each against `md/04-bohr-landau.md`: all 26 have an inline slash there. `/` replaced by ` slash ` in exactly these 26 (lines 34, 39, 47, 69, 73, 74, 81, 82, 113, 116, 117, 119, 120, 136, 137, 139, 153). The `/` that remain in the file all stand where the source has `\frac` or `\tfrac` (compared formula by formula for all section files). The PDF text now reads "1/2", "2/3", "1/6" and so on. |
| 0.3 | 9 formulas of `typ/06-numerics.typ`, the same | APPLIED | The source has slashes in all 9 (`md/06-numerics.md` lines 20, 26, 34). Replaced in lines 38 (4), 55 (2), 72, 75 (2). |
| 0.4 | Captions print "Figure 1: (exploratory; ..." | APPLIED | paper.md has "Figure 1 (exploratory; proves nothing)." Done once in `main.typ` (`#set figure.caption(separator: [ ])`), not in file 06: the two figures are the only captions of the paper. Pages 22 and 23 print "Figure 1 (exploratory; ..." and "Figure 2 (exploratory; ...". |
| 0.5 | Three invisible U+2060 in `refs.real.bib` | APPLIED | Removed, with the header lines that described them. `main.typ` already switches hyphenation off in the list; the three identifiers are whole and searchable in the PDF text. |
| 0.6 | Two references from one entry to another replaced by words | APPLIED, in another way | The source has "[alpoge-furman]" and "[openai-math]". A literal number in the .bib would be wrong after any renumbering, so the field now holds `⟦alpoge-furman⟧` and `⟦openai-math⟧` and a rule in `main.typ` replaces each by a citation of that key. Prints "theorem of [6])" in [5] and "paper.pdf in [3]." in [4]; the numbers follow the list. |
| 0.7 | Given names reduced to initials in 19 entries | APPLIED | The rule of the conversion is that names do not change, and entry [28] already printed full names. Every personal author field is now one literal name holding the words of `md/99-references.md` (checked by script against that file for all 27 such entries), e.g. `{{Levent Alpöge and Ralph Furman}}`, `{{Alex Kontorovich and Terence Tao (organizers)}}`, `{{Terence Tao, Tim Trudgian and Andrew Yang}}`. Authors that the source gives with initials print as before. |
| 0.8 | Wrapped code lines continue at the left edge (optional) | APPLIED, in the variant of 2.1 | See 2.1; one rule serves both findings. |

## Lens 1, math fidelity

| # | Finding | Result | Reason and what was done |
|---|---|---|---|
| 1.1 | Section 4: stacked fractions for slashes | APPLIED | Same edit as 0.2. |
| 1.2 | `typ/06` line 55: density exponent and (log T)^(3/5) stacked | APPLIED | Same edit as 0.3; page 24 prints "1 − (2σ₁ − 1)²/(2σ₁)" and "(log T)^{3/5}" with slashes. |
| 1.3 | `typ/06` lines 38, 72, 75 stacked | APPLIED | Same edit as 0.3. |
| 1.4 | `typ/01` lines 35 and 44: formulas broken inside the absolute value | APPLIED | Both still broke after the other changes; each is now in `#box[...]`. In item 4 the paragraph then re-broke twice as "T ≥" / "2", so the two short formulas `$T >= 2$` of that item are boxed as well. Page 3: no formula of item 4 is split, no loose line. |
| 1.5 | `typ/03` line 99: "ζ′(1 −" / "s) = ..." | APPLIED | `#box[...]`; page 12. |
| 1.6 | `typ/04` line 89: "(B₂({u}) −" / "1/6)/2" | REJECTED | Tried twice. With the whole formula boxed the line before it has a mean gap of 8.8 pt (normal 3.5 pt); with only the parenthesis boxed, 6.3 pt. The reviewer marked the box optional for this reason. The formula keeps its break after the minus sign (page 15); it is the only formula of the paper still split inside a delimiter. |
| 1.7 | `typ/05` line 30: "3(1 −" / "σ)/(2 − σ)" | APPLIED | `#box[...]`; page 17. |
| 1.8 | `typ/06` line 75: "(N(T) +" / "N₀(T))" | APPLIED | `#box[...]`; the formula now opens page 25 whole. |
| 1.9 | `typ/04` line 88: `\tfrac12` set as a display-size fraction | APPLIED | `inline(1/2)`, as in the pair-sum display of file 05; page 15. |
| 1.10 | Quoted "≤" taken from the fallback font | APPLIED | `typ/06` line 86, both quotations: the character stays, `#text(font: "New Computer Modern Math", weight: 450)[≤]`. The weight is added so that the glyph comes from the face the formulas use (NewCMMath-Book); without it a second math face was embedded. Libertinus Serif is no longer in the PDF; the text layer still has "Δ ≤ 3/8". |

## Lens 2, layout

| # | Finding | Result | Reason and what was done |
|---|---|---|---|
| 2.1 | Code lines longer than the box wrap at column 0 (major) | APPLIED | The rule of the finding is in `main.typ` (7.5 pt, each source line its own paragraph, hanging indent of four columns beyond the line's indentation, block not breakable; the longest block has six lines). Checked: the 18 code blocks of the typ files are byte-identical to those of paper.md, each is in the PDF text with no character added or lost, every source line starts a line, the blank line of the block on page 14 is kept. As the finding foresaw, the display of Section 5.5 then opened page 21 alone; the paragraph and display of Section 5.5 (lines 140 to 142 of `typ/05` as reviewed) are wrapped in the non-breakable block it gives, so the paragraph and its display stand together on page 21. |
| 2.2 | Reference list justified with very loose lines (major) | APPLIED | `#show bibliography: set par(justify: false)`. See 3.9 for the page count. |
| 2.3 | Caption separator; centred last line of the captions | APPLIED | `#set figure.caption(separator: [ ])` and `#show figure.caption: set align(left)` in `main.typ`. |
| 2.4 | Section 4 slashes | APPLIED | Same edit as 0.2. After it one paragraph of Section 4.4 split two more short formulas at a relation sign ("N =" / "Tᵃ", "a =" / "3/2"); four short formulas of that paragraph are boxed (lines 133, 135, 136, 137). The paragraph has no split formula and no loose line (page 16). |
| 2.5 | Section 6 slashes | APPLIED | Same edit as 0.3. |
| 2.6 | `typ/05`: loose lines before two long code names | APPLIED | The `breakable` helper of file 10 is copied to the top of the file and used for `Zeta23.BL.bohrLandau_explicit` (after a dot) and `nontrivial_zero_im_ne_zero` (after an underscore). Both lines are normal now (10.5 pt and 7.5 pt before). The first paragraph then split "(⅔A₁δ₀^{−3/2} +" / "B₁/2) T" inside its parentheses; that formula is boxed, with the semicolon after it written `\;` (a bare semicolon after a code expression is not printed). |
| 2.7 | `typ/08`: four very loose lines at the top of page 28 | APPLIED | Helper copied to the top of the file; the three `spectralGapHyp_...` names may break after an underscore. Page 28: all lines normal, one break `spectralGapHyp_iff_zeroFree_` / `strip`. |
| 2.8 | Code-only table cells stand 1.4 pt above the row's baseline | APPLIED | `#show table: set text(top-edge: 6pt)` in `main.typ`. Measured on page 5: the offset between "Mathlib" and its hashes went from 1.76 pt to 0.28 pt. Appendix A still fits page 29 and the table of Appendix B still ends on page 31. |
| 2.9 | Doubled space after a publisher without place | APPLIED | Rule in `main.typ`; the gaps after "Springer,", "Society," and before every "Available:" measure 3.50 pt. |
| 2.10 | Code block split across pages 13/14 | APPLIED | Covered by `breakable: false` in 2.1: the block opens page 14 whole. |
| 2.11 | Caret in the title of [39] ("3·10^12") | REJECTED | The characters are those of the reference list of paper.md; both reviewers left the choice to the author. Changing the characters of a title is not a conversion of markup. Left open (one-character edit: `3·10¹²`). |
| 2.12 | Figure 2 could be set larger; labels inside the image cross curves | REJECTED | The finding says no change is needed for legibility. With the margins of the other figure page the image still fits at 93% and no longer at 95% (the caption then runs 3.9 pt below the text area), a gain of 3%; narrower margins for this page alone would leave a few points of room and make the two figure pages differ. The crossed labels are in the SVG, outside this step. |

## Lens 3, references and cross-references

| # | Finding | Result | Reason and what was done |
|---|---|---|---|
| 3.1 | "(see Sec-" / "tion 4)" on page 11 | APPLIED, in another way | `#show ref: set text(hyphenate: false)` in `main.typ` in place of a box around the one reference: no printed reference can be hyphenated, whatever later changes move. Checked by building without the rule (the split returns) and with it (no "Sec-" at a line end in the PDF text). |
| 3.2 | "Appendix" / "B" split on page 4 | APPLIED | `Appendix~A` and `Appendix~B` in `typ/01` (lines 72, 110) and `typ/06` (line 78). The optional links were not added: the source has plain words here, not a reference, and a link would print in the accent colour unlike the section references. |
| 3.3 | Caption colon | APPLIED | Same edit as 0.4. |
| 3.4 | Entry-to-entry references in [4] and [5] | APPLIED | Same edit as 0.6. |
| 3.5 | U+2060 | APPLIED | Same edit as 0.5. |
| 3.6 | Given names | APPLIED | Same edit as 0.7. |
| 3.7 | Loose justified lines in the list | APPLIED | Same edit as 2.2. |
| 3.8 | Doubled spaces | APPLIED | Same edit as 2.9. |
| 3.9 | Entry [13] split by the page break | APPLIED | `#show bibliography: set grid.cell(breakable: false)`. With the full names, the code font of 3.10 and unbroken entries the list ran to a 35th page holding [39] alone; the space between entries is therefore 0.8em (paragraph spacing of the template: 0.95em), set in the same rule as 2.2. The list fills pages 32 to 34 (page 34 has 86 pt to spare). |
| 3.10 | The 15 backticked items of the list print in the text font | APPLIED | Rule in `main.typ`, with one addition: a file path may break after a slash (empty box, no character inserted). Checked with the font data of the PDF: exactly these 15 items are in the code font (18 runs, three items are broken over two lines), no URL is affected. |
| 3.11 | Caret in [39] | REJECTED | Same as 2.11; faithful to the source, left to the author. |
| 3.12 | Date | APPLIED | Same edit as 0.1. |

## Changes made beyond the wording of the findings

Each follows from an applied finding and changes no content.
- `typ/01`: `#box[$T >= 2$]` twice in item 4 (see 1.4).
- `typ/04`: four boxes in the paragraph of Section 4.4 (see 2.4).
- `typ/05`: one box with `\;` in Section 5.2 (see 2.6); the block around the paragraph and display of Section 5.5 (see 2.1).
- `main.typ`: space between reference entries 0.8em (see 3.9); a page range in the list is not split at its dash
  ("pp. 625–" / "635." appeared in [2] once the list was ragged).

## Checks on the final build

- 34 pages; all 34 page images read. No text beyond the margins except hanging punctuation (at most 2.3 pt, as before).
- Text of the new PDF against the PDF before this step, as token sequences: the only differences are the date, the slashes,
  the names and the two references in the list, the caption colons, the removed U+2060, and line-break artefacts.
  Punctuation counts of pages 1 to 31 agree except for the two caption colons and two pairs of parentheses
  ("(UTC)", and "(2σ₁)" which the stacked fraction had dropped).
- PDF metadata (title, author, ten keywords) unchanged.

## Left open

1. [39]: the title prints "3 · 10ˆ12" (caret of the source). Author's decision; `3·10¹²` was tested by the reviewers.
2. Page 15: "ψ₂ = (B₂({u}) −" / "1/6)/2" stays split (1.6).
3. Page 11: the line before "(see Section 4)" is somewhat loose (mean gap about 7 pt), the price of keeping "see Section 4"
   together and unhyphenated. Page 6: the two loose lines before `RestrictAddressFamilies=~AF_UNIX` are as before
   (the reviewer: can stay).
4. Pages 13 and 20 end a few lines short, because a code block (page 14) and a paragraph with its display (page 21) are
   kept whole.
5. Figure 2: three labels inside the image cross curves or the frame; only `figures/cube-relabeled.svg` can change that.
6. `harness-bib.typ` (a scratch harness of an earlier step) loads `refs.real.bib` without the rules of `main.typ` and would
   print the two `⟦key⟧` marks as they stand. Only `main.typ` builds the paper.
