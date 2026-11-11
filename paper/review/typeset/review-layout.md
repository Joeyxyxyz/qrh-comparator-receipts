# Layout review of main.pdf (34 pages)

Lens: layout only. Every page was rendered (`pdftoppm -r 80 -png main.pdf lay/p`, pages in `lay/p-01.png` to `lay/p-34.png`)
and read one by one; details were re-read at 150 to 220 dpi, and word positions were measured with `pdftotext -bbox`.
No file of the paper was edited. Every fix below was tried in a scratch copy of main.typ and of the section files
(removed afterwards): with fixes 1 to 8 applied together the paper still has 34 pages and no new overflow.

Verdict: 2 major, 8 minor. Nothing runs past a margin or off a page.

## What was checked and is in order

- Margins: no word, code line, table cell or figure passes the text block. The largest overshoot is 2.3 pt, which is
  Typst's hanging punctuation and hyphens at line ends.
- Title block and abstract (p. 1): balanced four-line title, author, date, repository link, abstract and keywords inset; fine.
- Running header (author left, short title right, hairline) on pp. 2 to 34, absent on p. 1; page numbers centred at the
  foot, also on the five landscape pages (22, 23, 29, 30, 31).
- Headings: none is left alone at the foot of a page. Pages 4 and 9 end 40 to 45 pt short because a subsection heading
  and two lines would not fit; pages 21 and 28 end short (72 and 59 pt) because landscape pages follow, and the last
  paragraph of Section 6.1 resumes on p. 24 after the two figure pages, in the order of paper.md. No widow or orphan line.
- Tables: all inside the text width; the header of the Appendix B table repeats on p. 31; no row is split.
- Figure pages (22, 23): image and caption fit on one landscape page each.
- Cross-references print as "Section 2.3", citations as "[3], [4]"; the in-text URL on p. 26 is linked without its semicolon.
- Landscape appendices: the prose there runs at a measure of about 150 characters. Setting it in two columns was tried and
  costs two more pages (Appendix A spills one word, Appendix B needs a third page), so no change is proposed.

## Major

### 1. Long lines of the Lean code blocks wrap to column 0 (pp. 11, 13, 14, 16, 17, 19, 20)

- File to edit: `main.typ` (one rule; the section files stay byte for byte).
- Where: 15 source lines in 12 of the 18 code blocks are longer than the 90 characters that fit at 7.8 pt:
  - `typ/03-runs-mnf.typ` l. 67 `MNF.RH.riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3 / 8 < Δ) : RiemannHypothesis ↔ …` (117 characters, p. 11);
    l. 80 and 81 `MNF.RH.on_line_density_one_of_gap (hBL : MNF.RH.BohrLandau) (hN : …` (112 and 118, p. 11);
    l. 139 `sturm_liouville_simple_eigenvalues (V : ℝ → ℝ) (hV : IsConfiningPotential V) …` (119, p. 13).
  - `typ/04-bohr-landau.typ` l. 42 `MNF.RH.offLine_le_one_third : ∀ ε > 0, …` (114, p. 14);
    l. 54 `def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → … ≤ C * T` (92, p. 14: the continuation line is the single letter `T`);
    l. 110 `∃ C, ∀ (σ : ℝ), σ₁ ≤ σ → …` (114, p. 16); l. 130 `Zeta23.BL.bohrLandau_gt_sixth : …` (107, p. 16);
    l. 145 `@MNF.RH.onLineDensityOne_of_gap_only : …` (107, p. 16).
  - `typ/05-density-cube.typ` l. 17 `∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T ^ …` (119, p. 17);
    l. 69, 70, 71 `MNF.RH.reservoirMass_eq_integral …`, `MNF.RH.reservoirMass_le_rpow …`, `MNF.RH.meanDisplacement_tendsto_zero …` (114, 112, 110, p. 19);
    l. 119 `MNF.RH.noDegenerate_iff : (∀ (ρ : ℂ), … ¬MNF.RH.Degenerate ρ) ↔` (91, p. 20: the continuation line is a lone `↔`);
    l. 137 `@MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo : …` (93, p. 20: the continuation line is `≠ 0`).
- Problem: a wrapped line continues at column 0, exactly like a new source line. The paper says the statements are printed
  as Lean prints them, and a reader cannot tell Lean's line breaks from the typesetter's: on p. 19 three statements show as
  six flush-left lines and one indented line; on p. 11 a continuation begins `MNF.RH.NcountSuperlinear) {Δ : ℝ} …`, which
  reads like the start of a declaration. Three wraps leave one token on a line of its own.
- Fix (tested): in `main.typ`, between the `#show: paper.with(...)` call and `#include "typ/01-introduction.typ"`, add

  ```typst
  // Code blocks: a wrapped line continues four columns beyond the indentation of its own line; 7.5pt holds 94 columns;
  // a block is not split across pages. The source lines are not changed.
  #show raw.where(block: true): it => block(
    width: 100%, fill: luma(245), inset: (x: 7pt, y: 6pt), radius: 2pt, breakable: false,
    {
      set text(font: "DejaVu Sans Mono", size: 7.5pt)
      set par(justify: false, leading: 0.62em, spacing: 0.62em)
      for l in it.lines {
        let k = l.text.len() - l.text.trim(at: start).len()
        par(hanging-indent: (k + 4) * 0.602em, if l.text.trim() == "" { hide[x] } else { l.body })
      }
    },
  )
  ```

  Result in the test build: the three lines of 91 to 93 characters fit on one line; the other twelve wrap once with a
  hanging indent; syntax colours, the grey box and the blank line of the block on p. 13/14 are kept; `pdftotext` gives the
  same code text (the hidden `x` of an empty line is not in the text layer); 34 pages.
  After applying it, look at pp. 20/21: the one-line block of Section 5.5 lets three lines of the next paragraph stay on
  p. 20 and its display starts p. 21. To keep them together wrap that paragraph and its display
  (`typ/05-density-cube.typ` l. 140 to 142, from `For real $0 < sigma < 1$` to `abs(J(sigma)) <= 1/(2 sigma) . $`) in
  `#block(breakable: false, above: 0.95em, below: 0.95em)[ ... ]` (tested: the paragraph moves to p. 21 as a whole).

### 2. The reference list is justified and has lines with very wide word gaps (pp. 32 to 34)

- File to edit: `main.typ`, after l. 40 `#show bibliography: set text(hyphenate: false)`.
- Where: entries [1], [2], [4], [5], [12], [13], [16], [17], [25], [34], also [3], [19], [28]. Mean word gap 8 to 15 pt against
  3.5 pt normal; worst are [17] l. 1 `S. Hubbard, “goldbach-lean (described by its repository as AI-` (eight words over the
  full measure), [5] l. 1 and 2 and [16] l. 1 and 2.
- Problem: long unbreakable strings (hashes, URLs, registry numbers) with justification and no hyphenation leave rivers;
  these lines look broken.
- Fix (tested): add `#show bibliography: set par(justify: false)`. The list is then ragged right with even spacing and
  still ends on p. 34, 4 pt above the bottom margin: after any other change check that no line spills to a p. 35. One
  URL then breaks as `…000001-v1.` / `json` in [33]; acceptable.

## Minor

### 3. Figure captions print "Figure 1: (exploratory; …" and end with a centred line (pp. 22, 23)

- File to edit: `main.typ` (or the top of `typ/06-numerics.typ`).
- Where: `typ/06-numerics.typ` l. 31 and l. 38, `caption: [(exploratory; proves nothing). Normalized spacings …` and
  `caption: [(exploratory; proves nothing). The pair measure …`.
- Problem: paper.md has "Figure 1 (exploratory; proves nothing). …"; Typst's default separator adds a colon before the
  parenthesis. The caption is justified but its last line is centred (the figure's alignment), which looks like a mistake
  under a seven-line justified caption.
- Fix (tested): after `#show: paper.with(...)` add `#set figure.caption(separator: [ ])` and
  `#show figure.caption: set align(left)`. Prints "Figure 1 (exploratory; proves nothing). Normalized …", last line flush left.

### 4. Slash fractions of the source are set as built-up fractions in Sections 4 and 6 (pp. 14 to 17, 23 to 25)

- Files to edit: `typ/04-bohr-landau.typ`, `typ/06-numerics.typ`.
- Where (35 formulas in which paper.md writes a slash and the Typst source a bare `/`):
  - `typ/04-bohr-landau.typ` l. 34 `$0 < abs(beta - 1/2) < delta$`, `$abs(beta - 1/2) >= Delta$`; l. 39 `$2/3 - epsilon$`;
    l. 47 `$1/3 + epsilon$`; l. 69 and 74 `$sigma > 1/2$`; l. 73 `$abs(beta - 1/2) >= delta$`; l. 81 `$1/2$`;
    l. 82 `$abs(zeta(2 + i t)) >= 1/3$`; l. 113 `$sigma > 1/2$`; l. 116 `$1/2 < sigma_1 < 1$`, `$sigma_1 - 1/2 < delta <= 1/2$`;
    l. 117 `$beta >= 1/2 + delta$`; l. 119 `$delta > sigma_1 - 1/2$`; l. 120 `$0 < delta < 1/2$`, `$sigma_1 = 1/2 + delta/2$`,
    `$delta >= 1/2$`; l. 136 `$sigma_1 >= 2/3$`; l. 137 `$a = 3/2$`, `$2/3 <= sigma_1 < 1$`, `$delta > sigma_1 - 1/2$`,
    `$delta > 1/6$`; l. 139 `$sigma_1 > 1/2$`; l. 153 `$Delta >= 1/2$`, `$0 < Delta < 1/2$`, `$1/2 < op("Re") s < 1/2 + Delta$`.
  - `typ/06-numerics.typ` l. 38 (caption of Figure 2) `$beta - 1/2$`, `$abs(beta - 1/2) > 3/8$`, `$abs(beta - 1/2) >= Delta$`,
    `$0 < abs(beta - 1/2) < Delta$`; l. 55 `$1 - (2 sigma_1 - 1)^2/(2 sigma_1)$`, `$O(T (log T)^(3/5))$`; l. 72 `$1/3 + epsilon$`;
    l. 75 `$2/3 + epsilon$`, `$5/9 + epsilon$`.
- Problem: the same quantities print as "1/2" in Sections 1 to 3 and 5 and in the appendices and as small stacked fractions
  here; the lines that hold them are taller, so the line spacing of pp. 14 to 17 and 24 is uneven; on p. 24 the exponent
  3/5 is a stacked fraction about 3 pt high and the density exponent loses its parentheses. It also departs from the
  convention "same symbols" (guide, pitfall 3).
- Fix: write `slash` in these 35 formulas, as the other sections do: `$abs(beta - 1 slash 2) >= delta$`,
  `$sigma_1 = 1 slash 2 + delta slash 2$`, `$1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)$`, `$O(T (log T)^(3 slash 5))$`, and so on.
  Leave the fractions that paper.md writes with `\tfrac` or `\frac` (for example `N(1/2 + delta, T)` in l. 118 to 123 of
  file 04). Tested together with the other fixes: 34 pages.

### 5. Very loose lines before long inline code names (pp. 19, 21, 28; lesser on p. 6)

- Files to edit: `typ/05-density-cube.typ`, `typ/08-authorship.typ`.
- Where: p. 19, `typ/05-density-cube.typ` l. 77 `… made explicit (`Zeta23.BL.bohrLandau_explicit`): there are` (first line of
  the paragraph, mean word gap 10.5 pt); p. 21, l. 140 `… has a nonzero ordinate (`nontrivial_zero_im_ne_zero`).` (7.5 pt);
  p. 28, `typ/08-authorship.typ` l. 20 `It attributes six files of `MNF.RH` (`Core`, `Gap`, …` (the first four lines of the
  page, 9 to 11 pt, because `spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of` and
  `spectralGapHyp_three_eighths_iff` cannot break). Lesser: p. 6, `typ/02-protocol.typ` l. 69 before
  `RestrictAddressFamilies=~AF_UNIX` (7 pt).
- Fix (tested for pp. 19, 21, 28): give these names a break opportunity that inserts no character, with the helper that
  `typ/10-appendix-b.typ` already defines in l. 10 to 15. Copy `#let breakable(it, after) = { … }` to the top of files 05
  and 08 and write `(#breakable(`Zeta23.BL.bohrLandau_explicit`, "."))`, `(#breakable(`nontrivial_zero_im_ne_zero`, "_"))`,
  `#breakable(`spectralGapHyp_iff_zeroFree_strip`, "_")`, `#breakable(`spectralGapHyp_three_eighths_iff_of`, "_")`,
  `#breakable(`spectralGapHyp_three_eighths_iff`, "_")`. The names keep their backticks and their text; the lines become
  normal, with breaks `(Zeta23.BL.` / `bohrLandau_explicit)`, `(nontrivial_zero_` / `im_ne_zero)`,
  `(spectralGapHyp_iff_zeroFree_` / `strip,`.

### 6. In tables, cells that hold only code sit about 1.4 pt above the baseline of their row (pp. 4, 5, 12, 29, 30, 31)

- File to edit: `main.typ`.
- Where: for example `typ/02-protocol.typ` l. 27 `[Mathlib], [`d13f23b723b8`], [`51e6992efd06`],` (p. 5);
  `typ/01-introduction.typ` l. 83 `[`MNF.RH.Ncount 0 T`]` (p. 4); `typ/03-runs-mnf.typ` l. 106 `[`mnf-library`]` (p. 12);
  `typ/09-appendix-a.typ` l. 19 `[`qrh-main`]` and the two hash columns (p. 29); the first two columns of the Appendix B table.
- Problem: cells are top-aligned and the smaller mono type has a lower cap height, so its baseline is higher than that
  of the roman cells beside it; the rows look slightly stepped.
- Fix (tested): after `#show: paper.with(...)` add `#show table: set text(top-edge: 6pt)`. Baselines of a row then agree;
  row heights grow by under 1 pt; the Appendix B table still ends on p. 31.

### 7. Double space after the publisher in references [2] and [18] (pp. 32, 33)

- File to edit: `main.typ`.
- Where: `Springer,  2021, pp. 625–635` in [2] and `American Mathematical Society,  1973, pp. 181–193` in [18] (gap 7.0 pt
  against 3.5 pt, measured on the unjustified last line of [18]); [21] has the same at a line end. The entries are
  `@inproceedings` with a publisher and no place (refs.real.bib l. 142, 217, 227).
- Fix (tested): `#show bibliography: it => { show regex(" {2,}"): [ ]; it }` next to the other bibliography rules.

### 8. A code block is split between pp. 13 and 14

- Where: `typ/04-bohr-landau.typ` l. 21 to 27; `def ReservoirDensityOne` ends p. 13 and `def OnLineDensityOne` opens p. 14,
  each half in its own grey box.
- Fix: covered by `breakable: false` in the rule of finding 1 (tested: the whole block opens p. 14, p. 13 ends with its
  lead-in sentence).

### 9. Reference [39] prints a caret: "3 · 10ˆ12" (p. 34)

- File: `refs.real.bib` l. 289 `title = {The Riemann hypothesis is true up to 3·10^12},` (not a section file; the reference
  list of paper.md has the caret as plain text, the body writes the number as a formula).
- Fix (tested, optional): `3·10¹²` with the Unicode superscript digits, which the text font has; the comma stays inside
  the closing quotation mark. `$3 dot 10^(12)$` also renders but moves the comma outside the quotation mark.

### 10. Figure 2: small labels, some crossed by plot lines (p. 23)

- Files: `typ/06-numerics.typ` l. 35 to 37 (size), `figures/cube-relabeled.svg` (labels).
- Where: at `width: 90%` the labels of the image print at 6.1 pt (size 10 of a 1000-unit drawing set 609 pt wide), the
  legends at 6.7 pt; in Figure 1 the inset tick labels print at 5.5 pt. All legible, at the lower limit. Inside the image
  the note `R2 ~ (pi^2/3) u^2 is Montgomery's conjecture; GUE is already flatter here.` is crossed by the cubic and the GUE
  curve, `fit window [0.25, 0.75]` touches the staircase, `density strip: 2012 ordered pairs …` crosses the dashed frame.
- Fix: none is needed for legibility. Optional, in markup only: l. 35 `margin: (x: 0.6in, y: 0.7in)` with l. 37
  `width: 96%` sets the image 11% larger (labels 6.8 pt) and fitted with 3.5 pt to spare in a test build; `94%` leaves
  about 12 pt. The crossed labels can only be moved in the SVG.
