# Converting paper.md (Markdown + TeX math) to Typst 0.15 for this paper

Build command (from the typst/ folder; the compiler is a Python module unpacked in the scratch area):

    python3 -I -c "import sys; sys.path.insert(0, sys.argv[1]); import typst; typst.compile(sys.argv[2], output=sys.argv[3])" <SCRATCH>/typst-env/site main.typ main.pdf

A compile error is raised as a Python exception whose text names the file, line and problem. Inspect pages with
`pdftoppm -r 80 -png main.pdf page` and read the PNGs; extract text with `pdftotext -layout main.pdf -`.

## The template (template.typ; do not edit it)

`#import "template.typ": *` gives:
- `paper(title:, short-title:, author:, date:, repository:, doi:, abstract:, keywords:, body)`, used once in main.typ through `#show: paper.with(...)`.
- `statement(kind: "Theorem", name: none, lean: none)[body]`: a ruled block for a theorem as formalized; `name` is a short
  plain-language name (content), `lean` the Lean constant as a string; the body is set in italics, so write math normally.
- `rtable(columns:, header: (...), align:, size: 8.6pt, ..cells)`: a ruled table whose header repeats on page breaks.
  Wrap a short table in `#figure(rtable(...), caption: [...])`; leave a long table (the appendix tables) unwrapped so it can break.
- Sections are numbered automatically: `= Title`, `== Subsection`, `=== Sub-subsection`. Never type section numbers.
- Unnumbered headings: `#heading(numbering: none)[Acknowledgments]`. Appendices: before the first appendix put
  `#counter(heading).update(0)` and `#set heading(numbering: "A.1")`, then `= The eleven runs` and so on.
- Figures: `#page(flipped: true, margin: (x: 0.8in, y: 0.9in))[#figure(image("figures/cube.svg", width: 100%), caption: [...]) <fig-cube>]`
  puts a wide figure on its own landscape page; refer to it with `@fig-cube` (renders as "Figure 2").
- Bibliography: citations are `@key` (several in a row: `@a @b`); with a supplement: `#cite(<key>, supplement: [§9.15])`.
  main.typ ends with `#bibliography("refs.bib", title: "References", style: "ieee")`.
- Cross-references to sections: put a label after the heading, `= The checking protocol <sec-protocol>`, and write `@sec-protocol`
  (renders as "Section 2").

## Markup differences from Markdown

| Markdown | Typst |
|---|---|
| `**bold**` | `*bold*` |
| `*emph*` or `_emph_` | `_emph_` |
| `` `code` `` | `` `code` `` (same) |
| fenced code block tagged lean | the same fence, tagged `lean` |
| `[text](url)` | `#link("url")[text]` |
| `- item` / `1. item` | `- item` / `+ item` |
| `> quote` | `#quote(block: true)[...]` |
| `---` rule | (drop) |
| `[@key]` | `@key` |

Characters that are special in Typst text and must be escaped with a backslash when meant literally: `#`, `$`, `@`, `<` (when
followed by a letter), `*`, `_` (only when not inside raw code), `~`, and a backslash itself. Lean names belong in backticks,
where nothing needs escaping. An en dash is `--` or the literal character; an em dash should not occur. Non-breaking space is `~`
(use it before citations and references: `Section~@sec-x`, `see~@key`). A percent sign is literal. Typographic quotes are produced
automatically from straight quotes.

## Math: TeX to Typst

Inline math is `$x$` with no spaces inside the dollars; display math is `$ x $` with a space after the opening and before the
closing dollar. There are no backslash commands: names are written bare.

| TeX | Typst |
|---|---|
| `\zeta \rho \beta \gamma \sigma \delta \Delta \theta \kappa \eta \pi \mu \alpha` | `zeta rho beta gamma sigma delta Delta theta kappa eta pi mu alpha` |
| `\varepsilon` / `\epsilon` | `epsilon` (this font shows the curly form; `epsilon.alt` is the lunate form) |
| `\le \ge \ne \approx \asymp \ll \gg \sim` | `<= >= != approx asymp << >> tilde` |
| `\to \mapsto \Rightarrow \iff \Leftrightarrow` | `-> |-> => <==> <=>` |
| `\cdot \times \pm \infty \partial` | `dot times plus.minus infinity partial` (`oo` also gives infinity) |
| `\frac{a}{b}` | `a/b` with parentheses as needed: `(a + b)/(c d)`; or `frac(a, b)` |
| `x^{a+b}` `x_{ij}` | `x^(a+b)` `x_(i j)` |
| `\sqrt{x}` | `sqrt(x)` |
| `\sum_{n \le X}` `\int_0^{1/2}` `\prod` | `sum_(n <= X)` `integral_0^(1/2)` `product` |
| `|x|` `\|f\|` `\lfloor x \rfloor` `\lceil x \rceil` | `abs(x)` `norm(f)` `floor(x)` `ceil(x)` |
| `\overline{\rho}` `\bar\rho` `\hat f` `\tilde f` | `overline(rho)` `overline(rho)` `hat(f)` `tilde(f)` |
| `\mathrm{Re}\, s` `\operatorname{Im}` | `"Re" s` or `op("Re") s`; `op("Im")` |
| `\log \exp \sin \cos \max \min \sup \inf \lim \arg \det` | the same names, bare |
| `\text{word}` | `"word"` |
| `N_{\mathrm{off}}` | `N_"off"` |
| `\mathbb{R} \mathbb{C} \mathbb{N} \mathbb{Z}` | `RR CC NN ZZ` |
| `\in \notin \subset \cup \cap \setminus \emptyset` | `in in.not subset union inter without emptyset` |
| `\forall \exists \neg \land \lor` | `forall exists not and or` |
| `\ldots \cdots` | `dots dots.c` |
| `\left( \right)` | plain parentheses scale automatically inside fractions; `lr(( ... ))` forces it |
| `\,` `\;` `\quad` | `thin` `med` `quad` |
| `\mathcal{L}` | `cal(L)` |
| `dx` in integrals | `dif x` |
| `\binom{n}{k}` | `binom(n, k)` |
| `\begin{cases}` | `cases(a "if" x > 0, b "otherwise")` |
| `\tfrac12` | `1/2` |
| `'` (prime) | `'` |

Pitfalls. (1) Two or more letters written together are read as ONE name: write `m rho` or `m(rho)`, never `mrho`; `T log T` is
fine because `log` is a known operator; an unknown multi-letter name such as `Li` is an error: write `"Li"`. Single letters next
to each other need spaces: `A T`, `2 sigma_1`, `x y`. (2) A subscript or exponent with more than one token needs parentheses:
`T^(5/6)`, `sigma_1` is fine, `N_0(T)` is fine, `e^(-s)`. (3) `/` builds a fraction and removes the outer parentheses of
numerator and denominator; when a slash should stay a slash (inline `1/2` in an exponent is fine as a small fraction) keep it; to
print a literal slash use `slash`. (4) A comma inside a function-like call separates arguments: `N(sigma, T)` is fine because `N`
is not a function, but inside `abs(...)`, `sqrt(...)`, `frac(...)` a literal comma must be `,` inside parentheses of its own or
written as `"," `. (5) `<=` and `>=` are fine in math; in running TEXT put every inequality, Greek letter and barred symbol in math mode (`$<=$`, `$rho$`, `$1 - overline(rho)$`) rather than typing the Unicode character, which would come from a fallback font. (6) `#` inside math starts
code: avoid. (7) Display equations that end a sentence carry their punctuation inside the dollars, after a `thin` or a space:
`$ a <= b . $`. (8) Multi-line displays: separate lines with `\` and align with `&`. (9) In headings and captions math works the
same. (10) `dot` is the centred multiplication dot; use it sparingly, as the paper does.

## Rules for this conversion

Convert, do not rewrite: every sentence, number, name, Lean statement and citation of paper.md must appear unchanged in meaning
and wording; change only the markup. Do not add, drop or reorder content. Lean code blocks are copied byte for byte. Keep one
sentence of text per source line where practical, so that diffs are readable. Compile after every few paragraphs.
