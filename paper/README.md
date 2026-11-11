# The paper

**Receipted Comparator Checks of Two Lean Proofs on Zeros of the Riemann Zeta Function, with
Formalizations of the Bohr–Landau Theorem and a Zero-Density Estimate.** Joey Messina, 2026-11-11.
34 pages: [`Messina_2026_Receipted_Comparator_Checks.pdf`](Messina_2026_Receipted_Comparator_Checks.pdf).

The paper describes the record of this repository as of commit
`9a6a1d9760847fb63e071c73b5f6c9c85f766653`; this folder was added in the commit after it. What the
paper does not claim is stated in its Section 1.3: nothing in it proves, or is evidence for, the
Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

| path | what |
|---|---|
| `Messina_2026_Receipted_Comparator_Checks.pdf` | the paper |
| `paper.md` | the text as reviewed (Markdown with TeX math); the PDF is typeset from it |
| `typst/` | the typesetting source: `main.typ`, `template.typ`, the ten section files under `typ/`, `refs.real.bib`, the two figures, `build.sh` |
| `review/facts/` | six fact sheets extracted from the record, with file evidence, from which the text was drafted |
| `review/content/` | the review of the text: five reviewers with separate lenses (Lean fidelity, receipts and numbers, claims and framing, literature and attribution, mathematical exposition), what was applied (`APPLIED.md`), then two further readers (`final-referee.md`, `final-statements.md`) |
| `review/typeset/` | the comparison of the typeset PDF with the text (text, math, layout, references) and what was applied |

**How it was made.** The text, like the documents of the record, was produced with Claude Code
(Anthropic's coding agent) under the author's direction, from the receipts and sources in this
repository; the reviewers named above were model reviewers (Claude Code agents). The author set
the goals and is responsible for the claims. Where the paper and the receipts differ, the receipts
and the Lean statements govern.

**Building the PDF.** `cd typst && typst compile --root . main.typ main.pdf` with Typst 0.15, or
`./build.sh /path/to/unpacked-wheel` with the Python wheel `typst` 0.15.2 from PyPI
(`typst-0.15.2-cp39-abi3-manylinux2014_x86_64.manylinux_2_17_x86_64.whl`, sha256
`99fe0916980cab453e60332125e133c737bf3b76efd325b60d055c551e5887a1`), which is how the deposited PDF
was built. The fonts New Computer Modern and DejaVu Sans Mono ship with Typst; the two figures
use DejaVu Sans, which must be installed. To print a DOI on the title page, set `paper-doi` at the
top of `main.typ`.

**License.** The text of the paper and its source are under CC BY 4.0. The record's own files keep
the Apache License 2.0 (`../LICENSE`, `../NOTICE`).
