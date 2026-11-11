// Main file of the paper. Build from this folder (the project root), so that the root-relative paths
// used by the section files ("/template.typ", "/figures/...") resolve.
#import "template.typ": *

// Set the DOI here once it is assigned, as a string such as "10.5281/zenodo.1234567"; none prints no DOI line.
#let paper-doi = none

#show: paper.with(
  title: [Receipted Comparator Checks of Two Lean Proofs on Zeros of the Riemann Zeta Function, with Formalizations of the Bohr–Landau Theorem and a Zero-Density Estimate],
  short-title: [Receipted Comparator checks],
  author: "Joey Messina",
  date: [2026-11-11 (UTC)],
  repository: "https://github.com/Joeyxyxyz/qrh-comparator-receipts",
  doi: paper-doi,
  abstract: [
    This paper reports eleven runs of Comparator, the Lean FRO's proof judge, under a pinned, sandboxed protocol, each with a published receipt.
    Two runs repeat checks of public Lean 4 proofs on zeros of the Riemann zeta function: OpenAI's theorem that zeta has no zeros with real part above 7/8, and zeta23, Anthropic's formalization of Alpöge and Furman's theorem that more than two thirds of the zeros are simple and on the critical line (as judged: for every $epsilon > 0$, a proportion at least $2 slash 3 - epsilon$ at all large heights).
    Both ended in PASS: the pinned proof was accepted by the Lean kernel (and NanoDa for zeta23) against the pinned statement file, using only the axioms propext, Quot.sound and Classical.choice.
    Nine further accepted runs judge Lean files added to the verified trees: the author's library MNF.RH, and a layer formalizing the Bohr–Landau theorem, a zero-density estimate with a power saving weaker than Carlson's, a bound for the zeros' total displacement from the critical line that is far weaker than Littlewood's and Selberg's, two equivalences that restate, and do not prove, the Riemann hypothesis with simplicity and a zero-free-strip hypothesis of the author's library, and the absence of real zeros of zeta in (0,1).
    The analytic results are classical or weaker than classical ones; Lean zero-density estimates with stronger exponents, which imply the one-sided Bohr–Landau bound, were registered earlier by others, and earlier Lean proofs of the absence of real zeros exist.
    Nothing here proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.
    The layer's Lean files (apart from four supporting files, which the author supplied), parts of MNF.RH, the scripts and this text were produced with Claude Code, Anthropic's coding agent, under the direction of the author, who conceived the MNF framework, set the goals, operated every run and is responsible for the claims.
  ],
  keywords: ("Riemann zeta function", "zeros of the zeta function", "Lean 4", "Mathlib", "Comparator", "proof checking", "reproducibility", "Bohr–Landau theorem", "zero-density estimate", "AI-assisted formalization"),
)

// ---- Refinements on top of the template (template.typ itself is not edited). ----

// Code blocks. The template wraps an over-long code line at the left edge of the box, where a continuation cannot
// be told from a new line of the Lean source. Here every source line is its own paragraph with a hanging indent of
// four columns beyond the line's own indentation, so a continuation is visibly a continuation; at 7.5pt the box
// holds 94 columns. A block is not split across pages (the longest has six source lines). The section files keep
// the code byte for byte; only its display changes. A blank source line is kept as an empty line of the same height.
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

// Figure captions: paper.md has "Figure 1 (exploratory; proves nothing). ...", without a colon after the number;
// the last line of a justified caption stands at the left, not centred.
#set figure.caption(separator: [ ])
#show figure.caption: set align(left)

// Tables: one first-line height for every cell, so that a cell holding only code (smaller type, lower capitals)
// stands on the same baseline as the roman cells of its row.
#show table: set text(top-edge: 6pt)

// A printed reference such as "Section 4" is never hyphenated ("Sec-" / "tion 4").
#show ref: set text(hyphenate: false)

#include "typ/01-introduction.typ"
#include "typ/02-protocol.typ"
#include "typ/03-runs-mnf.typ"
#include "typ/04-bohr-landau.typ"
#include "typ/05-density-cube.typ"
#include "typ/06-numerics.typ"
#include "typ/07-reproducing.typ"
#include "typ/08-authorship.typ"
#include "typ/09-appendix-a.typ"
#include "typ/10-appendix-b.typ"

// No hyphenation inside the reference list: in the full build the style's "[Online]" was split as "[On-" / "line]"
// across a page break, and identifiers (repository names, paths, registry numbers) must never be hyphenated.
#show bibliography: set text(hyphenate: false)
// The list is set ragged right: it is full of hashes, URLs and registry numbers that cannot break, and justified
// lines around them were very loose. An entry is not split across a page break; the space between entries is
// 0.8em (the template's paragraph spacing is 0.95em), with which the 39 entries fill three pages.
#show bibliography: set par(justify: false, spacing: 0.8em)
#show bibliography: set grid.cell(breakable: false)
// The ieee style leaves a doubled space where an entry has a publisher and no place ("Springer,  2021") and
// before "Available:"; a run of spaces is set as one space.
#show bibliography: it => {
  show regex("[ ]{2,}"): [ ]
  // A page range is not split at its dash at a line end ("pp. 625–" / "635."), which the ragged setting allowed,
  // nor between "pp." and its first number ("pp." / "625–635.").
  show regex("(pp\\. )?[0-9]+–[0-9]+"): m => box(m)
  // A reference from one entry to another: refs.real.bib writes ⟦key⟧, printed as a citation of that key.
  show regex("⟦[a-z0-9-]+⟧"): m => cite(label(m.text.trim("⟦").trim("⟧")))
  // The items that md/99-references.md has in backticks (commit hashes, file paths, a project folder, a theorem
  // name) are set as inline code, as in the body of the paper. The leading word keeps the rule off the URLs.
  // A file path may break after a slash; the empty box inserts no character.
  show regex("(commit|commits|and|file|project|theorem) ([0-9a-f]{40}|[^ ]+\\.lean|[^ ]+\\.pdf|zeta23/|riemannZeta_real_neg)"): m => {
    let i = m.text.position(" ")
    let code = m.text.slice(i + 1)
    m.text.slice(0, i)
    [ ]
    if code.ends-with(".lean") or code.ends-with(".pdf") {
      let parts = code.split("/")
      for (j, part) in parts.enumerate() {
        if j + 1 < parts.len() { raw(part + "/"); box() } else { raw(part) }
      }
    } else { raw(code) }
  }
  // URLs and DOIs. Left to itself the line breaker splits a link wherever it likes: inside a host name
  // ("https://github." / "com/..."), after the scheme ("https://" / "palomar-registry.org/") and inside a commit hash.
  // Here a link that fits on one line of the list (414pt: the text width less the number column) is not split at all;
  // a longer one may break only after a slash. Nothing is inserted into the link text and the targets are unchanged.
  show link: l => context {
    if measure(l).width <= 414pt { box(l) } else {
      show regex("https?://[^/]+/|[^/]+/?"): m => box(m)
      l
    }
  }
  it
}
#bibliography("refs.real.bib", title: "References", style: "ieee")
