// Page template for the paper. Typst 0.15.

#let accent = rgb("#1a3e8c")

#let paper(
  title: none, short-title: none, author: none, date: none,
  repository: none, doi: none, abstract: none, keywords: (), body,
) = {
  set document(title: title, author: author, keywords: keywords)
  set page(
    paper: "us-letter",
    margin: (x: 1.2in, top: 1.15in, bottom: 1.15in),
    numbering: "1",
    number-align: center,
    header: context {
      if counter(page).get().first() > 1 {
        set text(size: 8.5pt, fill: luma(80))
        [#author #h(1fr) #emph(short-title)]
        v(-0.55em)
        line(length: 100%, stroke: 0.3pt + luma(160))
      }
    },
  )
  set text(font: "New Computer Modern", size: 10.5pt, lang: "en")
  set par(justify: true, leading: 0.62em, spacing: 0.95em)
  set heading(numbering: "1.1")
  show heading.where(level: 1): it => {
    v(1.3em, weak: true)
    text(size: 13pt, weight: "bold", it)
    v(0.65em, weak: true)
  }
  show heading.where(level: 2): it => {
    v(1.05em, weak: true)
    text(size: 11pt, weight: "bold", it)
    v(0.5em, weak: true)
  }
  show heading.where(level: 3): it => {
    v(0.9em, weak: true)
    text(size: 10.5pt, weight: "bold", style: "italic", it.body)
    v(0.4em, weak: true)
  }
  show link: set text(fill: accent)
  show raw.where(block: true): it => block(
    width: 100%, fill: luma(245), inset: (x: 7pt, y: 6pt), radius: 2pt, breakable: true,
    text(font: "DejaVu Sans Mono", size: 7.8pt, it),
  )
  show raw.where(block: false): it => text(font: "DejaVu Sans Mono", size: 0.84em, it)
  set table(stroke: none, inset: (x: 5pt, y: 3.6pt))
  set figure(gap: 0.9em)
  show figure.caption: it => {
    set text(size: 9pt)
    set par(justify: true)
    it
  }
  set list(indent: 0.9em, body-indent: 0.5em)
  set enum(indent: 0.9em, body-indent: 0.5em)
  set math.equation(numbering: none)

  // Title block
  align(center)[
    #block(width: 92%)[
      #set par(justify: false, leading: 0.55em)
      #text(size: 16pt, weight: "bold", title)
    ]
    #v(0.9em)
    #text(size: 11.5pt, author)
    #v(0.1em)
    #text(size: 9.5pt, fill: luma(60))[#date]
    #if repository != none [
      #v(-0.25em)
      #text(size: 9pt)[#link(repository)]
    ]
    #if doi != none [
      #v(-0.45em)
      #text(size: 9pt)[DOI: #link("https://doi.org/" + doi)[#doi]]
    ]
  ]
  v(1.1em)
  block(inset: (x: 0.45in))[
    #set text(size: 9.6pt)
    #set par(justify: true, leading: 0.58em)
    #align(center, text(weight: "bold", size: 10pt)[Abstract])
    #v(0.2em)
    #abstract
    #if keywords.len() > 0 [
      #v(0.35em)
      #text(weight: "bold")[Keywords.] #keywords.join("; ").
    ]
  ]
  v(0.9em)
  body
}

// A statement block: a labelled, lightly ruled paragraph for theorems as formalized.
#let statement(kind: "Theorem", name: none, lean: none, body) = block(
  width: 100%, inset: (left: 9pt, right: 4pt, y: 5pt), stroke: (left: 1.6pt + accent), breakable: true,
)[
  #text(weight: "bold")[#kind#if name != none [ (#name)]#if lean != none [, Lean: #raw(lean)].]
  #emph(body)
]

// Booktabs-like table helper: header row in bold with rules above and below, rule at the end.
#let rtable(columns: 2, header: (), align: left, size: 8.6pt, ..cells) = {
  set text(size: size)
  set par(justify: false, leading: 0.5em)
  table(
    columns: columns, align: align,
    table.hline(stroke: 0.7pt),
    table.header(..header.map(h => text(weight: "bold", h))),
    table.hline(stroke: 0.4pt),
    ..cells,
    table.hline(stroke: 0.7pt),
  )
}
