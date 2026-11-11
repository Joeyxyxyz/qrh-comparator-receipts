# Review of WORK/paper.md: literature and attribution

Reviewer lens: every citation in the text, every entry of the References, the statements on the
status of Comparator, and the statements on prior Lean formalizations. Checked on 2026-11-10
(local) against Crossref, zbMATH Open, the arXiv API, the GitHub API and raw files, the Palomar
data origin, lean-lang.org, and the record (REPO). The paper was not edited. Each finding gives
the location (section title and a quote), the evidence, and a replacement text.

Result: 3 major, 12 minor. No finding touches a verdict, a hash or a Lean statement.

## Major

### M1. "the most recent improvement is due to Guth and Maynard" is not true

- Location: *The zero-density estimate*: "and the most recent improvement is due to Guth and
  Maynard [@guth-maynard]".
- Evidence.
  - arXiv:2501.16779 (Tao, Trudgian, Yang; 28 January 2025, eight months after the Guth–Maynard
    preprint of 31 May 2024), abstract: "new zero density estimates for the Riemann
    zeta-function".
  - https://teorth.github.io/expdb/blueprint/zero-density-chapter.html , Table 11.1 "Current best
    upper bound on A(σ)": Guth–Maynard's 15/(3+5σ) holds the range 7/10 ≤ σ < 19/25 only; other
    ranges are held by later results (Corollary 11.31; "Chen-Debruyne-Vidas density theorem",
    "recently extended").
  - The paper's own reference [lewko-density-3917], abstract at
    https://data.palomar-registry.org/entries/PALOMAR-2026-10-11-000010-v1.json : "The maximum of
    this coefficient bound is 39/17, improving the coefficient 30/13 in the Guth–Maynard bound."
- Replacement: "Ingham's exponent $3(1-\sigma)/(2-\sigma)$ [@ingham-1940] is smaller still for
  $1/2 < \sigma < 1$. Among the later improvements is the estimate
  $N(\sigma, T) \le T^{30(1-\sigma)/13 + o(1)}$ of Guth and Maynard [@guth-maynard]; Tao, Trudgian
  and Yang [@tao-trudgian-yang] tabulate the best exponents known and add new ones. See also
  [@titchmarsh]."

### M2. The mean square on lines right of 1/2 is attributed to Hardy–Littlewood (1918)

- Location: *Architecture of the formal proof*, Step 5: "This is the $O(T)$ upper bound of the
  Hardy–Littlewood mean-value theorem [@hardy-littlewood-1918]".
- Evidence.
  - WORK/facts/literature.md, entry `hardy-littlewood-1918`: "That the σ > 1/2 mean-square theorem
    is in this paper is the record's attribution ... not read in the original."
  - arXiv:2409.06301 (Broucke and Hilberdink, "A Mean Value Theorem for general Dirichlet
    Series"), Remark (iii): the known proofs that |ζ(σ+it)|² has a mean for σ > 1/2 proceed
    "either directly as in Landau [16, p. 806] (see also Titchmarsh [22, Lemma 7.2])", where [16]
    is Landau's Handbuch of 1909; Section 5: "In 1913, Bohr and Landau [2] observed that the
    boundedness of the mean square of the Riemann zeta function ζ(s) for σ > 1/2 implies ...".
    The bound was therefore in print in 1909 and in use in 1913, before Acta Math. 41
    (Crossref: 1916; zbMATH: 1917; customary: 1918). What that paper is known for is the
    critical-line mean square, T log T.
  - The Lean source itself cites the book, not the paper:
    REPO/sources/qrh-zeta23-addon-v6/Zeta23/BL/BohrLandauClosure.lean:1164 "(Titchmarsh §7.2)".
- Replacement: "This is the $O(T)$ upper bound in the classical mean-value theorem for
  $\lvert\zeta(\sigma+it)\rvert^2$ on the lines $\sigma > 1/2$ (the source cites Section 7.2 of
  [@titchmarsh]); the asymptotic formula is not proved." Then delete the entry
  [hardy-littlewood-1918] from the References (it would be uncited).

### M3. Ingham 1940: the page range in the References is wrong

- Location: References, [ingham-1940]: "The Quarterly Journal of Mathematics (Oxford Series), 11
  (1940), 201–202."
- Evidence.
  - zbMATH Open API, Zbl 0025.02704: "Q. J. Math., Oxf. Ser. 11, 291-292 (1940)"; JFM 66.0341.02:
    "Quart. J. Math. (Oxford Ser.) 11, 291-292 (1940)".
  - arXiv:2310.04544 (Pintz), reference [Ing1940]: "Quart. J. Math. Oxford Ser. 11 (1940),
    291–292."
  - Crossref itself: its listing of the 1940 volume (api.crossref.org/journals/0033-5606/works,
    1940) has Kober, "On fractional integrals and derivatives", at pages 193-211, which contains
    201-202, and no article between Cartwright 277-290 and Erdélyi 293-303. The "201-202" of the
    Crossref record for DOI 10.1093/qmath/os-11.1.201 is a metadata error; WORK/facts/literature.md
    section 6 item 2 took it for the correct value.
- Replacement: "[ingham-1940] A. E. Ingham. On the estimation of N(σ, T). The Quarterly Journal of
  Mathematics (Oxford Series), 11 (1940), 291–292. DOI 10.1093/qmath/os-11.1.201." (The DOI is
  the publisher's and resolves; only the pages change.)

## Minor

### m1. Which Bohr–Landau paper, and which year, has N(σ,T) = O(T)

- Location: *The Bohr–Landau theorem as formalized*: "Bohr and Landau proved in 1914 that
  $N(\sigma,T)=O(T)$ for each fixed $\sigma>1/2$ [@bohr-landau-1914]".
- Evidence. Not read in the original (literature.md, `bohr-landau-1914`: "The statement was not
  read in the original"). The sources disagree: the Jahrbuch review of the two 1914 notes (zbMATH
  JFM 45.0716.03) says the first proves O(T) for Dirichlet series convergent in σ > 0 and "In der
  zweiten Abhandlung wird O(T) durch das bessere o(T) ersetzt"; arXiv:2101.12263 (Kadiri, Lumley,
  Ng): "In 1913 Bohr and Landau [2] showed that N(σ,T) = O(T/(σ − 1/2))", with [2] = Math. Ann. 74
  (1913), 3–30; arXiv:2409.06301 also dates the O(T) bound to 1913; arXiv:2310.04544 credits the
  Comptes Rendus note with N(σ,T) = o(N(T)).
- Replacement: "The theorem goes back to Bohr and Landau, who proved that $N(\sigma,T)=O(T)$ for
  each fixed $\sigma>1/2$ and, in two notes of 1914, sharpened this to $o(T)$
  [@bohr-landau-1914; @bohr-landau-1914b]; the originals were not consulted for this paper. The
  source files cite Section 9.15 of [@titchmarsh] for the classical proof." Add to the References
  the entry `bohr-landau-1914b` of literature.md (Rend. Circ. Mat. Palermo 37 (1914), 269–272).

### m2. Status of Comparator: the tool was already archived when every run was made; "Lake 4.35.0"

- Location: *Comparator and what an acceptance means*: "The standalone tool is now archived; Lake
  4.35.0 provides `lake comparator` and `lake check` [@lean-4-35]." Also *What would strengthen
  the work*: "re-judging it with the `lake comparator` of Lake 4.35.0 [@lean-4-35]".
- Evidence. https://github.com/leanprover/comparator : banner "This repository was archived by
  the owner on Oct 20, 2026"; last commit `865edc14`, "doc: migration notice",
  2026-10-14T08:49:09Z (GitHub API); README: "Users are advised to migrate their validations
  setups to these tools as they are the only ones guaranteed to receive further security and
  performance improvements." Run 1 started 2026-10-27T17:43:45Z (paper, Appendix A), so all eleven
  runs postdate both the notice and the archival; "now archived" reads as if the archival came
  after the runs. The release notes (https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
  give no version "Lake 4.35.0"; they say of Lean 4.35.0 "This release brings all of this into
  Lake" and call `lake comparator` "a frontend to comparator".
- Replacement (first location): "The standalone repository was archived on 2026-10-20, a week
  before run 1, and since 2026-10-14 its README has advised migrating to `lake comparator` and
  `lake check`, which ship with Lean 4.35.0 [@lean-4-35]. The runs use the standalone tags v4.34.0
  and v4.33.0-rc2 because the two artifacts pin Lean 4.34.1 and 4.33.0-rc2, which are older than
  that release." Second location: "re-judging it with the `lake comparator` that ships with Lean
  4.35.0 [@lean-4-35]". Add to *Limitations*, Checks: "All eleven runs used the standalone
  Comparator after its repository had been archived; its README says that only the Lake commands
  are guaranteed further security and performance fixes."

### m3. Provenance of the two external theorems as their own sources state it

- Location: *The artifacts and what was added*: "Anthropic's formalization of the theorem of
  Alpöge and Furman [@alpoge-furman] that more than two thirds of the zeros".
- Evidence. arXiv:2608.13637v2, comments field: "Proof discovered autonomously by Claude
  (Anthropic); verified and communicated by the listed authors. See §1 for provenance. Lean
  formalization available". zeta23 README at the pin: "all Lean code in this repository ... was
  written by Claude (Anthropic)". openai/math README at the pin: "mathematical manuscripts and
  supporting proof artifacts produced by an internal OpenAI model". The paper is explicit about AI
  provenance for its own files and silent about it for the two artifacts.
- Replacement: add after that sentence: "The arXiv listing of [@alpoge-furman] states that the
  proof was discovered autonomously by Claude (Anthropic) and verified and communicated by the
  listed authors; OpenAI's repository states that its manuscripts and proof artifacts were
  produced by an internal OpenAI model."

### m4. The nearest earlier Lean work on zero density by Jensen's formula is not cited

- Location: *The Bohr–Landau theorem as formalized*: "The author is not aware of a prior Lean
  statement of the Bohr–Landau theorem in its two-sided form".
- Evidence. https://data.palomar-registry.org/entries/PALOMAR-2026-09-23-000001-v1.json (Andrew
  Fiori, registered 2026-09-23T01:19:36Z, Lean v4.34.0-rc1), abstract: zero-density bounds "proved
  by two different mechanisms -- Jensen's formula and Littlewood's lemma"; "a definite fraction of
  the window's zeros ... have real part in the middle band [alpha, 1-alpha], away from both edges
  of the critical strip"; "The results are conditional and their hypotheses are in the
  signature"; it also proves the reflection ρ → 1 − conj(ρ) as a multiplicity-preserving
  involution. arXiv:2609.22624 (18 September 2026). The key `fiori-2026` is in literature.md and
  unused. The hedged sentence stays supportable (short windows, a positive proportion, conditional),
  but this is the closest earlier Lean statement of a two-sided kind and uses the same method.
- Replacement: add after the sentence on Lewko's entry: "Earlier still, Fiori registered explicit
  zero-density bounds for short windows $(t-h, t+h]$ (Palomar entry of 2026-09-23, formalizing
  [@fiori-2026]), proved by Jensen's formula and by Littlewood's lemma, with a two-sided corollary:
  a positive proportion of the zeros in such a window have $\alpha \le \beta \le 1-\alpha$. Those
  results take explicit bounds and numerical certificates as hypotheses and are not the
  Bohr–Landau theorem." Add the entry `fiori-2026` to the References.

### m5. Improvements of the 7/8 half-plane that the record lists are not mentioned

- Location: *The MNF.RH library in standard terms*: "because OpenAI's theorem leaves the line
  $\operatorname{Re}s=7/8$ open."
- Evidence. REPO/DEPOSIT_MAP.md section 8: "Zero-free half-planes left of 7/8, read on 2026-10-28
  (none run here ...)": Liu, arXiv:2610.12234, "B_new ... ≈ 0.874957"; the tracker's frontier
  "0.873985". arXiv listing of 2610.12234 (v1 8 October 2026, v2 12 October 2026): "we slightly
  improve the bound 7/8 = 0.875 to B_new = ... 0.874957019420098946...". A reader of "The second
  threshold is exact" can take 3/8 for the current frontier.
- Replacement: append: "Exact, that is, relative to that theorem: smaller boundaries, obtained by
  refining the parameters of OpenAI's argument, have since been announced (about $0.874957$ by
  Liu [@liu-2026]); the register lists them as read and not run here, and none is used in this
  work." Add the entry `liu-2026` to the References.

### m6. Lewko's entry of 2026-10-11: say "according to the registry", and note its definition holes

- Location: *The Bohr–Landau theorem as formalized*: "the content of the theorem was available in
  Lean earlier: a zero-density estimate registered by Lewko".
- Evidence. `lean/comparator.json` at commit `ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0` of
  mrklwk/zeta-density-39-over-17-lean lists under "definition_names"
  `GuthMaynardStatement.densityCoefficient`, `.actualZeroBound`, `.dirichletPolynomial`. By
  Comparator's README these are definition holes ("the name, type, universe levels and safety
  level match"), so the registry's acceptance does not by itself compare the bodies that carry the
  exponent and the zero count. `lean/Challenge.lean` and `lean/Solution.lean` at that commit were
  read for this review: the three definitions are textually identical in both. The paper has the
  caveat "(that its proof was accepted is the registry's report, not re-checked here)" in the
  density section but states availability as a fact here.
- Replacement: "and, according to the registry, the content of the theorem was available in Lean
  earlier: a zero-density estimate registered by Lewko ...". In *The zero-density estimate* extend
  the parenthesis: "(that its proof was accepted is the registry's report, not re-checked here;
  its Comparator configuration lists the three definitions the statements rest on as holes, and
  the challenge and solution files at the registered commit define them identically)".

### m7. Definition holes: the README also compares the safety level

- Location: *Comparator and what an acceptance means*: "A definition listed as a hole is compared
  by name, type and universe levels only."
- Evidence. Comparator README at tags v4.34.0 and v4.33.0-rc2: "The name, type, universe levels
  and safety levels of all definition holes match".
- Replacement: "A definition listed as a hole is compared by name, type, universe levels and
  safety level only, not by body."

### m8. A provisional "first" in the record's notes is not retracted in the Errata

- Location: *Errata* (no entry); the paper points readers to `notes/` in *Availability*.
- Evidence. REPO/notes/density-field-2026-11-03/strip/STRIP_SCOPE_REPORTS_2026-11-04.md:331 "It
  would be, to my knowledge, the first kernel-checked zero-density estimate with a power saving at
  any pin, subject to the caveat ..."; strip/STRIP_PLAN.md:15 "the first kernel-checked
  zero-density estimate with a power saving on this trust base (novelty subject to Mark Lewko's
  two unverified Palomar entries ...)". literature.md section 6 item 10: "the claim 'first' does
  not hold".
- Replacement: add to *Errata*: "*A provisional priority claim in the notes.* The working notes
  of run 10 (`strip/STRIP_PLAN.md`, `strip/STRIP_SCOPE_REPORTS_2026-11-04.md`) call its target
  'the first kernel-checked zero-density estimate with a power saving', subject to reading Lewko's
  Palomar entries. Those entries have since been read (see *The zero-density estimate*); the
  description does not hold, and this paper makes no such claim."

### m9. The explicit δ-dependence is not compared with the classical one

- Location: *The displacement of the zeros from the line*: "there are $A, B \ge 0$ with
  $N_{\mathrm{off}}(\delta, T) \le (A\delta^{-5/2} + B)\,T$".
- Evidence. zbMATH JFM 50.0230.02, review of [littlewood-1924], last displayed line: N(σ,T) =
  O( T/(σ−1/2) · log 1/(σ−1/2) ); arXiv:2101.12263: "N(σ,T) = O(T/(σ − 1/2))" (attributed there to
  Bohr and Landau, 1913). The paper says "far weaker" for D(T) but not for this bound (framing
  rule 3).
- Replacement: add: "The classical dependence on $\delta$ is of order $\delta^{-1}$, up to a
  logarithm [@littlewood-1924]."

### m10. Source of the tabulated ordinates

- Location: *A numerical illustration*: "eleven ordinates agree with tabulated values, quoted from
  memory".
- Evidence. REPO/NOTICE: "the tabulated zero ordinates it compares against are public (Odlyzko /
  LMFDB tables)"; RESULTS.md (via WORK/facts/numerics.md F2.9): "values as recalled from the
  LMFDB/Odlyzko tables".
- Replacement: "eleven ordinates agree, to within $3.3\times 10^{-10}$, with values recalled from
  the public tables of Odlyzko and the LMFDB (typed from memory, not read from the tables)".

### m11. The operator hypotheses have a standard name

- Location: *What is open and what was withdrawn*: "two realization hypotheses, namely a symmetric
  operator, or a Schrödinger operator with a confining potential".
- Evidence. REPO/DEPOSIT_MAP.md section 4: "The operator realization (the corpus's `HPContext`,
  Hilbert–Pólya)" and "the Berry–Keating / Connes programmes aim at exactly this and none is a
  theorem".
- Replacement: "two realization hypotheses of Hilbert–Pólya type, namely a symmetric operator, or
  a Schrödinger operator with a confining potential, having every $(\rho-1/2)/i$ as an eigenvalue".

### m12. Earlier Lean proofs of the real-segment fact: pin one reference, add the usual caveat

- Location: References, [hubbard-goldbach-lean]: "GitHub repository sthubbar/goldbach-lean,
  default branch as read on 2026-11-10."; *No real zeros in the interval (0,1)*: "goldbach-lean
  [@hubbard-goldbach-lean] has it as well".
- Evidence. GitHub API: the file's only commit is `30ab3dd5fbb90ed832a592a0a63424ab858a94a0`
  (2026-10-21T18:17:37Z, author "Steve Hubbard"); the repository is still being pushed
  (pushed_at 2026-11-10T23:59:15Z), so a link to `main` can move. Repository description:
  "AI-written Lean 4 formalizations of Goldbach-relatedresults, for the Palomar registry"; file
  header: "AI wrote this file." Both earlier proofs were read, not built (literature.md 5.3).
- Replacement (reference): "[hubbard-goldbach-lean] Steve Hubbard. goldbach-lean (described by
  its repository as AI-written), file
  `entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean` (theorem
  `riemannZeta_real_neg`). GitHub repository sthubbar/goldbach-lean, commit
  `30ab3dd5fbb90ed832a592a0a63424ab858a94a0` (2026-10-21).
  https://github.com/sthubbar/goldbach-lean/blob/30ab3dd5fbb90ed832a592a0a63424ab858a94a0/entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean"
  Text: "... has it as well (both files were read for this paper; neither was built or re-checked
  here)."

## Checked and found correct (no change needed)

- All 37 citation keys used are defined in literature.md and in the References; no reference is
  uncited; the list is in alphabetical order of keys.
- Crossref: [guth-maynard] (Ann. of Math. 203 (2026), no. 2, 623–675), [lean4], [littlewood-1924],
  [mathlib], [montgomery-1973], [montgomery-vaughan-1974], [odlyzko-1987], [platt-trudgian-2021],
  [levinson-montgomery-1974], [von-mangoldt-1905], [speiser-1934] (Crossref dates the issue
  December 1935; 1934 is zbMATH's and the customary year).
- zbMATH: [bohr-landau-1914] (C. R. 158, 106–110), [carlson-1920] (Ark. 15, No. 20, 28 p.; the
  review confirms N(1/2+δ,T) = O(T^{1−4δ²+ε})), [selberg-1946], [littlewood-1924] (the review
  confirms the O(T log log T) bound for the integral of N(σ,T)).
- arXiv API: [alpoge-furman] (title, authors, v2 of 2026-08-19; abstract "at least two thirds
  ... counted with multiplicity"), [aristotle] (23 authors, first three as printed, v2 of
  2025-10-10), [tao-trudgian-yang], Guth–Maynard preprint, Platt–Trudgian preprint.
- Selberg's bound and its attribution to Theorem 1 of the 1946 paper: arXiv:1910.08274,
  introduction. Ingham's exponent: the same and the ANTEDB chapter (Theorem 11.14).
- GitHub API: openai/math `adc7f124` (2026-10-06, "Initial commit"; challenge file re-hashed to
  065f8c9a...); anthropics/formal-math `16a5ce41` (2026-10-27); Comparator tags v4.34.0 =
  d03acab154d2, v4.33.0-rc2 = 75c730e9b6ef, archived = true; lean4export pins and dates; landrun
  pin, author "Armin ranjbar"; robsimmons/nanoda_lib is a fork of ammkrn/nanoda_lib and holds the
  pinned commit; AxiomMath/ZetaZerosV2 `1d7edeb4` (2026-10-03), file RealSegment.lean, proof from
  `Zeta0EqZeta (N := 1)`; PrimeNumberTheoremAnd CITATION.cff (organizers, 2024-01-09).
- zeta23 README at the pin: title, 17 statements (Theorems A–E, D with the constant 0.67250...),
  files under `Zeta23/FromPNTPlus/` ported from PrimeNumberTheoremAnd, CI and AUDIT.md report
  Comparator runs ("Your solution is okay!").
- Comparator README: "originally developed by Lean FRO"; the systemd-run property
  RestrictAddressFamilies=~AF_UNIX; steps of the check; Lean 4.35.0 release notes: date
  2026-10-12, section "Checking Projects with lake check and lake comparator".
- Palomar: the four Lewko entries (titles, registration dates 2026-10-07 to 2026-10-21, Lean
  v4.35.0-rc2, one-sided counts); the exponent comparison with run 10 holds on all of (1/2, 1].
- Quotes attributed to the record (register, NOTICE, protocol, reports, Lean sources) were found
  verbatim in the files named.
- Searches for an earlier Lean Bohr–Landau statement or displacement bound (Palomar data API,
  web search) found none; this is weak evidence, as the paper says.
