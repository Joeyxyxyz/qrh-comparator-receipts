# Bibliography sheet (WORK/facts/literature.md)

Compiled 2026-11-10 (local date; 2026-11-11 UTC). Every entry below was checked against a web page
or API response opened on that day; the URL checked is given. Status is VERIFIED (bibliographic
data confirmed at the URL), PARTLY VERIFIED (what is and is not confirmed is stated) or UNVERIFIED.
"Cited for" says what the paper may use the entry for; where the attribution of a *result* to a
paper was not read in the original, that is said separately from the bibliographic status.

Sources used: arXiv listing pages; the Crossref REST API (api.crossref.org/works/DOI); the zbMATH
Open API (api.zbmath.org/v1/document/_search); the GitHub web pages and REST API; the Palomar
registry's public data origin (data.palomar-registry.org); lean-lang.org; anthropic.com. The zbMATH
web pages and openai.com returned HTTP 403 to the fetch tool; zbMATH was read through its API
instead, openai.com could not be read at all.

Citation keys are the strings in backticks at the head of each entry. Use them as `[@key]`.

---

## 1. The two artifacts under test and what accompanies them

### `openai-math`
OpenAI. *openai/math* (GitHub repository of mathematical manuscripts and Lean proof artifacts
produced by an internal OpenAI model). Commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
("Initial commit", committed 2026-10-06T21:58:50Z; the repository has one commit at this pin).
License Apache-2.0. https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
- Cited for: the artifact under test in run 1; the Lean theorem
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (listed in `lean/formalization.yaml` with
  Comparator configuration `ComparatorChallenges/QuasiRiemannHypothesis.json`, file
  `OAI/NumberTheory/DirichletL/Nonvanishing.lean`).
- Status: VERIFIED (GitHub API: commit, date, license; `lean/formalization.yaml` lines 1434-1436
  at the pin). The challenge file `lean/ComparatorChallenges/QuasiRiemannHypothesis.lean` fetched
  from the GitHub API at this commit hashes to sha256
  `065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5`, equal to the record's pin.
- Note on "checks their authors report": the repository ships Comparator configurations and a
  short instruction file (`lean/ComparatorChallenges/README.md`: install comparator, landrun and
  lean4export, then `lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json`), and
  the root README points to it for further checking instructions. In the files read (root
  README, `lean/README.md`, `lean/ComparatorChallenges/README.md`, `lean/docs/003.md`) there is no
  sentence that reports the outcome of a Comparator run made by OpenAI. See Open questions.

### `openai-qrh`
OpenAI. "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8". OpenAI Math Release
preprint, dated 30 September 2026. File
`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf` in [@openai-math].
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf
- Cited for: the manuscript that accompanies the 7/8 theorem (family 003, "The quasi-Riemann
  hypothesis", in the repository's `CONTENTS.md`; `lean/docs/003.md` maps it to the four
  Comparator files QuasiRiemannHypothesis, DirichletSevenEighths, HeckeSevenEighths, SiegelZeros).
- Status: VERIFIED for title, author line ("OpenAI"), date and location (the directory's
  `README.md` at the pin, which also carries the BibTeX block with key
  `OAI:The-Quasi-Riemann-Hypothesis-September-30-2026`, `author = {{OpenAI}}`, `year = {2026}`).
  The PDF itself (1,588,969 bytes) was not opened; no page count, no arXiv identifier and no DOI
  were found. The root README says the zero-free-region work was an exception to the repository's
  fixed procedure and that the write-up of the companion Re(s) > 11/12 result was edited by humans
  for readability (paraphrase of README line 43).

### `openai-announcement`
OpenAI. "Sharing AI progress in mathematics". Web post, reported date 6 October 2026.
https://openai.com/index/sharing-ai-progress-in-mathematics/
- Cited for: the public announcement of the repository (optional).
- Status: UNVERIFIED. The URL and title appear in web-search results and the search summary
  dates the post 2026-10-06, but the page returned HTTP 403 to the fetch tool, so the title, date
  and contents were not read on the page itself. Do not quote it.

### `anthropic-formal-math`
Anthropic. *anthropics/formal-math* (GitHub repository of machine-checked Lean 4 formalizations
published by Anthropic; project `zeta23/`). Commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`
(committed 2026-10-27T03:07:21Z; the commit itself adds the unrelated `eth/` project). License
Apache-2.0. https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5
- Cited for: the artifact under test in run 2 and the base tree of runs 6 to 11. The zeta23 README
  at the pin is titled "Zeta23 — a Lean 4 formalization of 'More than two thirds of the zeta zeros
  are simple and on the critical line'"; Lean `v4.33.0-rc2`, Mathlib
  `51e6992efd06126df61a496bebf8f49482a4e129`; `Challenge.lean` with 17 statements; Comparator
  configuration `comparator.json`; files under `Zeta23/FromPNTPlus/` ported from
  PrimeNumberTheoremAnd (Apache-2.0).
- Status: VERIFIED (GitHub API for commit, date, license; README contents as summarized by the
  fetch tool, not copied verbatim). Per that summary the README states that all Lean code was
  written by Claude (Anthropic), that Levent Alpöge and Ralph Furman wrote the mathematics,
  directed the formalization and reviewed its outputs, and that Eric Easley orchestrated the Lean
  work; and that the repository's CI runs the Palomar registry's Comparator acceptance check
  (Comparator, lean4export, nanoda, landrun). The README gives no Palomar registry identifier for
  zeta23 and no "how to cite" block. Keyword searches of the Palomar data API ("two thirds",
  "Alpöge", "critical line") returned no zeta23 entry; this was not pursued further.
- The URL `github.com/anthropics/zeta-23-lean` (used in Anthropic's post and in the paper's v1)
  is listed by a search engine under the title "anthropics/formal-math"; not checked further.

### `alpoge-furman`
Levent Alpöge and Ralph Furman. "More than two thirds of the zeta zeros are simple and on the
critical line". arXiv:2608.13637 [math.NT], v1 13 August 2026, v2 19 August 2026 (current).
MSC 11M06, 11M26, 15A42. DOI 10.48550/arXiv.2608.13637. https://arxiv.org/abs/2608.13637
- Cited for: the theorem zeta23 formalizes (at least two thirds of the nontrivial zeros, counted
  with multiplicity, are simple and on the critical line; at least five sixths are distinct; the
  Montgomery–Taylor constants 0.6725 and 0.8362; extension to primitive Dirichlet L-functions).
- Status: VERIFIED (arXiv listing, v1 and v2). The arXiv comments field says (paraphrase) that
  the proof was discovered autonomously by Claude (Anthropic) and verified and communicated by the
  listed authors, with a Lean formalization available; v1 is listed as 17 pages, v2 as 21 pages.
  No journal reference.
- DISAGREEMENT WITH THE RECORD: `README.md` of the record quotes the title as "More than two
  thirds of the zeros of the Riemann zeta function are simple and on the critical line". The
  arXiv listing (both versions) and the zeta23 README have "…of the zeta zeros…". The longer
  wording is the *description* in the root README of anthropics/formal-math and the title a search
  engine shows for the arXiv HTML rendering of v1 and for the PDF hosted by Anthropic. Use the
  arXiv listing title. Spelling of the first author on arXiv: "Alpöge" (the record's
  `zenodo-metadata.json` has "Alpoege").

### `anthropic-announcement`
Anthropic. "Claude has improved on a longstanding lower bound for the fraction of zeros of the
Riemann zeta function that satisfy the Riemann hypothesis". Web post, 10 August 2026, updated
13 August 2026. https://www.anthropic.com/research/riemann-zeta
- Cited for: the announcement accompanying zeta23 (optional); it states that the Lean proof
  passes Comparator, which supports "a check its authors report".
- Status: VERIFIED for URL, title and dates as read by the fetch tool (the tool reported the title
  in two parts; the second part "that satisfy the Riemann hypothesis" should be re-read on the
  page before the title is printed in full).

---

## 2. The checker and its components

### `comparator`
Lean FRO. *Comparator* (a judge for Lean proofs: challenge file against solution file). GitHub repository
leanprover/comparator, Apache-2.0. Pins used by the record: tag `v4.34.0` = commit
`d03acab154d269c06e60e4de7e4cc85deebff94b` (2026-09-14) and tag `v4.33.0-rc2` = commit
`75c730e9b6ef5c2c3b334fad7c3d51fe20624c88` (2026-08-03). https://github.com/leanprover/comparator
- Cited for: the proof judge of all eleven runs; its trust assumptions (challenge and build files
  trusted, solution never compiled before, landrun not escapable, kernel correct, user not
  privileged), as listed in its README.
- Status: VERIFIED (GitHub API: both tags resolve to the pinned commits, dates as given; README).
- Present status: VERIFIED. The repository is archived (GitHub API `archived=true`; the page
  banner reads "archived by the owner on Oct 20, 2026"). Its last commit is `865edc14`,
  a documentation commit adding the migration notice, 2026-10-14. The README opens with a deprecation section saying the
  project was merged into core as of Lean release v4.35.0 in the form of `lake comparator` and
  `lake check`, and advising migration. The last tag is `v4.35.0` (`e3dcf308`, 2026-10-12). The
  README credits development to the Lean FRO with feedback from the AIMO team.
- NOTE: no file of the record (REPO) contains the archival date or the words "lake comparator"
  (grep of REPO on 2026-11-10); the statement in the task brief is confirmed on the web, not in
  the record. Both pins predate the archival; the runs used the standalone tool.

### `lean-4-35`
Lean FRO. Lean 4.35.0 release notes, section "Checking Projects with lake check and lake
comparator". Released 2026-10-12.
https://lean-lang.org/doc/reference/latest/releases/v4.35.0/ ;
https://github.com/leanprover/lean4/releases/tag/v4.35.0 (published 2026-10-12T18:13:12Z)
- Cited for: the successor of the standalone Comparator.
- Status: VERIFIED for the release date and the existence of the section. Per the fetch tool's
  reading, the release notes describe `lake comparator` as a frontend to comparator, whereas
  Comparator's README says the project was merged into core; the two wordings differ and
  the paper should say only that Lake 4.35.0 provides `lake comparator` and `lake check`.

### `lean4export`
Lean FRO. *lean4export* (plain-text export of Lean 4 declarations). GitHub repository
leanprover/lean4export, Apache-2.0. Pins: `076e8e57707e813375e8f9da8bf989799ace9680`
(2026-09-14, toolchain bump to v4.34.0) and `9fb131bb100eb32ccf6836f14e4f8328d13b6792`
(2026-08-03, toolchain bump to v4.33.0-rc2). https://github.com/leanprover/lean4export
- Cited for: the exporter whose output the kernels replay.
- Status: VERIFIED (GitHub API).

### `nanoda`
ammkrn (GitHub user name; no personal name on the page). *nanoda_lib* (a library
implementing type inference and checking for Lean), an external type
checker for Lean 4 export files, built with cargo. Apache-2.0. https://github.com/ammkrn/nanoda_lib
The record pins the fork https://github.com/robsimmons/nanoda_lib at commit
`68d5ca9db226849b41a6fff59d796ff19d0a8840` (commit author "ammkrn", 2026-03-04).
- Cited for: the second kernel of runs 2 and 6 to 11.
- Status: VERIFIED (GitHub API: robsimmons/nanoda_lib is a fork of ammkrn/nanoda_lib; the pinned
  commit exists there). Comparator's README links the ammkrn repository. The author's personal
  name is not on the pages read: cite by repository.

### `landrun`
Armin Ranjbar (GitHub: Zouuup). *landrun* (runs a Linux process in an unprivileged sandbox using
Landlock). MIT license. Pin `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (2026-07-23).
https://github.com/zouuup/landrun
- Cited for: the sandbox Comparator requires.
- Status: VERIFIED (GitHub API: license, pinned commit with author name "Armin ranjbar"). The
  version label "0.1.18" is the record's (PINS.env) and was not checked.

### `lean4`
Leonardo de Moura and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language".
In: *Automated Deduction – CADE 28*, Lecture Notes in Computer Science 12699, Springer, 2021,
pp. 625–635. DOI 10.1007/978-3-030-79876-5_37.
- Cited for: Lean 4.
- Status: VERIFIED (Crossref: authors, title, book title, pages, year 2021). The LNCS volume
  number 12699 is from memory and is not in the Crossref record read: check before printing or
  omit it.

### `mathlib`
The mathlib Community. "The Lean Mathematical Library". In: *Proceedings of the 9th ACM SIGPLAN
International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367–381.
DOI 10.1145/3372885.3373824. Repository: https://github.com/leanprover-community/mathlib4
- Cited for: Mathlib. Pins of the record: `d13f23b723b8a846827a245b89c10fc7d3f11612` (OpenAI
  tree) and `51e6992efd06126df61a496bebf8f49482a4e129` (zeta23 tree).
- Status: VERIFIED (Crossref). The paper describes the Lean 3 library; it is the customary
  citation for Mathlib.

### `loeffler-stoll`
David Loeffler and Michael Stoll. "Formalizing zeta and L-functions in Lean". *Annals of
Formalized Mathematics* 1 (2025), 43–56. DOI 10.46298/afm.15328. arXiv:2503.00959.
- Cited for: Mathlib's `riemannZeta`, its functional equation, and `riemannZeta_ne_zero_of_one_le_re`
  (non-vanishing for Re s ≥ 1) (optional).
- Status: VERIFIED (zbMATH Open API, Zbl 1578.68295).

### `pnt-plus`
Alex Kontorovich and Terence Tao (organizers). *Prime Number Theorem and More*
(PrimeNumberTheoremAnd), collaborative Lean project launched 2024-01-09. Apache-2.0.
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Cited for: the source of the files zeta23 ports under `Zeta23/FromPNTPlus/` (the approximate
  formula `Zeta0EqZeta`, zeta bounds), on which the layer of runs 7 to 11 also relies.
- Status: VERIFIED (the repository's `CITATION.cff`: title, authors, release date 2024-01-09).

### `palomar`
Palomar Registry. A public registry of Lean-verified results (statement, pinned source, kernel
replay, automated review). https://palomar-registry.org/ ; data origin
https://data.palomar-registry.org/ ; https://github.com/PalomarRegistry
- Cited for: where the prior Lean zero-density formalizations are registered (section 5).
- Status: VERIFIED that the site and data API exist and serve the entries quoted in section 5.
  The pages read do not name an operator.

### `claude-code`
Anthropic. *Claude Code* (an agentic coding tool that reads a codebase, edits files and runs
commands). Documentation: https://code.claude.com/docs/en/overview
- Cited for: the tool with which the Lean files of runs 7 to 11, the scripts and the documents
  were produced under the author's direction.
- Status: VERIFIED (page read 2026-11-10; docs.claude.com/en/docs/claude-code/overview redirects
  there). No version number is recorded in the record: do not state one.

### `aristotle`
Tudor Achim, Alex Best, Alberto Bietti, et al. (23 authors). "Aristotle: IMO-level Automated
Theorem Proving". arXiv:2510.01346 [cs.AI], v1 1 October 2025, v2 10 October 2025.
- Cited for: Harmonic's prover, named in the record's NOTICE as co-author of
  `SturmLiouville/SimpleEigenvalues.lean` (only if the paper discusses that file).
- Status: VERIFIED (arXiv listing). That this system is the "Aristotle (Harmonic)" of the NOTICE
  is the natural reading and is not stated in the record.

---

## 3. Classical literature on the zeros of zeta

### `titchmarsh`
E. C. Titchmarsh. *The Theory of the Riemann Zeta-function*. Second edition, revised by
D. R. Heath-Brown. Oxford Science Publications. Oxford: Clarendon Press, 1986. x + 412 pp.
- Cited for: the standard reference (Chapter IV, approximate formulae, Theorem 4.11 and Lemmas
  4.2/4.3; Chapter VII, mean values; Chapter IX, N(T), Littlewood's lemma §9.9, density theorems
  §9.15 ff.). The section and theorem numbers are those used in the record's notes; they were not
  checked against the book (the record's own scoping report says the numbering in §9.15–9.17 was
  "not checked").
- Status: VERIFIED bibliographically (zbMATH Open API, Zbl 0601.10026). ISBN not confirmed.

### `bohr-landau-1914`
Harald Bohr and Edmund Landau. "Sur les zéros de la fonction ζ(s) de Riemann". *Comptes Rendus
de l'Académie des Sciences (Paris)* 158 (1914), 106–110.
- Cited for: the Bohr–Landau theorem: for fixed σ > 1/2, N(σ, T) = O(T), so all but a vanishing
  proportion of the zeros lie in any strip |Re s − 1/2| < δ.
- Status: VERIFIED bibliographically (zbMATH Open API, JFM 45.0716.02). The statement was not
  read in the original; the attribution is the standard one (and the record's).

### `bohr-landau-1914b`
Harald Bohr and Edmund Landau. "Ein Satz über Dirichletsche Reihen mit Anwendung auf die
ζ-Funktion und die L-Funktionen". *Rendiconti del Circolo Matematico di Palermo* 37 (1914),
269–272.
- Cited for: the companion paper with the general theorem on Dirichlet series (optional).
- Status: VERIFIED bibliographically (zbMATH Open API, JFM 45.0716.03).

### `carlson-1920`
Fritz Carlson. "Über die Nullstellen der Dirichletschen Reihen und der Riemannschen ζ-Funktion".
*Arkiv för Matematik, Astronomi och Fysik* 15, No. 20 (1920/21), 28 pp.
- Cited for: Carlson's zero-density theorem N(σ, T) ≪ T^{4σ(1−σ)+ε}, the first power saving.
- Status: VERIFIED bibliographically (zbMATH Open API, JFM 47.0282.03 and 48.0337.02).
  YEAR: zbMATH gives 1921; Littlewood's 1924 paper cites it as 1920 (footnote on the Cambridge
  Core page), and the Tao–Trudgian–Yang database cites "Carlson (1921)". "Carlson (1920)" in the
  text with "1920/21" in the reference is defensible. The first name "Fritz" is from memory;
  zbMATH has "Carlson, F.": print "F. Carlson". The exponent 4σ(1−σ) is confirmed by
  [@tao-trudgian-yang] (A(σ) ≤ 4σ) and by the title and abstract of [@chourasiya-2024].

### `littlewood-1924`
J. E. Littlewood. "On the zeros of the Riemann zeta-function". *Proceedings of the Cambridge
Philosophical Society* 22 (1924), no. 3, 295–318. DOI 10.1017/S0305004100014225.
- Cited for: the bound Σ_{0<γ≤T, β>1/2} (β − 1/2) = O(T log log T) for the displacement of the
  zeros from the line (equivalently a bound for ∫ N(σ, T) dσ), obtained from Littlewood's lemma
  and the mean square of ζ.
- Status: VERIFIED bibliographically (Crossref; Cambridge Core page, issue date 20 September
  1924). ATTRIBUTION OF THE RESULT: not read in the original (paywalled; the free extract only
  defines N(T) and N(σ, T) and cites Bohr–Landau–Littlewood 1913, Carlson 1920 and Cramér 1919).
  The O(T log log T) statement is taken from the record's notes
  (`notes/density-field-2026-11-03/strip/STRIP_SCOPE_REPORTS_2026-11-04.md`) and agrees with the
  standard account; a 2018 arXiv paper (1811.05277) proves a lemma of the same shape by the same
  method. If the paper wants a page-exact citation, cite it through [@titchmarsh], Chapter IX.

### `selberg-1942`
Atle Selberg. "On the zeros of Riemann's zeta-function". *Skr. Norske Vid.-Akad. Oslo I*
1942, No. 10, 59 pp.
- Cited for: a positive proportion of the zeros lie on the critical line.
- Status: PARTLY VERIFIED. zbMATH (Zbl 0028.11101) lists "Skr. Norske Vid.-Akad., Oslo 10, 1–59
  (1943)"; the customary citation is "1942, no. 10" (from memory). Title, author, series, number
  and length are confirmed; the year printed should be "1942" with the series number, or follow
  zbMATH (1943). That this is the positive-proportion paper is standard and was not read in the
  original.

### `selberg-1946`
Atle Selberg. "Contributions to the theory of the Riemann zeta-function". *Arch. Math.
Naturvid.* 48 (1946), no. 5, 89–155.
- Cited for: N(σ, T) ≪ T^{1 − (σ − 1/2)/4} log T uniformly for 1/2 ≤ σ ≤ 1 (Theorem 1 there),
  which on integration over σ gives Σ (β − 1/2)^+ = O(T), sharper than Littlewood's bound.
- Status: VERIFIED bibliographically (zbMATH Open API, Zbl 0061.08402; also the reference list of
  [@simonic-2019]). The density bound and its attribution to "[Sel46, Theorem 1]" are confirmed by
  the abstract and introduction of [@simonic-2019] and by [@tao-trudgian-yang] (θ = 1/8 in
  T^{1−θ(2σ−1)} log T). The O(T) displacement bound is a one-line consequence (∫_{1/2}^{1}
  T^{1−(σ−1/2)/4} log T dσ ≤ 4T); its attribution to Selberg's paper as a stated result was not
  read in the original (the record's notes say the same).

### `hardy-littlewood-1918`
G. H. Hardy and J. E. Littlewood. "Contributions to the theory of the Riemann zeta-function and
the theory of the distribution of primes". *Acta Mathematica* 41 (1918), 119–196.
DOI 10.1007/BF02422942.
- Cited for: mean values of ζ, in particular the mean square ∫_1^T |ζ(σ+it)|² dt = O(T) for
  fixed σ > 1/2 and the T log T mean square on the line.
- Status: VERIFIED for authors, title, journal, volume, pages and DOI (Crossref; zbMATH JFM
  46.0498.01). YEAR: Crossref gives 1916, zbMATH 1917; the customary citation, and the record's
  notes, give 1918. Print "41 (1918)" or "41 (1916–1918)". That the σ > 1/2 mean-square theorem
  is in this paper is the record's attribution ("Hardy–Littlewood's O(T) mean square") and the
  standard one; not read in the original.

### `hardy-littlewood-1921`
G. H. Hardy and J. E. Littlewood. "The zeros of Riemann's zeta-function on the critical line".
*Mathematische Zeitschrift* 10 (1921), no. 3–4, 283–317. DOI 10.1007/BF01211614.
- Cited for: the approximate functional equation in its first form; N_0(T) ≫ T.
- Status: VERIFIED bibliographically (Crossref; also in the reference list of [@simonic-2019]).
  What the paper contains is stated from the standard account, not read in the original.

### `hardy-littlewood-1923`
G. H. Hardy and J. E. Littlewood. "The approximate functional equation in the theory of the
zeta-function, with applications to the divisor-problems of Dirichlet and Piltz". *Proceedings of
the London Mathematical Society* (2) 21 (1923), 39–74. DOI 10.1112/plms/s2-21.1.39.
- Cited for: the approximate functional equation.
- Status: VERIFIED (Crossref).

### `hardy-littlewood-1929`
G. H. Hardy and J. E. Littlewood. "The approximate functional equations for ζ(s) and ζ²(s)".
*Proceedings of the London Mathematical Society* (2) 29 (1929), 81–97.
DOI 10.1112/plms/s2-29.1.81.
- Cited for: the approximate functional equation (optional).
- Status: VERIFIED (Crossref).

### `ingham-1937`
A. E. Ingham. "On the difference between consecutive primes". *The Quarterly Journal of
Mathematics (Oxford Series)* 8 (1937), 255–266. DOI 10.1093/qmath/os-8.1.255.
- Cited for: Ingham's first density bound (A(σ) ≤ 2 + 4μ(1/2)) and "Lindelöf implies the density
  hypothesis" (optional).
- Status: VERIFIED (Crossref); the attribution of the bound is from [@tao-trudgian-yang].

### `ingham-1940`
A. E. Ingham. "On the estimation of N(σ, T)". *The Quarterly Journal of Mathematics (Oxford
Series)* 11 (1940), 201–202. DOI 10.1093/qmath/os-11.1.201.
- Cited for: N(σ, T) ≪ T^{3(1−σ)/(2−σ)} log^5 T, still the best exponent next to the line
  (1/2 ≤ σ ≤ 7/10).
- Status: VERIFIED (Crossref: pages 201–202). The bound is confirmed by [@simonic-2019]
  (introduction, eq. (2)) and [@tao-trudgian-yang] (A(σ) ≤ 3/(2−σ)).

### `montgomery-1973`
H. L. Montgomery. "The pair correlation of zeros of the zeta function". In: *Analytic Number
Theory* (St. Louis, Mo., 1972), Proceedings of Symposia in Pure Mathematics 24, American
Mathematical Society, 1973, pp. 181–193. DOI 10.1090/pspum/024/9944.
- Cited for: the pair correlation conjecture and the GUE-like small-gap law; the deduction, under
  RH, that at least 2/3 of the zeros are simple.
- Status: VERIFIED (Crossref; zbMATH Zbl 0268.10023).

### `montgomery-vaughan-1974`
H. L. Montgomery and R. C. Vaughan. "Hilbert's inequality". *Journal of the London Mathematical
Society* (2) 8 (1974), 73–82. DOI 10.1112/jlms/s2-8.1.73.
- Cited for: the weighted Hilbert inequality and the mean-value theorem for Dirichlet polynomials
  (zeta23's `Zeta23.MV.mvDiag_thirteen`, the layer's `M1.dirichlet_meanSquare_le`).
- Status: VERIFIED (Crossref). The label "Cor. 3" used in the record's notes was not checked.

### `odlyzko-1987`
A. M. Odlyzko. "On the distribution of spacings between zeros of the zeta function". *Mathematics
of Computation* 48 (1987), no. 177, 273–308. DOI 10.1090/S0025-5718-1987-0866115-0.
- Cited for: numerical agreement of zero spacings with GUE statistics.
- Status: VERIFIED (Crossref).

### `levinson-1974`
Norman Levinson. "More than one third of zeros of Riemann's zeta-function are on σ = 1/2".
*Advances in Mathematics* 13 (1974), no. 4, 383–436. DOI 10.1016/0001-8708(74)90074-7.
- Cited for: the proportion of zeros on the line (1/3).
- Status: VERIFIED (Crossref; the Crossref title prints "σ = 12" for σ = 1/2).

### `conrey-1989`
J. B. Conrey. "More than two fifths of the zeros of the Riemann zeta function are on the critical
line". *Journal für die reine und angewandte Mathematik* 399 (1989), 1–26.
DOI 10.1515/crll.1989.399.1.
- Cited for: the proportion of zeros on the line (2/5).
- Status: VERIFIED (Crossref for title, journal, pages; zbMATH Zbl 0668.10044 for the author).

### `levinson-montgomery-1974`
Norman Levinson and H. L. Montgomery. "Zeros of the derivatives of the Riemann zeta-function".
*Acta Mathematica* 133 (1974), 49–65. DOI 10.1007/BF02392141.
- Cited for: the quantitative form of Speiser's theorem (named in DEPOSIT_MAP.md).
- Status: VERIFIED (Crossref).

### `speiser-1934`
Andreas Speiser. "Geometrisches zur Riemannschen Zetafunktion". *Mathematische Annalen* 110
(1934), 514–521. DOI 10.1007/BF01448042.
- Cited for: Speiser's theorem (RH is equivalent to ζ′ having no zeros in 0 < Re s < 1/2), kept
  in the library as the named hypothesis `SpeiserTheorem` (`MNF/RH/Hypotheses.lean`:
  `RiemannHypothesis ↔ ∀ s ∈ LeftCriticalStrip, deriv riemannZeta s ≠ 0`). The statement is the
  record's and the standard one; the 1934 paper was not read.
- Status: VERIFIED for author, title, journal, volume, pages, DOI. YEAR: zbMATH (Zbl 0010.16401,
  JFM 60.0272.04) gives 1934; Crossref gives December 1935 for the issue. "1934" matches the
  record and zbMATH; "110 (1935)" would match the publisher's metadata.

### `von-mangoldt-1895`
H. von Mangoldt. "Zu Riemanns Abhandlung 'Ueber die Anzahl der Primzahlen unter einer gegebenen
Grösse'". *Journal für die reine und angewandte Mathematik* 114 (1895), 255–305.
DOI 10.1515/crll.1895.114.255.
- Cited for: the first proof of the Riemann–von Mangoldt formula for N(T).
- Status: VERIFIED (Crossref; zbMATH JFM 26.0215.03, which writes "Riemann's").

### `von-mangoldt-1905`
H. von Mangoldt. "Zur Verteilung der Nullstellen der Riemannschen Funktion ξ(t)". *Mathematische
Annalen* 60 (1905), 1–19. DOI 10.1007/BF01447494.
- Cited for: the Riemann–von Mangoldt formula with remainder O(log T) (standard attribution,
  not read in the original).
- Status: VERIFIED (zbMATH JFM 36.0263.02; Crossref, whose title field misprints ξ as γ).

### `backlund-1918`
R. J. Backlund. "Über die Nullstellen der Riemannschen Zetafunktion". *Acta Mathematica* 41
(1918), 345–375. DOI 10.1007/BF02422950.
- Cited for: Backlund's method for N(T) (zeta23 has a module `Zeta23/RvM/Backlund.lean`)
  (optional).
- Status: VERIFIED (zbMATH JFM 46.0499.01).

### `vallee-poussin-1896`
Ch.-J. de la Vallée Poussin. "Recherches analytiques sur la théorie des nombres premiers".
*Annales de la Société Scientifique de Bruxelles* (1896), 183–256, 281–362, 363–397.
- Cited for: ζ(1 + it) ≠ 0 and the prime number theorem (optional; the zero-free *region* is in
  the 1899 memoir).
- Status: PARTLY VERIFIED (zbMATH JFM 27.0155.03: author, original title, year, pages). VOLUME:
  zbMATH writes "Brux. S. sc. 21 B"; the customary citation gives volume 20 (from memory). Print
  the volume only after checking, or cite by year and pages.

### `vallee-poussin-1899`
Ch.-J. de la Vallée Poussin. "Sur la fonction ζ(s) de Riemann et le nombre des nombres premiers
inférieurs à une limite donnée". *Mémoires couronnés et autres mémoires publiés par l'Académie
royale de Belgique* 59 (1899), 74 pp.
- Cited for: the classical zero-free region σ ≥ 1 − c/log t.
- Status: VERIFIED bibliographically (zbMATH JFM 30.0193.03: "Belg. Mém. 59, 74 p. (1899)"; the
  expansion of the series name is the customary one). Result attribution standard, not read in
  the original.

### `vinogradov-1958`
I. M. Vinogradov. "A new estimate of the function ζ(1 + it)" (Russian). *Izvestiya Akademii Nauk
SSSR, Seriya Matematicheskaya* 22 (1958), 161–164.
- Cited for: the Vinogradov–Korobov zero-free region σ ≥ 1 − c/((log t)^{2/3}(log log t)^{1/3}).
- Status: VERIFIED bibliographically (zbMATH Zbl 0097.26302, which gives the title in German:
  "Eine neue Abschätzung der Funktion ζ(1+it)"; the English rendering above is a translation).

### `korobov-1958`
N. M. Korobov. "Estimates of trigonometric sums and their applications" (Russian). *Uspekhi
Matematicheskikh Nauk* 13 (1958), no. 4(82), 185–192.
- Cited for: as [@vinogradov-1958].
- Status: VERIFIED bibliographically (zbMATH Zbl 0086.03803, title given there in German:
  "Abschätzungen trigonometrischer Summen und ihre Anwendungen").

### `platt-trudgian-2021`
Dave Platt and Tim Trudgian. "The Riemann hypothesis is true up to 3·10^12". *Bulletin of the
London Mathematical Society* 53 (2021), no. 3, 792–797. DOI 10.1112/blms.12460.
arXiv:2004.09765.
- Cited for: the numerical verification of RH for 0 < γ ≤ 3·10^12 (so every hypothesis about a
  strip holds vacuously below that height).
- Status: VERIFIED (Crossref; arXiv listing). The exact figures in the record's notes
  (12,363,153,437,138 zeros up to height 3,000,175,332,800) are NOT in the abstract and were not
  verified: quote only "up to height 3·10^12" unless the article itself is checked.

### `ivic-1985`
Aleksandar Ivić. *The Riemann Zeta-Function: The Theory of the Riemann Zeta-Function with
Applications*. New York: John Wiley & Sons, 1985. xvi + 517 pp. (Reprinted: Dover, Mineola, NY,
2003, as *The Riemann Zeta-Function: Theory and Applications*.)
- Cited for: zero-density estimates, Chapter 11 (the chapter number is the record's; not checked).
- Status: VERIFIED bibliographically (zbMATH Zbl 0556.10026, Zbl 1034.11046).

### `guth-maynard`
Larry Guth and James Maynard. "New large value estimates for Dirichlet polynomials". *Annals of
Mathematics* (2) 203 (2026), no. 2, 623–675. DOI 10.4007/annals.2026.203.2.6. arXiv:2405.20552
(v1 31 May 2024, v2 7 April 2026).
- Cited for: the current zero-density record N(σ, T) ≤ T^{30(1−σ)/13+o(1)}; context only.
- Status: VERIFIED (zbMATH Open API: journal, volume, pages, DOI; arXiv listing: versions).

### `tao-trudgian-yang`
Terence Tao, Tim Trudgian and Andrew Yang. "New exponent pairs, zero density estimates, and zero
additive energy estimates: a systematic approach". arXiv:2501.16779, 28 January 2025. Companion
database (ANTEDB), zero-density chapter:
https://teorth.github.io/expdb/blueprint/zero-density-chapter.html
- Cited for: a tabulated history of zero-density exponents (Carlson, Ingham, Huxley, Jutila,
  Heath-Brown, Bourgain, Guth–Maynard; Selberg near the line) (optional).
- Status: VERIFIED (arXiv listing; the blueprint chapter was read). The chapter does not mention
  Bohr–Landau or Littlewood.

### `simonic-2019`
Aleksander Simonič. "Explicit zero density estimate for the Riemann zeta-function near the
critical line". arXiv:1910.08274 (v2, 29 November 2019).
- Cited for: a modern statement of Selberg's 1946 bound, and of Jutila's and Conrey's
  improvements of the constant 1/4 (optional).
- Status: VERIFIED as a preprint (arXiv listing and the PDF's first pages). The arXiv page lists
  no journal reference; a published version was not searched for.

### `chourasiya-2024`
Shashi Chourasiya. "An explicit version of Carlson's theorem". arXiv:2412.02068, 3 December 2024.
- Cited for: an explicit form of Carlson's bound (optional).
- Status: VERIFIED as a preprint (arXiv listing; no journal reference there). The explicit
  constants quoted in the record's notes (0.78, exponent 5 − 2σ of the logarithm) were not checked.

### `bui-conrey-young-2011`
H. M. Bui, Brian Conrey and Matthew P. Young. "More than 41% of the zeros of the zeta function
are on the critical line". *Acta Arithmetica* 150 (2011), no. 1, 35–64. DOI 10.4064/aa150-1-3.
- Cited for: proportion on the line (optional).
- Status: VERIFIED (zbMATH Zbl 1250.11083).

### `pratt-robles-zaharescu-zeindler-2020`
Kyle Pratt, Nicolas Robles, Alexandru Zaharescu and Dirk Zeindler. "More than five-twelfths of
the zeros of ζ are on the critical line". *Research in the Mathematical Sciences* 7 (2020),
no. 1, Paper No. 2, 74 pp. DOI 10.1007/s40687-019-0199-8.
- Cited for: the unconditional record (5/12) before [@alpoge-furman] (optional).
- Status: VERIFIED (zbMATH Zbl 1505.11116).

### `davenport-heilbronn-1936`
H. Davenport and H. Heilbronn. "On the zeros of certain Dirichlet series". *Journal of the London
Mathematical Society* 11 (1936), 181–185 (part II: 307–312). DOI 10.1112/jlms/s1-11.3.181.
- Cited for: a function with a Riemann-type functional equation and zeros off the line; why
  mean-value arguments alone cannot exclude zeros (optional).
- Status: VERIFIED (zbMATH Zbl 0014.21601, Zbl 0015.19802).

---

## 4. Related recent work named in the record

### `liu-2026`
Baiying Liu. "Improved zero-free half-planes for the quasi-Riemann hypothesis". arXiv:2610.12234
[math.NT], v1 8 October 2026, v2 12 October 2026.
- Cited for: a parameter refinement of the 7/8 half-plane (constant about 0.874957), read and not
  run in the record (DEPOSIT_MAP.md §8).
- Status: VERIFIED (arXiv listing). Per the abstract as summarized, the result is stated for
  finite-order Hecke L-functions over Q(√−3). The record's DEPOSIT_MAP names the repository with
  the words "Slightly-improved-zero-free-half-planes…"; the arXiv title is as above.

### `qr-tracker`
*Quasi-Riemann Tracker* (community tracker of zero-free half-plane bounds with CI replays).
https://github.com/GTimG/QuasiRiemannTracker
- Cited for: the frontier value recorded in DEPOSIT_MAP.md §8 (0.873985 on 2026-10-27).
- Status: PARTLY VERIFIED: the repository exists and describes itself as a tracker of quasi-Riemann bounds
  with Lean formalizations and independent proof verification. The frontier value and the record
  identifier quoted in DEPOSIT_MAP.md were not re-checked.

### `lamzouri-2026`
Youness Lamzouri. "A new proof that more than 2/3 of the zeros of the Riemann zeta function are
simple and on the critical line". arXiv:2609.02882, v1 2 September 2026, v2 8 September 2026.
- Cited for: the paper formalized by [@axiom-zetazeros], which contains a prior Lean proof that ζ
  has no real zero in (0, 1) (section 5).
- Status: VERIFIED (arXiv listing).

---

## 5. Prior public Lean formalizations: what was found (answers to the three questions)

Searches made on 2026-11-10: web search; the Palomar data API
(`https://data.palomar-registry.org/api/v1/results?q=…` with q = zeta, zeros, density, Riemann,
Landau, Bohr-Landau, critical line, zero-free, two thirds, seven eighths, quasi-Riemann, Alpöge);
GitHub code search restricted to Lean (bohr_landau, bohrLandau, "Bohr-Landau", zero_density,
zeroDensity, riemannZeta with "Ioo 0 1", riemannZeta_neg_of, riemannZeta_real_neg, …), also
restricted to leanprover-community/mathlib4, AlexKontorovich/PrimeNumberTheoremAnd, teorth/IEANTN
and AxiomMath/PrimeNumberTheoremAnd; Mathlib's `Mathlib/NumberTheory/LSeries/ZetaZeros.lean` on
master; the Mathlib checkout at the zeta23 pin `51e6992e` on this machine. LIMITS: GitHub code
search does not index every repository (it did not return Lewko's repositories, which exist); the
Palomar search is keyword based and returned partial pages; an absence below is "not found by
these searches", not "does not exist".

### 5.1 A zero-density estimate N(σ, T) = O(T^{1−c}): YES, prior Lean formalizations exist

Four Palomar entries by Mark Lewko predate run 10 (2026-11-04), all on Lean `v4.35.0-rc2`,
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, permitted axioms propext, Quot.sound,
Classical.choice, replayed by the registry with nanoda and con-ron, review outcome "neutral" by an
automated reviewer, status "registered". Authorship per the repositories: Mark Lewko supplied the
mathematics and directed the formalization, with AI assistance (Codex is named in one README).

### `lewko-density-34`
Mark Lewko. "The density hypothesis for σ > 3/4". Palomar registry PALOMAR-2026-10-07-000009
(registered 2026-10-07). Repository mrklwk/zeta-zero-density-lean, commit
`5dd0dd391c117ef4d8fd04a6b16b4b1ad5735d88`. Theorem `DensityThreeQuarters.density_bound`:
N(σ, T) ≪ T^{2(1−σ)+ε} for 3/4 < σ < 1, zeros counted with multiplicity.
https://data.palomar-registry.org/entries/PALOMAR-2026-10-07-000009-v1.json ;
https://github.com/mrklwk/zeta-zero-density-lean
- Status: VERIFIED that the entry and repository exist as described (registry JSON, README). The
  Lean statement itself was not read. The registry says the mathematical source is unpublished
  notes of the author.

### `lewko-density-32`
Mark Lewko. "A zero-density estimate with exponent 3(1−σ)/(2σ) for the Riemann zeta function".
PALOMAR-2026-10-09-000005 (registered 2026-10-09). Repository
mrklwk/zeta-density-three-over-two-sigma-lean, commit `804bdb55b1fc40e6a1a6878fd96078644a70e288`.
Theorems `DensityStronger.density_bound`, `DensityStronger.twelfth_moment`: for σ > 3/4, ε > 0,
N(σ, T) ≤ C T^{3(1−σ)/(2σ)+ε} for T ≥ 2 (zeros with Re ρ ≥ σ, |Im ρ| ≤ T, with multiplicity).
https://data.palomar-registry.org/entries/PALOMAR-2026-10-09-000005-v1.json
- Status: VERIFIED as above (registry JSON, README); Lean statement not read.

### `lewko-density-3917`
Mark Lewko. "Zero-density estimates from an improved large-values bound".
PALOMAR-2026-10-11-000010 (registered 2026-10-11T09:00:10Z). Repository
mrklwk/zeta-density-39-over-17-lean, commit `ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0`.
Registered theorems `GuthMaynardStatement.full_curve`, `.global_uniform`,
`.uniform_away_boundary`, `.middle_large_values`.
https://data.palomar-registry.org/entries/PALOMAR-2026-10-11-000010-v1.json ;
https://github.com/mrklwk/zeta-density-39-over-17-lean/blob/ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0/lean/Challenge.lean
- Status: VERIFIED, and here the challenge file at the registered commit WAS read. In mathematical
  terms `full_curve` says: for every σ with 1/2 ≤ σ ≤ 1 and every ε > 0 there is C > 0 such that
  for all T ≥ 2 the zeros ρ of `riemannZeta` with 0 < Re ρ < 1, Re ρ ≥ σ, |Im ρ| ≤ T, counted with
  analytic multiplicity, number at most C·T^{A(σ)(1−σ)+ε}, where A(σ) = 3/(2−σ) for σ ≤ 9/13,
  18/(7σ+3) for 9/13 < σ ≤ 5/7, 9/4 for 5/7 < σ ≤ 3/4 and 3/(2σ) for σ > 3/4. `global_uniform`
  gives one constant for all σ in [1/2, 1] with exponent (39/17)(1−σ)+ε. What was read is the
  *statement* file (proofs replaced by `sorry`, as in any Comparator challenge); that the solution
  was accepted is the registry's report, not re-checked here.
- CONSEQUENCE FOR THE PAPER: on [1/2, 9/13] this is Ingham's exponent 3(1−σ)/(2−σ), which is < 1
  for every σ > 1/2 and smaller than the record's exponent 1 − (2σ−1)²/(2σ) at every σ in
  (1/2, 1) (write σ = 1/2 + δ: 1 − 2δ/(3/2 − δ) against 1 − 4δ²/(1 + 2δ)). So a public Lean
  zero-density estimate with a power saving for every σ > 1/2, stronger than run 10's, was
  registered about three weeks before run 10. It is one-sided (Re ρ ≥ σ, |Im ρ| ≤ T), on another
  toolchain pin, and is not on the zeta23 tree.

### `lewko-density-improved`
Mark Lewko. "Improved zero-density estimates for the Riemann zeta function".
PALOMAR-2026-10-21-000008 (registered 2026-10-21T03:18:19Z). Same repository, commit
`c55fc0088bd4d7e61c5934abc5dd9153e8cb2f5d`; 73 registered theorem names in namespace
`LewkoDensityPalomar`; improved exponents on 12/17 < σ ≤ 3/4 and 7/9 < σ ≤ 7/8.
https://data.palomar-registry.org/entries/PALOMAR-2026-10-21-000008-v1.json
- Status: VERIFIED that the entry exists as described (registry JSON); Lean statements not read.

### `fiori-2026`
Andrew Fiori. "Zero density theorems for short intervals". arXiv:2609.22624 (18 September 2026).
Lean formalization: andrewfiori/ZeroDensityInShortIntervals, Lean `v4.34.0-rc1`, CC-BY-4.0;
Palomar PALOMAR-2026-09-23-000001. https://github.com/andrewfiori/ZeroDensityInShortIntervals
- Cited for: explicit zero-density results in short windows (t − h, t + h], with Lean theorems
  `zero_density_jensen` and `zero_density_littlewood` (via Jensen's formula and via Littlewood's
  lemma). Per the README these are CONDITIONAL on 27 assumptions packaged as hypothesis classes
  (16 published bounds on ζ and Γ, 11 numerical certificates computed outside Lean).
- Status: VERIFIED (arXiv listing; README; Palomar search listing). Not a T^{1−c} estimate.

Also found: PrimeNumberTheoremAnd defines, in `PrimeNumberTheoremAnd/IEANTN/ZetaDefinitions.lean`
(last commit 2026-09-28), a zero-counting function `riemannZeta.N'` and a *structure*
`zero_density_bound` whose field `bound` is the estimate; this is a hypothesis record used to
quote explicit results from the literature, not a proved density theorem. The successor project
teorth/IEANTN states the Kadiri–Lumley–Ng explicit density estimate as a node whose conclusions
are Lean `Prop`s. Neither proves a zero-density estimate. Mathlib (master, `ZetaZeros.lean`,
Copyright 2026 Huanyu Zheng) proves that the zero set of ζ is closed, discrete and finite on
compact sets; it has no zero-counting function and no density estimate.

### 5.2 The Bohr–Landau theorem: no Lean statement under that name found; it is implied by 5.1

No Lean declaration named after Bohr–Landau, and no two-sided count of the zeros with
|Re ρ − 1/2| ≥ δ, was found by the searches above (GitHub Lean code search for bohr_landau,
bohrLandau, "Bohr-Landau", "Bohr–Landau": no hits; Palomar search "Bohr-Landau": no entries;
"Landau": two unrelated entries; Mathlib and PrimeNumberTheoremAnd: nothing). However,
[@lewko-density-3917] `full_curve` gives, for each fixed σ > 1/2, N(σ, T) ≤ C·T^{θ} with θ < 1
(take ε small), which is stronger than the one-sided Bohr–Landau bound O(T); the two-sided form
follows from it by the reflection ρ ↦ 1 − ρ̄. So the content of Bohr–Landau was available in
Lean, as a corollary not stated as such, before runs 8 and 9 (2026-11-03/04). The record's own
DEPOSIT_MAP.md §8 already notes Lewko's entries as a possible source of "the Bohr–Landau-type
input".

### 5.3 Non-vanishing of ζ on the real segment (0, 1): YES, prior Lean proofs exist

### `axiom-zetazeros`
Axiom Math. *ZetaZerosV2* (Lean formalization of [@lamzouri-2026]). GitHub repository
AxiomMath/ZetaZerosV2, Apache-2.0, head commit `1d7edeb4e67096f9da1b37cd4b763e8b73886655`
(2026-10-03). File `ZetaZeros/Analytic/RealSegment.lean` ("No zeros on the real segment").
https://github.com/AxiomMath/ZetaZerosV2/blob/1d7edeb4e67096f9da1b37cd4b763e8b73886655/ZetaZeros/Analytic/RealSegment.lean
- Contains `ZetaZeros.riemannZeta_re_neg_of_pos_of_lt_one` ((ζ σ).re < 0 for real 0 < σ < 1),
  `ZetaZeros.riemannZeta_neg_of_pos_of_lt_one` and `ZetaZeros.riemannZeta_ne_zero_of_pos_of_lt_one`
  (ζ σ ≠ 0 for real 0 < σ < 1), proved from the first-order Euler–Maclaurin formula at N = 1 with
  PrimeNumberTheoremAnd's `ZetaBounds`: the same route as the record's
  `riemannZeta_ofReal_ne_zero_of_mem_Ioo` (run 11, 2026-11-11 UTC).
- Status: VERIFIED (file read through the GitHub API; commit date 2026-10-03T13:37:59Z, which is
  also the only commit touching the file). The repository's README says it was verified locally
  with Comparator; no registry entry was looked for.

### `hubbard-goldbach-lean`
Steve Hubbard. *goldbach-lean* (GitHub repository sthubbar/goldbach-lean; several Palomar
entries). File `entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean`, theorem
`riemannZeta_real_neg`: for real 0 < σ < 1, ζ(σ) is real and negative. File commit 2026-10-21;
the file header says it was written by AI.
https://github.com/sthubbar/goldbach-lean/blob/main/entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean
- Status: VERIFIED (file read through the GitHub API on the default branch; not pinned to a
  commit here).

Mathlib itself has no such lemma at the zeta23 pin (local grep of `Mathlib/NumberTheory/LSeries/`
and `Harmonic/ZetaAsymp.lean`: only `riemannZeta_ne_zero_of_one_lt_re`, `…_of_one_le_re`,
`riemannZeta_one_ne_zero` and neighbourhood-of-1 lemmas) nor in `ZetaZeros.lean` on master; the
zeta23 tree has `riemannZeta_ne_zero_of_two_le_re` and a segment lemma conditional on no zero at
height T, not the real-segment fact.

### 5.4 The other new statements

- Total displacement of the zeros (the record's "reservoir mass", Littlewood/Selberg type): no
  prior Lean statement found (one GitHub code search; Palomar listings read). Weak evidence only.
  Lewko's uniform bounds do not obviously imply a non-trivial displacement bound.
- The pair-measure ("cube") module and its two equivalences are in the author's own vocabulary;
  no search is meaningful. Related Lean work on simple zeros and proportions exists (zeta23;
  AxiomMath/ZetaZerosV2; Palomar entries of teal-sea/zeta-lab) and is not about these statements.
- Riemann–von Mangoldt in Lean: used by the record from zeta23 (`Zeta23.RvM`); not searched.

### 5.5 What the paper may and may not say (for framing rule 8)

- NOT supported: "the author is not aware of a prior Lean formalization of a zero-density
  estimate with a power saving". Say instead that Lean zero-density estimates with stronger
  exponents were registered earlier by Lewko [@lewko-density-34; @lewko-density-32;
  @lewko-density-3917; @lewko-density-improved], on a different toolchain pin and in one-sided
  form, and that run 10 is an independent formalization of Carlson's method on the zeta23 tree,
  with a weaker exponent, judged by Comparator with a published receipt.
- NOT supported: any priority claim for "no real zero of ζ in (0, 1)"; cite [@axiom-zetazeros]
  (2026-10-03) and [@hubbard-goldbach-lean] as earlier Lean proofs by the same Euler–Maclaurin
  argument.
- Supportable, with the caveat attached: "The author is not aware of a prior Lean statement of
  the Bohr–Landau theorem in its two-sided form (a count of the zeros with |Re ρ − 1/2| ≥ δ); the
  one-sided bound is a consequence of the stronger estimates of [@lewko-density-3917]."
- Supportable as stated, weakly: "The author is not aware of a prior Lean formalization of a
  bound for the total displacement Σ m(ρ)|Re ρ − 1/2|" (searches limited as described above).

---

## 6. Disagreements and corrections found while compiling

1. Title of arXiv:2608.13637: record's README has the long wording; arXiv has "…of the zeta
   zeros…" (see `alpoge-furman`).
2. Ingham 1940 is pp. 201–202 of Quart. J. Math. 11 (Crossref), not 291–292 as sometimes quoted.
3. Carlson: 1920 (customary, Littlewood's citation) against 1921 (zbMATH, Tao–Trudgian–Yang).
4. Speiser: 1934 (zbMATH, the record) against December 1935 (Crossref issue date).
5. Selberg, "On the zeros of Riemann's zeta-function": 1942 (customary) against 1943 (zbMATH).
6. Hardy–Littlewood, Acta Math. 41: 1916 (Crossref), 1917 (zbMATH), 1918 (customary, the record).
7. de la Vallée Poussin 1896: volume 20 (customary) against "21 B" (zbMATH).
8. The record's README dates run 11 "2026-11-11"; the run-11 report gives start
   2026-11-11T00:02:37Z and end 2026-11-11T00:17:52Z (UTC), which is 2026-11-10 in the operator's
   local time. Dates in the paper should be stated as UTC.
9. The record's DEPOSIT_MAP.md §8 cites only two of Lewko's four Palomar entries
   (-10-11-000010 and -10-21-000008) and describes them as on "another pin" and "one-sided";
   both descriptions are confirmed. The two earlier entries (-10-07-000009, -10-09-000005) are
   not mentioned there.
10. The record's notes (STRIP_PLAN.md, STRIP_SCOPE_REPORTS) call run 10's target "the first
    kernel-checked zero-density estimate with a power saving … subject to" reading Lewko's
    entries. They have now been read: the claim "first" does not hold (5.1).
