# Review findings applied to WORK/paper.md

Applied 2026-11-11 UTC (2026-11-10 local). 70 findings from five reviewers (lens 0 to 4).
Each was checked against the files it cites (and, for bibliography, against the web pages named at
the end) before any edit. Result: 69 APPLIED, 1 REJECTED as worded (its defect is fixed under another
finding). Where a proposed sentence went beyond what a file supports, a narrower wording was used;
those cases are marked "narrowed" with the reason.

How the edits were made: exact-string replacements that stop if an anchor is missing or ambiguous
(`review/_apply/apply1.py`, `apply2.py`, `apply3.py`, plus six one-line corrections made during the
re-read); the paper before the edits is `review/_apply/paper.before.md`. After editing:
`review/_assemble/check.py` reports RESULT: OK (18 code blocks byte-identical to the drafts, 39 keys
cited and 39 reference entries, sorted, all defined in `facts/literature.md`, 39 cross-references to
23 existing headings, Appendix A and the table of runs 3 to 6 equal to `facts/runs.md`);
`check_lean.py` finds every Lean statement in the receipts or sources. Words: 14261 before, 16142
after. Nothing outside WORK was modified.

## Lens 0 (Lean fidelity)

1. major, Appendix B, three `Cube.lean` rows tagged [PROVED]: APPLIED. `Cube.lean` lines 173 to 175, 242, 253, 488 use `Zeta23.zetaZeroConfig.reflect_mem` and the real-zero theorem; rows now read [PROVED | this tree], the header says the register prints [PROVED], and the body names the zeta23 lemma.
2. minor, inputs taken from the tree: APPLIED. `Zeta23/BohrLandau.lean` lines 40 and 50 use `reflect_mem` and `mult_reflect`; both are now listed for step 7.
3. minor, paraphrase of [PROVED | this tree]: APPLIED. `BohrLandauClosure.lean` imports `Zeta23.BohrLandau`, which holds the two `sorry` lemmas; the header now says so.
4. minor, "Run" column for the run 3 rows: APPLIED. One sentence added: run 3 compared definitions as holes, bodies first in run 4 (DEPOSIT_MAP lines 143 to 146).
5. minor, "The second threshold is exact": APPLIED, merged with lens 2 no. 4 and lens 3 no. 8. The docstring in `Unconditional.lean` says only that the 7/8 theorem does not exclude the line Re s = 7/8.
6. minor, reasons for the 27 + 2 exclusions: APPLIED. Add-on v6 README lines 39 to 43 give the third reason; the mirror `MNFChallengesD/Extension.lean` (hash as in the receipt) holds 13 `aux_` lemmas and none is among the 534 audit reports.
7. minor, sign of the pole term: APPLIED. `audit.out` prints `↑N ^ (1 - s) / (s - 1)`. The added words "in mean square" were not taken over (not needed for the correction).
8. minor, names of the layer in Appendix B: APPLIED. The namespaces are declared in the add-on's files (`BohrLandauClosure.lean` line 1206, `StripDensity.lean` line 73).

## Lens 1 (receipts and numbers)

1. major, "nothing had been compiled": APPLIED. RECEIPT.md records 106968 compiled dependency files before run 1 and the prebuilt Mathlib cache; both sentences of the Introduction now say "nothing of the challenge or of the proof".
2. major, definition counts presented as bodies compared: APPLIED, narrowed. The report scripts count `def` lines (`mnf_check.py` line 91, `z23_density_check.py` line 100); run 4's log exports 43 theorem names and no definition, run 3's adds the 17 holes; `MNF.RH.Counter` is in no statement of runs 4 to 6; `CG`, `meanSquareB`, `A₀` are referred to by nothing but each other in run 11's mirror. Table cells, a paragraph under the table, Appendix A and an erratum were changed. Narrowed: the example is given for run 11 only (run 10's mirror was not checked), and "a few" became "a counted definition that no claimed statement refers to (`MNF.RH.Counter` is one)".
3. major, placeholder DOI: APPLIED with the fallback sentence ("This paper is deposited on Zenodo; its DOI is on the Zenodo record page."). The DOI itself is the author's to reserve; see the list at the end.
4. minor, date line: APPLIED as "Date: 2026-11-11 (UTC)", the UTC date of this revision and of run 11. The deposit date is the author's; see the list at the end.
5. minor, "Mirrors are generated at run time": APPLIED, corrected. Add-ons v1 to v3 ship `MNFChallenges/` under their manifests and copy it; the zeta23 add-ons generate in the tree. The proposed "in both cases the receipt lists their sha256" is not true of run 4, whose listing has only `RH.lean` and `RH.json`; the text says so.
6. minor, "re-derives every hash the record cites": APPLIED with the wording of lens 2 no. 3.
7. minor, two duration formats: APPLIED ("1 h 54 min 37 s", "21 min 1.5 s", column header "Wall clock (min:s)").
8. minor, "102265": APPLIED ("102,265"; the receipt prints the number without a separator).
9. minor, sign of the pole term: APPLIED (same edit as lens 0 no. 7).
10. minor, Figure 1 shows 3.4 and 3.3: APPLIED. The caption explains exact law against Wigner surmise.
11. minor, labels inside Figure 2: APPLIED by relabeling a copy of the image (see "Figures" below) and by the caption.
12. minor, statements that go stale at the next push: APPLIED in part. The sentence now ties `VERIFY=OK` and the counts to commit `f03aaa9`, "the commit that added run 11". The stale README header, its `sources/` list and `zenodo-metadata.json` are in the repository, outside WORK, and were not touched; see the list at the end.

## Lens 2 (claims and framing)

1. major, what NOTICE attributes to Claude Code inside MNF.RH: APPLIED, narrowed. NOTICE lists the three gap theorems of v2 and the Prop forms of `GapMechanism` and `SchrodingerRealization`; the paragraph now lists them, and "What is not claimed" and the abstract say "parts of MNF.RH". Not taken over: "with its re-proved lemmas included" (not in NOTICE).
2. major, headline and annotations inside Figure 1: APPLIED by the preferred fix, a relabeled copy of the image with neutral labels (see "Figures" below), and a new caption.
3. major, "every hash the record cites": APPLIED. The script checks the 27 listed files, the verdicts, the sources of runs 3 to 5 and 7 to 11, the manifests and two upstream files.
4. minor, "exact": APPLIED (merged with lens 0 no. 5).
5. minor, abstract drops required qualifiers: APPLIED, narrowed. "The author's gap hypothesis" became "a zero-free-strip hypothesis of the author's library" (the term is not defined in the abstract); "existed in Lean before" became "were registered earlier by others" (acceptance is the registry's report); "set the goals" added from framing rule 7.
6. minor, register tag placed after "it is RH": APPLIED in the three places.
7. minor, "more than two thirds" against the judged constants: APPLIED, narrowed. The receipt's statements have 2/3 − ε, 5/6 − ε and `cMT`; the decimals are quoted with the register's words "docstrings, not statements"; "which Comparator does not compare" was not taken over.
8. minor, "is not known to imply anything about it": APPLIED.
9. minor, "turn the illustration into a theorem": APPLIED, merged with lens 4 no. 10.
10. minor, heading "milestone": APPLIED ("The intermediate result for distances above one sixth"; no cross-reference used the old title).
11. minor, "most recent improvement": APPLIED with the wording of lens 3 no. 1.
12. minor, "One gap remains": APPLIED ("A gap in provenance:").
13. minor, theorem counts read as content: APPLIED, narrowed. "Most of them auxiliary lemmas" was not taken over (no file gives that count); the sentence says "auxiliary lemmas included" and quotes the register's "no analytic content" for the 75 of 124.
14. minor, "adversarial reviews" read as reviews by people: APPLIED, narrowed to what the files say (the working log's "workflow agent", NOTICE's "independent model reviewers", no human reviewer named), with one sentence that this paper's text was reviewed by model reviewers too. The optional sentence "No mathematician other than the author has reviewed ..." needs the author's confirmation and was not added.
15. minor, "independent" and Anthropic: APPLIED, narrowed. The paragraph was added to "Authorship and use of AI tools"; the clause on who owns the checkers became "not of a language model" (no file read states the affiliation of the NanoDa fork's owner). The optional sentence on the author's affiliations needs the author's confirmation and was not added.
16. minor, "simplicity of the projected zeros": APPLIED (standard wording, NOTICE's phrase in quotation marks).
17. minor, "each is defined once ... where it is first used": APPLIED, narrowed. MNF is glossed as "the author's name for the framework these Lean files are written for" (the wording of the `Cube.lean` header) and nullification as the thresholding map; "built around" was not taken over.
18. minor, the register's stronger non-claim: APPLIED (DEPOSIT_MAP lines 148 and 149, quoted).
19. minor, "unconditional" corollary: APPLIED.
20. minor, departure from GUE not marked as a non-finding: APPLIED with the notes' own words ("a ~2-2.5 sigma effect on 400 zeros", RESULTS.md line 210).
21. minor, bare constant 5/9: APPLIED, narrowed ("says nothing about whether P(T) vanishes" instead of "far from that expected value").
22. minor, labels inside Figure 2: APPLIED by relabeling and caption (see "Figures" below).

## Lens 3 (literature and attribution)

1. major, Guth and Maynard as "the most recent improvement": APPLIED. arXiv:2501.16779 (28 January 2025) announces new zero-density estimates; the sentence now names Guth and Maynard among the later improvements and Tao, Trudgian and Yang for the tabulation.
2. major, mean square attributed to Hardy and Littlewood 1918: APPLIED. The fact sheet says the attribution was not read in the original; the sentence now cites Section 7.2 of Titchmarsh, as the Lean source does, and the entry `hardy-littlewood-1918` was removed from the References (cited nowhere else).
3. major, Ingham 1940 pages: APPLIED. zbMATH (Zbl 0025.02704) has 291–292; Crossref's own list of the volume has Kober at 193–211 and nothing at 291–292. The entry gives 291–292, keeps the DOI and notes that the Crossref record has 201–202.
4. minor, attribution of O(T) to the 1914 Comptes Rendus note: APPLIED, narrowed. Both notes of 1914 are cited, with "not consulted for this paper"; the proposed "sharpened this to o(T)" was not taken over, because the zbMATH review read does not settle which note proves which bound. `bohr-landau-1914b` added to the References.
5. minor, status of Comparator: APPLIED, narrowed. Archive date, migration notice and "ships with Lean 4.35.0" are in; the causal "because the two artifacts pin ..." became a plain statement of the versions (no file gives the reason). The sentence for Limitations was added.
6. minor, AI provenance of the two external theorems: APPLIED (from the entries `alpoge-furman` and `openai-math` of the fact sheet, without quotation marks, since the sheet paraphrases).
7. minor, Fiori's earlier entry: APPLIED, narrowed to what the registry entry's abstract says, with "not re-checked here". `fiori-2026` added to the References.
8. minor, smaller zero-free boundaries: APPLIED (DEPOSIT_MAP section 8; `liu-2026` added to the References).
9. minor, Lewko's entry stated as fact, and its definition holes: APPLIED. `comparator.json` at the registered commit lists the three definitions as holes; the three definitions are identical in `Challenge.lean` and `Solution.lean` (files fetched and compared).
10. minor, what a hole compares: APPLIED (Comparator's README at tag v4.34.0 names safety levels too).
11. minor, provisional priority claim in the notes: APPLIED (erratum added; both notes contain the quoted phrase).
12. minor, classical dependence on δ: APPLIED, as what the zbMATH review of Littlewood 1924 records.
13. minor, the tables: APPLIED (NOTICE and RESULTS.md name Odlyzko and the LMFDB).
14. minor, Hilbert–Pólya: APPLIED (the register's own name, DEPOSIT_MAP lines 83 and 105).
15. minor, goldbach-lean not pinned: APPLIED. The file's only commit is `30ab3dd5…` of 2026-10-21 (GitHub API); the reference is pinned and the text says both earlier proofs were read, not built.

## Lens 4 (mathematical exposition)

1. major, "GUE: 0.4221": APPLIED, narrowed. The main text now prints only the value computed in the record, the Wigner surmise 0.4220 (`mnf_analysis.log`); 0.4221 is a typed constant (`mnf_analysis.py` line 88). The exact-law value 0.4243 comes from the reviewer's script `review/_mathexp/gue_sd.py`, which was run again here with the same output; it appears only in the erratum, marked as a recomputation made in review.
2. minor, Guth and Maynard: REJECTED as worded. The defect is real and is fixed under lens 3 no. 1; the proposed "sharpest known bound ... with A = 30/13" is contradicted by the registry entry cited in the same paragraph, whose stated coefficient is 39/17.
3. minor, Hardy–Littlewood: APPLIED (same edit as lens 3 no. 2).
4. minor, "The first does not give the second": APPLIED ("is not known to give").
5. minor, the letter A for three constants: APPLIED (A₁, B₁ and A′).
6. minor, sign of the pole term: APPLIED (same edit as lens 0 no. 7).
7. minor, negative ordinates: APPLIED (the docstring of `spectralGapHyp_iff_bandCoincidentMass` says "negative ordinates by conjugation").
8. minor, Selberg's estimate uniform in σ: APPLIED.
9. minor, `Zeta0EqZeta` called an approximate formula: APPLIED in both places.
10. minor, "turn the illustration into a theorem": APPLIED (merged with lens 2 no. 9).
11. minor, P and N used twice: APPLIED (ψ₂ in step 1; one sentence in Notation).
12. minor, the elementary mean value in Appendix B: APPLIED.
13. minor, two meanings of "Jensen's inequality": APPLIED in both places.

## Figures

Three findings (lens 1 no. 11, lens 2 no. 2 and no. 22) prefer relabeled images to longer captions.
`review/_apply/relabel_figures.py` wrote `figures/cascade-relabeled.svg` and
`figures/cube-relabeled.svg`: text labels only, 13 and 8 exact replacements, geometry and plotted data
untouched; the two original files are still in `figures/`, byte-identical to the record's. Copies with
the font attribute the typesetting step uses (DejaVu Sans) are in `typst/figures/` under the same
two names. Both were rendered once through Typst and looked at: no label overflows or overlaps.
`paper.md` now points to the relabeled files, and each caption says that the image is the record's
with its text labels edited and the plotted data unchanged. To go back to the unedited images, point
the two image lines at `figures/cascade.svg` and `figures/cube.svg` and use the longer captions
proposed in `review/claims-and-framing.md`.

Label changes, Figure 1: title "First 400 nontrivial zeros of zeta, read through the MNF threshold
cascade" to "Normalized spacings of the first 400 nontrivial zeros of zeta"; "GUE sd 0.422" to
"surmise sd 0.422"; "verified by Euler-Maclaurin" to "(uncertified) ... re-located by
Euler-Maclaurin"; "A. Hidden (reservoir) mass below the threshold, h_D / sum s" to "A. Fraction of
the total spacing length in spacings below x"; "reservoir empty up to D = 0.243:" to "no spacing below
0.243:"; D to x on the axis and in the inset; "Trace delta* = max s = 2.201." and "Hover the dots and
bars for the counts." removed. Figure 2: title to "Ordered pairs of the first 400 nontrivial zeros of
zeta"; "All 400 zeros ... are simple and on the line" to "Uncertified computation: all 400 zeros found
simple and on the line ..."; "A. The cube ... and its support under RH" to "A. Schematic of the
coordinates; the data lie on the s axis"; "(the 0.0e zone)" removed; "empty under the gap hypothesis
(open)" to "empty iff the gap hypothesis holds (unproved)"; "reservoir |delta| >= Delta: O(T^(1-c))
zeros, proved" to "|delta| >= Delta: O(T^(1-c)) zeros up to height T (Carlson 1920)"; "7/8 face
|delta| >= 3/8" to "|delta| > 3/8: no zeros (OpenAI's 7/8 theorem)".

## For the author to decide

1. DOI. The sentence in Availability no longer carries a placeholder. If a DOI is reserved in the Zenodo form before the PDF is built, print it there.
2. Date line. "2026-11-11 (UTC)" is the date of this revision; replace it by the deposit date if that differs.
3. The relabeled figures (above): keep them, or return to the record's images with longer captions.
4. Two sentences the reviewers offered "if true", not added: "No mathematician other than the author has reviewed the Lean files or this text." and "The author has no affiliation with OpenAI or Anthropic."
5. The repository, not touched by this step: README header ("seventeen artifacts, eight receipts") and its `sources/` list are stale; `zenodo-metadata.json` describes runs 1 to 6 only and says "every definition compared by body" for run 3; write new Zenodo metadata for the paper. After the push, re-run `verify_deposit.sh` and, if the paper should name the new commit, change `f03aaa9` and the count of 27 listed files in "Verifying the record offline".
6. Corrections the paper now makes to the record, which the README or the register may want to repeat: the three `Cube.lean` equivalences are [PROVED | this tree], not [PROVED]; the reports' "N definitions ... all compared by name, type and body" counts `def` lines; "GUE 0.4221" in `numeric/RESULTS.md` is a typed constant; the "first kernel-checked zero-density estimate" wording in two strip notes does not hold; Ingham 1940 is pages 291–292.
7. "The text of this paper is under CC BY 4.0" still rests on the section brief, not on a file of the record (carried over from the assembly notes).

## Web pages opened for this step (bibliography and registry facts only)

- api.crossref.org: the record of DOI 10.1093/qmath/os-11.1.201 (pages "201-202") and the list of the 1940 volume of The Quarterly Journal of Mathematics.
- api.zbmath.org: Zbl 0025.02704 (Ingham, "Q. J. Math., Oxf. Ser. 11, 291-292 (1940)"); JFM 45.0716.03 (Bohr and Landau, Palermo Rend. 37, 269-272 (1914), review); JFM 50.0230.02 (Littlewood 1924, review).
- arxiv.org/abs/2501.16779 (Tao, Trudgian, Yang; 28 January 2025).
- data.palomar-registry.org, entry PALOMAR-2026-09-23-000001 (Fiori).
- raw.githubusercontent.com: Comparator's README at tag v4.34.0 and on its default branch; `comparator.json`, `Challenge.lean` and `Solution.lean` of mrklwk/zeta-density-39-over-17-lean at commit `ee2a8a32…` (copies in the scratch folder `applycheck_dl`, beside WORK).
- api.github.com: the commit list of the goldbach-lean file and the repository's description.
No request carried anything about the author or the record.

## Final round

Applied 2026-11-11 UTC (2026-11-10 local). 29 findings from the two final reviewers (3 major, 26
minor), numbered here in the order of their JSON list. Each was checked against the files it cites
before any edit. Result: 28 APPLIED (12 as proposed, 11 narrowed or extended after the check, 5 in
part because the rest needs the author or a change in the repository), 1 NOT APPLIED because only
the author can supply its facts, 0 REJECTED. No Lean statement was touched: the 18 code blocks are
byte-identical to the drafts and `check_lean.py` finds every statement in the receipts or sources.

How the edits were made: exact-string replacements that stop if an anchor is missing or ambiguous
(`review/_finalround/apply_final_1.py` to `apply_final_4.py`; 41 replacements, then 5 and 1 made on
re-reading). The paper before this round is `review/_finalround/paper.before-final.md`.
After editing, `review/_assemble/check.py` reports RESULT: OK (39 keys cited and 39 reference
entries, 47 cross-references to 25 existing headings, Appendix A and the table of runs 3 to 6 equal
to `facts/runs.md`). Words: 16142 before, 18393 after. One fact sheet was extended:
`facts/method.md` has an addendum with the five commit hashes and trailers read from `git log`
(the checker requires every hash printed in the paper to be in a fact sheet). Nothing outside WORK
was modified; `git status` in the repository is clean.

1. major, ACCEPTED presented as a status above PROVISIONAL: APPLIED, extended. `receipt.py` lines 12 to 14, 267 to 273 and 425 and `PROTOCOL.md` lines 189 to 194 say what the finding quotes; `z23_density.sh` of add-on v6 lines 87 to 93 and 107 and `z23_mnf.sh` line 82 launch with `--run-type warm`. The paragraph of *Cold and warm runs* was replaced by two paragraphs with the proposed content, and the Introduction, the sentence on what the nine acceptances rest on, Limitations and *What would strengthen the work* were changed as proposed. Three departures: (a) the facts of every one of runs 7 to 11 also record run 6's five modules as compiled earlier ("density_b2_files ... warm for Core, Gap, Hypotheses, Counting, Zeta23Restated"), so the text says "runs 7 to 11", not "runs 8 to 11", for modules of this work compiled by earlier runs; (b) the README's own sentence on the library runs ("warm with respect to the external proof files by design") is quoted as further support for runs 3 to 5, whose bundles record no run type; (c) "made after run 1 had found ... unchanged" became "made after run 1's receipt had recorded ... as unchanged and after the launch script had verified the checkout again" (`mnf_prepare.sh` requires phase 7 and calls `verify_oai_tree` before the copy). "At the cost of the two hours of run 1" became "at the cost of compiling OpenAI's proof again (1 h 54 min 37 s in run 1)".
2. major, "The record names no model version": APPLIED, narrowed. `git log` shows the trailer "Co-Authored-By: Claude Fable 5.1" on the four commits 397563f, 81b9ac3, 6acc735, fa7e30a and "Co-Authored-By: Claude Fable 5.2" on f03aaa9; a search of the files finds only scratch paths. The proposed sentence "A trailer names the model of the session that prepared the commit" rests on no file and became "A trailer is attached to a commit, not to a file". The optional sentence on the model that wrote the paper's text is the author's to add.
3. major, checks before and after the run: APPLIED as proposed. Run 11's `facts.tsv` has `trusted_files_after`, `deps_after`, `dep_lakefiles_after`, `tools_after`, `addon_after` once (run 2) and only `mnf_files_after` / `density_files_after` for runs 6 to 11; `nanoda_bin_sha256_*` five times with run 2's value; the facts of runs 3 to 5 have no check after the run; the scripts agree (`z23_density.sh` lines 39 to 57, `z23_density_report.sh` lines 35 to 38, `z23_mnf.sh` lines 35 to 53, `z23_mnf_report.sh` lines 36 to 38, `mnf_prepare.sh`).
4. minor, the receipted runs were not first attempts: APPLIED, narrowed and extended. Line 105 now reads "Every Comparator launch of the eleven runs and of the controls". A paragraph was added to *Cold and warm runs* and one sentence to Limitations. "The eleven runs are not first attempts" was not taken over: the files show earlier acceptances for runs 2, 4, 5 and 7 to 11 and say nothing for runs 1, 3 and 6, so the text says "Most of the receipted runs". Added from the files: the README of the zeta23 add-on reports a dry run before run 2 (17 statements accepted on the author's account; its files are not in the record). For runs 7 to 11 the text follows the README of each add-on ("warm pre-check, outside the launcher") and the five dry-run reports in the notes, each ending ACCEPTED before the receipted run started. "The record holds no receipted run that ended REJECTED" is qualified by the fifteen controls that were rejected as intended.
5. minor, the mirrors compare the library with a copy of itself; the challenge files of runs 6 to 11: APPLIED, extended. Checked here: the 21 generated files of `notes/density-field-2026-11-03/zeta23-tree/` have the sha256 values of run 11's listing; no add-on tarball and no bundle of runs 6 to 11 contains a challenge `.lean` file. Extended: the generator of each add-on was run in a scratch copy on that add-on's sources for every one of runs 6 to 11, and every generated file has the sha256 of the receipt's listing (`review/_finalround/regen.log`); the paper says so in one sentence, since that replaces "a reader has to regenerate them" by a check that was made. The sentence on what the verifier establishes was narrowed: `verify_deposit.sh` checks theorem counts only for runs 2 and 7 to 11.
6. minor, the counts are `∑ᶠ` sums: APPLIED. `Counting.lean` line 57 and its header ("would be vacuously 0 on an infinite set"); `zerosIn_finite` has an axiom report in the `audit.out` of runs 5 and 6 and in none of runs 3, 4, 7 to 11; the docstring quoted is in zeta23's `Challenge.lean` as printed in run 2's receipt. "Replayed as a dependency of the claimed theorems" became "the claimed proofs that use it depend on it, and the kernel replay covers what the claimed proofs depend on".
7. minor, two equivalences or three: APPLIED as proposed (body and Appendix B).
8. minor, "hand-written block": APPLIED as proposed (`mnf_check.py` line 182, `z23_mnf_check.py` line 184, `z23_density_check.py` line 185 write the block).
9. minor, the four supporting files: APPLIED. NOTICE lines 52 to 54. In the abstract the insertion carries no cross-reference (an abstract is read alone): "(apart from four supporting files, which the author supplied)".
10. minor, the corpus and Aristotle: APPLIED, narrowed. DEPOSIT_MAP lines 160 to 182 and the header of `SimpleEigenvalues.lean` say what the finding quotes; no file of the corpus is in the repository. "Aristotle's part in the corpus is therefore not limited to that one file" became "These names suggest that ...", since file names are the only evidence.
11. minor, "quoted from memory": APPLIED, narrowed. `rs_zeros.py` line 347 prints "LMFDB/Odlyzko values as recalled"; NOTICE says the code was written with Claude Code. The text states those two facts and that the values were not read from the tables for this work, without saying whose recall it was.
12. minor, GUE, Wigner surmise, Poisson, Lean FRO: APPLIED IN PART. "Gaussian unitary ensemble (GUE) of random matrix theory" was added at the first use; this expansion of the acronym is standard terminology and is in no file of the record. The Wigner surmise and the Poisson law are now given by the formulas of the record (`mnf_analysis.py` line 28, `RESULTS.md`: $(32/\pi^2)s^2e^{-4s^2/\pi}$ and $e^{-s}$) and not by the proposed glosses "two-by-two approximation" and "independent points", which no file gives. "Lean FRO" is not expanded: no file read gives the expansion (for the author).
13. minor, statements of the record that the paper contradicts in silence: APPLIED IN PART. Items (a) to (d) are in a new erratum, with the reports quoted exactly ("says a gap at Δ ≤ 3/8 cannot give it"); the Lean statement of `gap_below_bound_insufficient` is about a set `S ⊆ Set.Ioo (-b) b`. Item (e), the README header "seventeen artifacts, eight receipts", its `sources/` list and `zenodo-metadata.json`, is in the repository and was not touched (for the author).
14. minor, three senses of "reservoir": APPLIED. `Density.lean` lines 66 to 67 and 166, `ReservoirMass.lean` lines 19 to 21, `Cube.lean` line 114. The sentence stands at the end of its paragraph, so that "the first" and "the second" stay together.
15. minor, Availability: APPLIED IN PART. The full commit hash is printed; "its DOI is on the Zenodo record page" was deleted; three sentences say what the record itself says about a "Zenodo record of 2026-10-29" (DEPOSIT_MAP line 24, NOTICE line 1, the notes field of `zenodo-metadata.json`) and that no file gives a DOI for it. Whether a snapshot of the record is archived, the DOI of this paper and the status of the earlier Zenodo record are the author's to state.
16. minor, further acceptances and `BRIDGE.md`: APPLIED, narrowed to quotations. DEPOSIT_MAP line 279 ("also ACCEPTED at the OpenAI pin on 2026-11-03"), README line 176 ("accepted again on 2026-11-03, Lean kernel and NanoDa"), `BRIDGE.md` ("it is not a second Comparator run"), DEPOSIT_MAP lines 67 to 68 (same content as the second bridge file; the text says so for runs 3 to 5, the runs that judged `Unconditional.lean`).
17. minor, what "operated" covers: APPLIED, narrowed. Every add-on and the kit ship a `CLAUDE.md`. The READMEs of the kit and of the three MNF add-ons describe the run through a Claude Code session; only the six zeta23 add-ons give the commands and add "Or give Claude Code the prompt ...". The proposed "the README files offer that route beside the commands typed by hand" was worded accordingly. A pointer was added to the sentence "One operator made all eleven runs" in Limitations.
18. minor, "presumably earlier": APPLIED as proposed. `diff` of the two pins files prints only `56a57,62`, the block of step B2.
19. minor, two caveats on the external artifacts: APPLIED as proposed (`PROTOCOL.md` lines 17 to 18; README lines 170 to 172, quoted).
20. minor, the constants in the abstract: APPLIED as proposed (statement of `two_thirds_simple_on_critical_line` in run 2's receipt).
21. minor, tooltips inside the relabeled figures: APPLIED IN PART. `review/_finalround/relabel_tooltips.py` rewrote 21 tooltips of Figure 1 and 3 of Figure 2 in `figures/` and in `typst/figures/` with the wording of the visible labels; everything outside `<title>` elements is byte-identical before and after (checked by the script), and the unedited images are still identical to the record's. Not done here: looking at the two crowded labels in the final PDF, and depositing the relabeling scripts and images (for the typesetting step and the author).
22. minor, the recomputed value 0.4243: APPLIED IN PART. The script `review/_mathexp/gue_sd.py` was run again (0.42426, surmise 0.42202). It cannot be added to the record from here, so the number stays with one more clause: "the script of that recomputation is not in the record at the commit cited in *Availability*". The author can deposit the script and change the clause, or drop the number.
23. minor, affiliation, funding, competing interests, human review: NOT APPLIED. No file establishes any of the proposed sentences; they are the author's to add if true.
24. minor, Appendix A, run 1, "none listed": APPLIED ("no count given"). `facts/runs.md` keeps its own wording for that cell; the checker does not compare it for runs 1 and 2.
25. minor, run 1 left out of the sentence on holes: APPLIED, narrowed. The nine-line challenge file defines nothing; "mentions only Mathlib's `riemannZeta`" became "uses only what Mathlib provides, the function `riemannZeta` included", and one clause says that OpenAI's configuration is pinned by sha256 and not copied into the bundle (so nothing is said about its hole list).
26. minor, acknowledgments: APPLIED as proposed.
27. minor, the leading `@`: APPLIED as proposed. In run 11's `audit.out` all 279 statements with `@` begin with `∀ {` and none of the 255 others does; 29 of those have a later implicit binder.
28. minor, the proof of `rightHalf_all`: APPLIED as proposed (`BohrLandauClosure.lean` lines 1209 to 1219).
29. minor, gloss of [RESTATEMENT | zeta23] in Appendix B: APPLIED as proposed (`Density.lean` lines 180 and 188 to 190; `Zeta23/Superlinear.lean` line 24; `Zeta23/OffLine.lean` line 41).

### For the author to decide (final round)

1. Which model produced the text of the paper, if the author wants it named (finding 2). The repository's commit trailers name Claude Fable 5.1 and 5.2; no file says which model wrote which file.
2. The expansion of "Lean FRO" (finding 12), and whether to keep the expansion of GUE as written.
3. The sentences of finding 23, each only if true: no affiliation with OpenAI, Anthropic, Harmonic or the Lean FRO and no funding; no person other than the author has reviewed the Lean statements, the mathematics or the text.
4. Zenodo (finding 15): the paper's DOI if reserved before the PDF is built; whether a snapshot of the record at the cited commit is deposited with the paper; whether the "Zenodo record of 2026-10-29" was published, and its DOI.
5. The push. Availability and *Verifying the record offline* name commit `f03aaa9` (full hash in Availability) and 27 listed files. If the push adds a commit, re-run `verify_deposit.sh` and change the hash and the count; the erratum on 0.4243 also refers to "the commit cited in *Availability*".
6. The repository, not touched here: README header ("seventeen artifacts, eight receipts"), its `sources/` list and `zenodo-metadata.json` are stale; the README says both authors report Comparator runs of their own; the register calls runs 7 to 11 cold with "every definition compared by body", the gap hypothesis "insufficient for every Δ ≤ 3/8" and the threshold "exact", and tags the three `Cube.lean` statements [PROVED]; README and register attribute the mean square to Hardy and Littlewood. The paper now says where it departs from each.
7. Files that could go into the record's notes so that the paper's statements can be reproduced from it: `review/_mathexp/gue_sd.py` (finding 22), `review/_apply/relabel_figures.py` and `review/_finalround/relabel_tooltips.py` with the two relabeled images (finding 21), `review/_finalround/regen.log` (finding 5), and the dry-run folder of run 2 that the add-on's README mentions (finding 4).
8. Figures: two crowded labels to look at in the final PDF (the three subtitle lines of panel B in Figure 2; "no spacing below 0.243:" in Figure 1).
9. Finding 1 is answered in the text, not by a run: a cold run of the complete layer (and of the library on OpenAI's tree) would remove the warm status; the paper lists it under *What would strengthen the work*.
10. Seen while checking, outside the 29 findings and not put in the paper: `notes/density-field-2026-11-03/aristotle/` holds a prompt and a target file of 11 theorems, each with `sorry` for its proof, prepared for Aristotle (Harmonic) on 2026-11-03, and `plan/BOHR_LANDAU_CLOSURE.md` says that the agents' workflow "proved the chain that the Aristotle target file ... laid out" and that "The Aristotle package is superseded". The authorship section does not mention this; one sentence could.
