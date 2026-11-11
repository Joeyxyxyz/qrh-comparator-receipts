# Final referee report on WORK/paper.md

Referee pass of 2026-11-11 UTC (2026-11-10 local), first reading of `paper.md` (670 lines, 16,142 words) from the first line to the last, against REPO at commit `f03aaa9d9f461e5ba7540a848db736de73f32018` (clean working tree) and the eleven bundles under `WORK/extracted/`. Nothing outside WORK was modified; temporary extractions made in the scratch area were removed. Abbreviations: PAPER = `WORK/paper.md` (line numbers are those of the file), REPO = the record, KIT = `REPO/sources/qrh-comparator-kit`, V6 = `REPO/sources/qrh-zeta23-addon-v6`, NOTES = `REPO/notes/density-field-2026-11-03`, EXT = `WORK/extracted`.

## Verdict

Publishable after revision. No statement about the mathematics, no verdict, no hash, time, count or Lean statement that was checked against the receipts was found wrong, and the paper's non-claims (not RH, not simplicity, not a zero-free strip, not a first verification, classical results with weaker bounds, relocation only) are stated wherever they are needed and nowhere contradicted. Three statements about the protocol and about authorship are false or unsupported as written and should be corrected before the deposit (M1 to M3). Twenty-three smaller points follow (m1 to m23); most ask for a sentence the paper should contain and does not.

## What was checked and found to agree

- All 17 fenced Lean blocks (24 statements or definitions): each is in a receipt (`MNF_LIBRARY.md`, `MNF_ZETA23.md`, `MNF_DENSITY.md` or `audit.out`) or in a source file of the add-ons, character for character up to white space (`review/_final/blocks.py`).
- Appendix A and the table of runs 3 to 6: start and end stamps, wall clocks, exit codes, run types, theorem and definition counts, kernels (acceptance lines of the Lean kernel in all eleven logs, of NanoDa in runs 2 and 6 to 11), and all 21 eight-digit hashes against `CHECKSUMS.sha256`.
- One boot identifier (`03b05777-…`) in the facts of all eleven runs; AF_UNIX denied in all eleven jobs; probes recorded for runs 1, 2 and 6 to 11 and not for runs 3 to 5, as the paper says.
- Controls: 21 projects, 6 accepted and 15 rejected, 17:31:27Z to 17:32:07Z on 2026-10-27, eleven minutes before run 1; four NanoDa projects skipped.
- `verify_deposit.sh` run again at `f03aaa9` for this report (temporary files in the scratch area): every line `ok`, `VERIFY=OK`, both upstream statement files fetched and equal to the pins.
- Theorem counts per module (4+19+19+56+12+9+5 = 124; +139+7 = 270; +64 = 334; +38+108 = 480; +54 = 534); 279 of 534 statements printed with a leading `@` in run 11; every one of the 534 axiom reports within the three axioms; no `sorryAx`.
- The English readings of the quoted statements against the definitions in V6 (`nullify`, `SpectralGapProperty`, `NOff`, `NRight`, `NOffLine`, `N0`, `reservoirMass`, `Degenerate`, `OrdinatesInjectiveOn`, `bandZeros`, `pairSum`, `offDiagonalCoincidentMass`, `bandCoincidentMass`); real exponents where the paper says "a real power" (`(3:ℝ)/5`, `-(5/2 : ℝ)`); the arithmetic of the exponent comparisons (5/6 against 3/4, the factor 1/(2σ₁), the window σ₁ ≥ 2/3, the constant 5/9, the counterexample 10 against 8, the split at (log T)^(-2/5)).
- The numbers of the numerical section against `NOTES/numeric/RESULTS.md` and `CUBE_NUMERIC.md`.
- The unpacked copies under `REPO/sources/` against their manifests (all nine add-ons and the kit: no mismatch), and V6 against its tarball (identical).
- Two checks the paper does not report and could: the copy of run 11's challenge in `NOTES/zeta23-tree/MNFChallengesD/` (19 modules, `Density.json`) and `MNF_AuditDensity.lean` have exactly the sha256 values of the receipt's listing; and running V6's generator on V6's sources in an empty folder reproduces the same 21 files and a configuration with 534 theorem names, no definition holes, the three axioms and NanoDa enabled (see m2).

## Major findings

### M1. "Runs 3 to 11 are a different case": the status of ACCEPTED is put higher than the kit's own rule allows

- Location: PAPER line 113 (*Cold and warm runs*): "Runs 3 to 11 are a different case, new files judged on a tree whose upstream part an accepted run had compiled; their reports say ACCEPTED, and this paper keeps the two words apart."; line 115: "For everything upstream these nine acceptances rest on the two cold runs."; line 23 (Introduction): "Runs 3 to 11 reuse compiled files of the verified trees and report ACCEPTED; the protocol reserves PASS for runs in which nothing of the challenge or the proof was compiled beforehand, and this paper keeps the two words apart."; line 469 (*Limitations*): "Runs 3 to 11 reuse the compiled trees of runs 1 and 2 and are reported as ACCEPTED, the kit's protocol reserving PASS for cold runs."; line 552 (Appendix A): "Each of runs 8 to 11 re-judges the layer of the previous run together with the new modules."
- Problem: the paragraph first gives the kit's rule (a warm acceptance is PROVISIONAL, "because a hostile proof compiled earlier could have prepared the ground") and then exempts runs 3 to 11 from it without a reason. The kit's documents do not exempt them. (a) ACCEPTED is not a verdict of the kit: its verdicts are PASS, PROVISIONAL, INVALID, REJECTED, ERROR, INCOMPLETE. In the kit ACCEPTED is the outcome of an attempt (Comparator said yes), from which the verdict is then derived: INVALID if a condition failed, PROVISIONAL if the run type is warm, PASS otherwise. The add-ons' report scripts use the outcome word as their result. Runs 6 to 11 were launched with `--run-type warm`, so the kit's own derivation would have given them PROVISIONAL. (b) The kit classifies exactly this situation, a further statement judged in the tree after the accepted main run, as warm. (c) For warm runs the protocol says that none of the exposures is closed. (d) In runs 8 to 11 the warm part is not only "upstream": the modules of the earlier layer runs were already compiled in the tree. A reader comes away believing that ACCEPTED is a status between PASS and PROVISIONAL; the record supports only that it is the add-ons' name for an acceptance in a run the kit would call warm.
- Evidence: `KIT/scripts/receipt.py` lines 12 to 14: "PASS  Comparator accepted in a cold run and every condition of the protocol held." / "PROVISIONAL  Comparator accepted in a warm run (files compiled by an earlier attempt were reused). Informative, not a certification."; lines 255 and 267 to 273 (`warm = run_type == "warm"`; `elif warm: verdict, reason = "PROVISIONAL", "Comparator accepted, in a warm run. That is not a certification"`); line 425, on the optional second statement of OpenAI's repository: "This is always a warm run (it reuses the proof files the main run compiled), so it can be PROVISIONAL at best."; `KIT/docs/PROTOCOL.md` lines 189 to 194: "A hostile proof could have used that to prepare the ground for the next run: a doctored compiled challenge, altered compiled dependencies, a planted program or library in a directory that `lake env` puts on the search paths, or changes to a dependency's build configuration, all of which the next run would pick up outside the sandbox. The kit closes none of these for warm runs; it only labels the result."; `EXT/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`, 2026-11-11T00:02:36Z: `density_v2_files  compiled earlier in this tree (v2-v5 runs):` followed by fifteen module names; `V6/scripts/z23_density.sh` lines 87 to 91: only `MNF/RH/Cube` and `MNFChallengesD/Cube` must be uncompiled, and line 107: `run_comparator.sh … --run-type warm`; `REPO/sources/qrh-zeta23-addon/README.md` lines 62 to 64: "The run is warm with respect to the Zeta23 library by design".
- Replacement for PAPER lines 113 (from "Runs 1 and 2 are cold") and 115 (last sentence):

  "Runs 1 and 2 are cold and carry the verdict PASS. Runs 3 to 11 judge new files on a tree in which an earlier run had already compiled the upstream proof. Their reports say ACCEPTED. In the kit that word names the outcome of an attempt, from which a verdict is derived; the add-ons use it as their result, and it is not a verdict of the kit. By the kit's own rule these runs are warm: its receipt generator says of a second statement judged on OpenAI's tree after the main run that it "reuses the proof files the main run compiled", so that "it can be PROVISIONAL at best", and of the ways in which files compiled earlier could prepare the ground the protocol says: "The kit closes none of these for warm runs; it only labels the result." With respect to everything compiled before the run, ACCEPTED therefore certifies no more than the kit's PROVISIONAL would, and this paper keeps it apart from PASS for that reason. What limits the exposure is recorded run by run. Runs 3 to 5 each start from a fresh copy of run 1's compiled tree, made after run 1 had found its trusted inputs, proof sources and checker binaries unchanged and after the checkout had been verified again, and compile only the add-on's modules; their bundles record no run type. Runs 6 to 11 work in run 2's checkout and are recorded as warm; each is cold only for the modules its add-on introduces, which the launch script enforces. In runs 8 to 11 the modules of the earlier layer runs were therefore already compiled in the tree (run 11 records fifteen of them, and its script requires only `Cube` and its mirror to be uncompiled); Comparator still exported, and both kernels replayed, every claimed theorem with all it depends on. (The record's register calls runs 7 to 11 "cold"; the receipts are followed here.)"

  and, for the last sentence of line 115: "For everything compiled before them, the upstream libraries and in runs 8 to 11 the earlier modules of the layer, these nine acceptances rest on the runs that compiled it."
- Replacement for line 23: "Runs 3 to 11 reuse compiled files of the verified trees and report ACCEPTED, the add-ons' word; the kit's protocol reserves PASS for runs in which nothing of the challenge or the proof was compiled beforehand and would call these runs warm (see *Cold and warm runs*). This paper keeps the two words apart."
- Replacement for line 469: "Runs 3 to 11 reuse the compiled trees of runs 1 and 2, and runs 8 to 11 also the layer modules compiled by the runs before them; they are reported as ACCEPTED, and under the kit's protocol, which reserves PASS for cold runs, they are warm runs, for which the kit closes none of the exposures it lists."
- Addition to *What would strengthen the work* (line 483): "A cold run of the complete layer, on a fresh checkout in which Comparator compiles the zeta23 library and the layer together, would remove the warm status of runs 6 to 11; the same holds for the library on OpenAI's tree, at the cost of the two hours of run 1." (The cost for the zeta23 tree is not recorded; runs 2 and 11 took 21 and 15 minutes.)

### M2. "The record names no model version." is false for the public repository

- Location: PAPER line 522 (*Authorship and use of AI tools*), last sentence of the paragraph.
- Problem: the paper defines the record as the public repository. Every commit of that repository carries a trailer that names a model. An authorship statement that a reader can refute with `git log` damages the section that most needs to be exact.
- Evidence: `git log` in REPO: commits `397563f`, `81b9ac3`, `6acc735`, `fa7e30a` end with "Co-Authored-By: Claude Fable 5.1" and commit `f03aaa9` (run 11) with "Co-Authored-By: Claude Fable 5.2". No file of the record names a model (grep of REPO for model names: only scratch paths match).
- Replacement: "The files of the record name no model version. The commit messages of the repository do: the four commits up to run 10 carry the trailer "Co-Authored-By: Claude Fable 5.1", and the commit of run 11 "Co-Authored-By: Claude Fable 5.2". A trailer names the model of the session that prepared the commit; the record does not say which model wrote which Lean file." If the author knows which model produced the text of the paper, one more sentence should say so.

### M3. The after-run checks are described for nine runs but were made in full only for two

- Location: PAPER line 119 (*Receipts and the verifier*): "Artifacts, tools and toolchains are pinned by commit or sha256 and checked before the run and, except in runs 3 to 5, again after it".
- Problem: for runs 6 to 11 no check of tools or toolchains after the run is recorded, and none before it either: the launch scripts check the add-on's manifest and five files of the zeta23 checkout, and the report scripts re-check the hashed layer files and three statement files. The checker binaries and the toolchain were hashed for run 2 only (the NanoDa binary's hash is recorded again before each of runs 7 to 11 and is the same). The sentence credits six runs with a protection the receipts do not show.
- Evidence: `EXT/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`: `trusted_files_after`, `deps_after`, `dep_lakefiles_after`, `tools_after`, `addon_after` occur once, at 2026-10-28T11:30 (run 2); for runs 6 to 11 the only after-run facts are `mnf_files_after unchanged` and `density_files_after unchanged`; `lean_toolchain_verified`, `comparator_sha256`, `landrun_sha256` occur once, on 2026-10-28; `nanoda_bin_sha256_zeta23-density*` (five entries, `d883b313…`, equal to run 2's `nanoda_sha256`). `V6/scripts/z23_density.sh` lines 39 to 57 (manifest; `Challenge.lean`, `ChallengeDeps.lean`, the configuration, `lake-manifest.json`, `lean-toolchain`); `V6/scripts/z23_density_report.sh` lines 35 to 38 (the listing `density_sha256.txt` and three statement files); `REPO/sources/qrh-zeta23-addon/scripts/z23_mnf.sh` line 52 and `z23_mnf_report.sh` lines 36 to 38 (the same for run 6); `REPO/sources/qrh-mnf-addon-v3/scripts/mnf_prepare.sh` lines 43 to 54 (manifest, `verify_oai_tree`; nothing after the run); `EXT/qrh-receipt/receipt/RECEIPT.md`, row "After the run".
- Replacement: "Artifacts, tools and toolchains are pinned by commit or sha256. Runs 1 and 2 checked them before the run and again after it (run 1: checkout, trusted inputs, proof sources, checker binaries and kit; run 2: trusted files, compiled dependencies, their build configuration, tools and add-on). The later runs checked less. Runs 3 to 5 verified OpenAI's checkout and the add-on's manifest before the run and recorded no check after it. Runs 6 to 11 checked, before the run, the add-on's manifest and five pinned files of the zeta23 checkout (the two statement files, the configuration, the dependency manifest and the toolchain file) and, after it, the hashed files of the layer (sources, mirrors, configuration, audit file, lakefile) and the three statement files; the checker and toolchain binaries were not hashed again after run 2, except that runs 7 to 11 each record the hash of the NanoDa binary, the same as in run 2. The kit and each add-on are checked against their own manifests."

## Minor findings

### m1. The eleven runs were not first attempts, and one sentence is too wide

- Location: PAPER line 105: "Every Comparator launch, controls included, goes through one script"; lines 131 to 135 (pre-checks mentioned only as sources of three lessons); line 506: "The instructions state: "A REJECTED result is a real result.""; *Limitations*.
- Problem: the record shows a systematic practice that the paper mentions only in passing: before a receipted run the same configuration had been accepted by Comparator on the author's own account, outside the launcher, and for runs 7 to 11 the add-on had also been run there as a dry run. The receipted runs repeated outcomes already seen; every recorded failure happened in a pre-check. Quoting "A REJECTED result is a real result" without this lets a reader take the eleven verdicts for eleven first tests. Line 105 is literally false for the pre-checks.
- Evidence: `NOTES/DENSITY_LEDGER.md` lines 5 to 9 ("warm run on the author's account, outside the QRH launcher; this is a pre-check, not a receipt"), the addenda for v3 ("dry run on the author's account ACCEPTED (`dryrun-v3/`)"), v4 (`comparator-precheck-v4.log`), v5 ("Comparator pre-check of the whole layer, 480 theorems and 98 definitions, accepted with both kernels"; "Dry run on the author's account (`dryrun-v5/`): MNF_DENSITY=ACCEPTED"), v6 ("Comparator pre-check, 534 theorems and 110 definitions, accepted with both kernels"; "first attempt failed because the generator kept the two `aux_` lemmas"; "dry run on the author's account (`dryrun-v6/`): MNF_DENSITY=ACCEPTED, 2026-11-04T18:54:22Z–19:09:39Z"); `REPO/sources/qrh-mnf-addon-v2/README.md` lines 108 to 112 and `qrh-mnf-addon-v3/README.md` lines 144 to 146 ("judged by a locally built Comparator … outside the kit's systemd unit; that pre-check is not the receipt"); `V6/README.md` lines 66 to 68; logs in NOTES: `comparator-precheck.log`, `comparator-precheck-124.log`, `comparator-precheck-v4.log`, `reservoir/comparator-precheck-v5.log`, `strip/comparator-precheck-v6.log`, `cube/comparator-precheck-v7.log`, `cube/comparator-precheck-v7-attempt1-failed.log`, folders `dryrun` to `dryrun-v6`.
- Replacement for line 105: "Every Comparator launch of the eleven runs and of the controls goes through one script, …".
- Addition to *Cold and warm runs* or *Limitations*: "The eleven runs are not first attempts. Before runs 4 and 5 the statements that need only Mathlib were judged by a locally built Comparator on the author's own account, outside the launcher; before each of runs 7 to 11 the whole configuration had been accepted there, in a pre-check, in a dry run of the add-on, or in both (working log and README files of the add-ons; the pre-check logs and the dry-run reports are in the notes). A receipted run thus repeated, under the launcher and in the tree of run 1 or run 2, an outcome already seen, and the failures recorded in *Lessons learned* all occurred in pre-checks. The record holds no receipted run that ended REJECTED."

### m2. The challenge of runs 3 to 11 is a copy of the solution; and where a reader can read it

- Location: PAPER line 127 (*Challenges as module-for-module mirrors*); line 500 (*Verifying the record offline*).
- Problem: the Introduction motivates Comparator by a short statement file that a reader can read. For runs 3 to 11 the statement files are generated from the solution's own sources, so the comparison of statements compares the library with a copy of itself and cannot detect a wrong or vacuous statement; the paper describes the mirrors and does not draw this consequence. Also, the challenge files of runs 6 to 11, the statements actually judged, are in no bundle and no add-on tarball, and the paper does not say where they can be read.
- Evidence: `V6/scripts/z23_gen_density_challenge.py` (mirror = source module with non-Mathlib imports replaced or dropped and proofs replaced by `sorry`); `verify_deposit.sh` lines 84 to 87 ("the challenge mirrors, the audit file and lakefile.toml are generated or modified in the tree and are not shipped"); `REPO/sources/qrh-zeta23-addon/MNFChallenges/` holds only `theorem_list.txt`. Checked for this report: the files in `NOTES/zeta23-tree/MNFChallengesD/` and `NOTES/zeta23-tree/MNF_AuditDensity.lean` match all 21 corresponding lines of `EXT/qrh-zeta23-density-v6-receipt/density-v6/density_sha256.txt`; the generator run on V6's sources reproduces the same 21 files. The listings of runs 7 to 10 match none of the files in that folder; each mirror begins with a header line that names the generator's version, which may be the whole difference (not examined).
- Addition at the end of line 127: "Two consequences follow. First, the challenge of runs 3 to 11 is derived mechanically from the solution's own sources, so the comparison of statements in these runs compares the library with a copy of itself: it cannot detect a statement that is wrong or vacuous. What these runs add to an ordinary build is the sandboxed compile, the fact that every definition used by a claimed statement is defined in the mirror modules, which import nothing but Mathlib and one another, the axiom check and the kernel replay. Second, the challenge files of runs 6 to 11 are in no bundle and in no add-on tarball. Those of run 11 can be read in `notes/density-field-2026-11-03/zeta23-tree/MNFChallengesD/`; that copy has the sha256 values of the receipt's listing, and the generator of add-on v6, run on its sources, reproduces the same files (both checked while this paper was reviewed). For runs 6 to 10 a reader has to regenerate them with the generator of the add-on concerned and compare with the receipt's listing; the verifier does not do this."
- Replacement in line 500: "the second, that the bundles carry the verdicts and theorem counts reported here and that the judged Lean sources of runs 3 to 5 and 7 to 11 are the published ones."

### m3. The counting functions are `∑ᶠ` sums; the paper never says where finiteness is proved

- Location: PAPER lines 50 to 60 (*Notation*).
- Problem: `Ncount`, `N0`, `NOff`, `NRight`, `NOffLine`, `reservoirMass` and `pairSum` are Mathlib finite sums `∑ᶠ`, which are 0 by convention on an infinite index set. Read without the finiteness of the zeros in a window, `BohrLandau` and every other upper bound for a count would be empty statements. The reading is correct, because finiteness is a judged theorem, but the paper does not say so, and a reader who knows Lean will look for it. The theorem is not in the claim set of runs 7 to 11.
- Evidence: `V6/MNF/RH/Counting.lean` line 57: `noncomputable def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ`; `MNF.RH.zerosIn_finite` has an axiom report in `EXT/qrh-mnf-v3-receipt/mnf-v3/audit.out` (run 5) and `EXT/qrh-zeta23-mnf-receipt/mnf/audit.out` (run 6) and none in run 11's `audit.out`; `ReservoirMass.lean` uses it (`finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)`); zeta23's `Challenge.lean`, docstring of `Ncount`, printed in `EXT/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`: "(`∑ᶠ` is Mathlib's finite sum; that the window contains finitely many zeros is proved on the solution side, not assumed)".
- Addition after the table: "In Lean each of these counts is a sum `∑ᶠ` over the zeros of the window, weighted by `zeta_order`, and Mathlib's `∑ᶠ` is 0 by convention when the index set is infinite. The reading as a count therefore needs the fact that a window contains finitely many zeros. That fact is `MNF.RH.zerosIn_finite`, judged in runs 5 and 6; in runs 7 to 11 it is not in the claim set and is replayed as a dependency of the claimed theorems. The statement file of zeta23 says of its own counting functions that finiteness "is proved on the solution side, not assumed"; it is not among the 17 statements of run 2."

### m4. "Two equivalences", three Lean statements

- Location: PAPER lines 9, 33, 413 ("two equivalences"), the code block at lines 417 to 424 (three statements), line 556 ("For the three equivalences of `Cube.lean`").
- Problem: the count changes between sections.
- Replacement for line 556: "For the three statements of `Cube.lean` that carry the two equivalences (the second in two forms)"; and at line 426, after "The first says …": "Lean prints three statements; the second and the third are two forms of one equivalence."

### m5. "a hand-written block"

- Location: PAPER line 119.
- Problem: the block is fixed text in the report generator, as lines 139 and 473 say ("fixed generator prose", "fixed prose of the report generator"); "hand-written" suggests a person wrote each report.
- Replacement: "… a table of axiom reports and a block of fixed prose, "How to read this", that the report generator carries, beside a sha256 listing of the files judged."

### m6. Blanket attribution of the layer's files in three places, exception only in the body

- Location: PAPER line 9 ("The layer's Lean files, parts of MNF.RH, the scripts and this text were produced with Claude Code"), line 42 ("The Lean files of runs 7 to 11, …"), line 522 ("the Lean files of runs 7 to 11 … were produced with Claude Code").
- Problem: lines 245 and 524 say, with `NOTICE`, that four supporting files of the layer were supplied by the author and that the record does not say which tool drafted them. The three sentences above state the attribution without the exception.
- Evidence: `REPO/NOTICE` lines 52 to 54: "Zeta23/Superlinear.lean, OffLine.lean, BohrLandau.lean, MNFBridge.lean: supplied by Joey Messina on 2026-11-03 (the file does not record which tool drafted them)".
- Replacement: insert "(four supporting files apart, which the author supplied; see *Authorship and use of AI tools*)" after "The layer's Lean files" in line 9, and "except four supporting files supplied by the author" after "The Lean files of runs 7 to 11" in lines 42 and 522.

### m7. The corpus: where it is, and what the record says about Aristotle's part in it

- Location: PAPER line 163 ("the author's earlier Lean collection (the "corpus")"); line 524 ("the record does not say which tool, if any, drafted them"); line 239.
- Problem: the paper withdraws five items "of the corpus" and never says what or where the corpus is. And the authorship paragraph limits Aristotle's part to one file, while the record indicates more.
- Evidence: `REPO/DEPOSIT_MAP.md` lines 160 to 182: "Of the 241 project documents, the RH line consolidated above is: … the aristotle stubs 1–3, and aristotle_stress_test_synthesis"; "Batch1–14 and MdBatch1–7 with their `_aristotle` variants"; "These belong to Zenodo Vol 1 (operator core) and Vol 3 (physical applications) and are outside this deposit"; header of `REPO/sources/qrh-mnf-addon-v3/SturmLiouville/SimpleEigenvalues.lean` lines 6 to 8: "Consolidated 2026-10-27 from the three corpus variants … (all Aristotle, Lean v4.24.0 / Mathlib f897ebcf, 2026-03-03)".
- Addition to line 524: "The corpus itself is not part of the record and was not examined for this paper; the register's inventory counts 241 documents and assigns the files outside the RH line to "Zenodo Vol 1 (operator core) and Vol 3 (physical applications)". That inventory lists "aristotle stubs" and an "aristotle_stress_test_synthesis" within the RH line and `_aristotle` variants outside it, and the header of the Sturm–Liouville file calls its three corpus variants "all Aristotle". Aristotle's part in the corpus is therefore not limited to that one file, and the record does not say which statements of the six consolidated files descend from such outputs."

### m8. "quoted from memory": whose memory

- Location: PAPER line 446.
- Problem: the comparison values were typed into the script from the coding agent's recall; the phrase as it stands can be read as the author's memory or as a quotation from the tables.
- Evidence: `NOTES/numeric/rs_zeros.py` line 347: "self-check against tabulated zeros (LMFDB/Odlyzko values as recalled)"; `RESULTS.md`, caveat 3: "The tabulated comparison values are quoted from memory of the standard tables".
- Replacement: "… with tabulated values (the public tables of Odlyzko and the LMFDB); the comparison values were typed into the script from the coding agent's recall and were not read from the tables for this work."

### m9. Abbreviations never expanded

- Location: PAPER line 41 (first "GUE"), line 448 ("Wigner surmise"), line 450 ("Poisson"), line 9 ("Lean FRO").
- Problem: GUE is used sixteen times and never expanded; "Wigner surmise" and "Poisson" are used as reference laws without a word of explanation.
- Replacement: line 41: "reproduce known behavior of the kind predicted by the Gaussian unitary ensemble (GUE) of random matrix theory"; line 448: "(Wigner surmise, the two-by-two approximation to the GUE spacing law: 0.4220)"; table header at line 450: "expected, Poisson (independent points)". "Lean FRO" should be expanded once if the author can confirm the expansion; no file read for this report gives it.

### m10. The errata do not list every statement of the record that the paper declines to repeat

- Location: PAPER lines 471 to 479 (*Errata*); line 193.
- Problem: the paper is more careful than the record in several places and says so only for some. A reader who opens the reports will find sentences the paper contradicts in silence.
- Evidence: (a) `EXT/qrh-mnf-receipt/mnf/MNF_LIBRARY.md` (the same sentence is in the reports of runs 4 and 5 and in `REPO/README.md` lines 100 to 103): "`gap_below_bound_insufficient` says a gap at Δ ≤ 3/8 cannot give it"; `REPO/DEPOSIT_MAP.md` line 140: "insufficient for every Δ ≤ 3/8"; line 52: "shows the threshold Δ > 3/8 of §2 is exact". The Lean statement, `∃ S ⊆ Set.Ioo (-b) b, (∀ x ∈ S, -x ∈ S) ∧ MNF.RH.SpectralGapProperty S Δ ∧ S ≠ {0}`, is about an abstract set and says nothing about the zeros of ζ. (b) `REPO/README.md` lines 116 to 118: "both authors report Comparator runs of their own"; `WORK/facts/literature.md`, entry `openai-math`: no sentence in the files read reports the outcome of a run by OpenAI. (c) `REPO/DEPOSIT_MAP.md` lines 257 to 258: "cold under the kit's launcher, … every definition compared by body". (d) `REPO/README.md` line 49, `DEPOSIT_MAP.md` line 281: "Hardy–Littlewood's O(T) mean square", an attribution the paper dropped as unchecked. (e) `REPO/README.md` line 3 ("seventeen artifacts, eight receipts") and its `sources/` list; `REPO/zenodo-metadata.json` ("Five receipt bundles", "every definition compared by body" for all four library runs, run 3 included).
- Addition to *Errata*: "*Statements of the record that this paper does not repeat.* The reports of runs 3 to 5 and the README say that `gap_below_bound_insufficient` shows that a gap at Δ ≤ 3/8 "cannot give" RH, and the register calls the gap hypothesis "insufficient for every Δ ≤ 3/8" and the threshold "exact". The Lean statement concerns an abstract symmetric set, not the zeros of ζ; whether G(Δ) implies RH for such Δ is not decided by it (if RH holds, the implication holds trivially), and *The MNF.RH library in standard terms* says only where the argument stops. The README says that both authors report Comparator runs of their own; for OpenAI the files read show a configuration and an instruction, not a reported run. The register calls runs 7 to 11 cold and says that every definition was compared by body; the receipts record warm runs, and the definition counts are upper bounds. The README and the register attribute the mean-square bound to Hardy and Littlewood; that attribution was not checked and is not made here." Item (e) is for the repository, to be corrected before the deposit.

### m11. "reservoir" has three meanings in the sources

- Location: PAPER line 263 ("the author's word for zeros off the line (here, those closer to it than δ)") and line 382.
- Problem: the gloss is right for the two files it is attached to, but a reader who opens `Cube.lean`, or the tooltips of Figure 2, meets the opposite convention.
- Evidence: `V6/MNF/RH/Density.lean` lines 66 to 67 ("on the line or in the δ-reservoir", for |Re ρ − 1/2| < δ) and line 166 ("under a gap at Δ > 0 the Δ-reservoir is empty"); `V6/MNF/RH/ReservoirMass.lean` lines 19 to 21 (""reservoir" is its word for the zeros off the critical line (Re ρ ≠ 1/2)"); `V6/MNF/RH/Cube.lean` line 114: `def InReservoir (Δ : ℝ) (ρ : ℂ) : Prop := Δ ≤ |ρ.re - 1 / 2|`.
- Addition to line 263: "The sources are not uniform: in `Density.lean` the δ-reservoir is the set of zeros with 0 < |β − 1/2| < δ, in `ReservoirMass.lean` the reservoir is the set of all zeros off the line, and in `Cube.lean` the reservoir at threshold Δ is the set with |β − 1/2| ≥ Δ."

### m12. Availability: no archived copy of the record is named, and the DOI sentence says nothing

- Location: PAPER line 512.
- Problem: "its DOI is on the Zenodo record page" informs no reader. The receipts, which are the substance of the paper, are located only by a repository URL and a seven-digit commit prefix; nothing says whether a snapshot is archived. The record itself speaks of an earlier Zenodo record, and the paper does not say what that is.
- Evidence: `REPO/DEPOSIT_MAP.md` lines 23 to 25: "the copies inside the add-on folders and inside the Zenodo record of 2026-10-29 are frozen"; `REPO/NOTICE` line 1: "NOTICE — zenodo-record-2026-10-29"; `REPO/zenodo-metadata.json` (upload type "dataset", runs 1 to 6); REPO has no tag; the tree without `.git` is 22 MB.
- Replacement (the bracketed facts are the author's to supply): "The record is the public repository https://github.com/Joeyxyxyz/qrh-comparator-receipts; everything said here refers to commit `f03aaa9d9f461e5ba7540a848db736de73f32018`. [A snapshot of the record at that commit is deposited on Zenodo with this paper, DOI …] or [The record is held only in that repository and is not archived.] [The register and `NOTICE` speak of a Zenodo record of 2026-10-29 for runs 1 to 6: its DOI is …] or [that record was prepared and not published.]" Print the DOI of the paper if it is reserved before the PDF is built; otherwise delete the sentence about it.

### m13. Things in the record that are not in the paper and that a reader will find

- Location: PAPER lines 212 to 227 (*Runs 3 to 6*), *Limitations*.
- Problem: the paper reports eleven runs; the record mentions two further Comparator acceptances of the author's files without receipts, and run 1's bundle contains a second report that the paper never names.
- Evidence: `REPO/DEPOSIT_MAP.md` line 279: "the MNF2 package's algebra (also ACCEPTED at the OpenAI pin on 2026-11-03)"; lines 300 to 303 and `REPO/README.md` line 176: the Sturm–Liouville file "as a standalone Lake project with its own Comparator challenge (accepted again on 2026-11-03, Lean kernel and NanoDa)"; `EXT/qrh-receipt/receipt/BRIDGE.md`: "Result: BRIDGE-OK … This step is an ordinary Lean compile with `#print axioms`, run inside the sandbox; it is not a second Comparator run"; `DEPOSIT_MAP.md` lines 67 to 68: "Same content as the kit's `MNF_Bridge78_Unconditional.lean`, restated over the consolidated definitions."
- Addition: "Outside the eleven runs, the record mentions two further Comparator acceptances whose receipts it does not hold: the injection and ejection algebra of the author's "MNF2" package at the OpenAI pin, and the Sturm–Liouville file as a standalone project with both kernels, each dated 2026-11-03. They are not results of this paper. Run 1's bundle also holds `BRIDGE.md`, the report of an ordinary sandboxed compile, not a Comparator run, of two earlier files of the author on OpenAI's tree; `Unconditional.lean`, judged from run 3 on, restates their content."

### m14. "operated every run"

- Location: PAPER lines 9, 42, 245, 520; line 469 ("One operator made all eleven runs").
- Problem: the kit and every add-on ship an instruction file whose stated job is to have a Claude Code session carry out the protocol as the unprivileged user. The record attributes the operation of every run to the author and says who started a run only for run 11. The reader should be told what "operated" covers.
- Evidence: `KIT/CLAUDE.md` lines 3 and 14 ("You are operating a rented Linux machine … for Joey Messina"; "Your job is to carry out this kit's protocol and report the outcome"); `V6/CLAUDE.md` line 3 ("You are on Joey's laptop, as user `qrh`"); `V6/README.md` line 88 ("Or give Claude Code the prompt *Read CLAUDE.md and carry out the add-on protocol.*"); `REPO/README.md` line 180 ("Joey Messina: … operation of every run"); `NOTES/DENSITY_LEDGER.md` lines 333 to 336 ("This run was started by Joey from a regular terminal window").
- Addition to line 520 or 522: "One qualification of "operated": the kit and every add-on ship an instruction file written for a Claude Code session that starts the scripts, waits and writes the report as the unprivileged user, and the README files offer that route beside the commands typed by hand. The record attributes the operation of every run to the author. Except for run 11, which the working log says he started from a terminal, it does not say for each run whether the commands were typed by him or issued by such a session at his request."

### m15. The provenance gap of run 2 can be stated with evidence instead of "presumably"

- Location: PAPER line 123 and line 552 ("another, presumably earlier, version launched run 2").
- Evidence: checked for this report: `EXT/qrh-zeta23-receipt/receipt/PINS-zeta23.env` (56 lines) is `REPO/sources/qrh-zeta23-addon/PINS-zeta23.env` (62 lines) without its last six lines, the block headed "step B2: the MNF.RH library files reused unchanged from the MNF add-on v2" (`diff` prints only `56a57,62`).
- Replacement: "… so another version launched run 2. It was an earlier one: the pins file copied into run 2's bundle is the deposited add-on's file without its last six lines, the block added for run 6. The scripts of that version are not in the record; what run 2 judged is fixed by its receipt."

### m16. Two caveats about the external artifacts that the record states and the paper omits

- Location: PAPER line 74 and line 93.
- Evidence: `KIT/docs/PROTOCOL.md` lines 17 to 18: "OpenAI's own catalogue of these formalizations, `lean/formalization.yaml`, carries `review: status: unchecked`."; `REPO/README.md` lines 170 to 172: "(the paper zeta23 formalizes; this record does not check the paper, only the Lean statements)".
- Addition to line 74: "The kit's protocol records that OpenAI's own catalogue of these formalizations, `lean/formalization.yaml`, "carries `review: status: unchecked`"." Addition to line 93, after "the mathematics of OpenAI's argument was not read": "Nor was the paper of Alpöge and Furman compared with the statements of zeta23."

### m17. Abstract: "more than two thirds" without the form that was judged

- Location: PAPER line 9.
- Problem: line 157 explains that the judged constants are 2/3 − ε, 5/6 − ε and symbolic constants whose decimals are "docstrings, not statements". The abstract, which most readers will see alone, gives only the title's words.
- Replacement: "… and zeta23, Anthropic's formalization of Alpöge and Furman's theorem that more than two thirds of the zeros are simple and on the critical line (as judged: for every ε > 0, a proportion at least 2/3 − ε at all large heights)."

### m18. Figures

- Location: `WORK/figures/cube-relabeled.svg`, `WORK/figures/cascade-relabeled.svg`; PAPER lines 459 and 461.
- Problem: (a) the relabeled Figure 2 still carries the old wording in its `<title>` tooltips: "reservoir: Delta <= max|delta| < 3/8 (O(T^(1-c)) zeros, proved); empty for the 400 zeros here", "band: … empty under the gap hypothesis (open)", "7/8 face …"; Figure 1's tooltips keep "h_D". They do not show in a PDF and do show if the SVG files are published. (b) Rendered at page width (`review/_final/fig-1.png`, `fig-2.png`), the three subtitle lines of panel B of Figure 2 are crowded against the legend, and in Figure 1 the line "no spacing below 0.243:" touches the top grid line; both are legible. (c) The script that edited the labels is in `WORK/review/_apply/relabel_figures.py` only.
- Fix: remove or relabel the `<title>` elements in both files; deposit the relabeling script and the two edited images with the paper or in the record's notes, since the captions say that the labels were edited.

### m19. The value 0.4243 rests on a script that is not in the record

- Location: PAPER line 477.
- Evidence: `WORK/review/_mathexp/gue_sd.py`; no file of REPO contains it, and no key of `facts/literature.md` supports a citation for the value.
- Replacement: "… and a recomputation of the exact law made while this paper was reviewed gave 0.4243 (script `gue_sd.py`, deposited with the notes)", after adding the script to the notes; or drop the number: "… and the exact law gives a slightly larger value than the surmise."

### m20. Affiliation, competing interests and human review are not stated

- Location: PAPER lines 518 to 528.
- Problem: the paper judges artifacts of two companies with a tool of one of them and says so, which is right; it does not say whether the author has any tie to either, or to Harmonic, or whether any person other than the author has read the Lean statements, the mathematics or the text. Line 522 says only that the record names no human reviewer.
- Replacement (each sentence only if true; no file can establish them): "The author has no affiliation with OpenAI, Anthropic, Harmonic or the Lean FRO and received no funding for this work." "No person other than the author has reviewed the Lean statements, the mathematics or this text."

### m21. Appendix A, run 1, column "Def": "none listed" is ambiguous

- Location: PAPER line 540.
- Problem: the cell can be read as "the configuration lists no definition holes", which no file of the bundle shows (OpenAI's configuration is pinned by hash and not copied into it), or as "the receipt gives no count", which is what the note at line 552 says.
- Replacement: "no count given".

### m22. Line 95 leaves run 1 out

- Location: PAPER line 95: "Run 3 listed its 17 definitions as holes; run 2 and runs 4 to 11 list none".
- Replacement: add "; run 1's challenge defines nothing of its own, and its statement mentions only Mathlib's `riemannZeta`".
- Evidence: the nine-line challenge file printed in `EXT/qrh-receipt/receipt/RECEIPT.md`.

### m23. Acknowledgments omit three sources the work leans on

- Location: PAPER line 532.
- Problem: the Bohr–Landau proof and the real-zero theorem start from `Zeta0EqZeta`, which the paper itself calls a port from PrimeNumberTheoremAnd (lines 295, 434), every run on the zeta23 tree used NanoDa, and every run used landrun; none of the three is acknowledged, though all are cited.
- Replacement: add "The Euler–Maclaurin representation used here comes from the PrimeNumberTheoremAnd project [@pnt-plus] through zeta23; NanoDa [@nanoda] and landrun [@landrun] are the work of their authors."

## Questions only the author can settle

1. The model or models that wrote the Lean files and the text (M2).
2. Whether the commands of runs 1 to 10 were typed by hand or issued by a Claude Code session (m14).
3. Whether a Zenodo record of 2026-10-29 exists, and whether a snapshot of the record will be archived with the paper (m12).
4. Affiliations, funding and human review (m20).
5. The expansion of "Lean FRO" (m9).
6. Before the deposit, the repository's README header, its `sources/` list and `zenodo-metadata.json` (m10, item e); after any new commit, the commit named in *Verifying the record offline*.

## How the checks were made

- Lean blocks: `review/_final/blocks.py` (exact search, white space normalized, in the bundles and in `REPO/sources`).
- Receipts: `facts.tsv`, `*.start`, `*.end`, `*.exit`, `*.type`, `*.time`, the Comparator logs and the reports of all eleven bundles under `WORK/extracted/`, read directly.
- Verifier: `TMPDIR=<scratch> bash ./verify_deposit.sh` in REPO at `f03aaa9`, ending in `VERIFY=OK`; `git status` empty before and after.
- Run 11's challenge: `sha256sum -c` of the 21 challenge and audit lines of the receipt's listing inside `NOTES/zeta23-tree/`; then the generator of V6 run with `python3 -I` on a copy of V6's `MNF/` and `Zeta23/` folders in an empty scratch folder, and the same `sha256sum -c` there (21 of 21 in both).
- Run 2's pins: `diff` of the bundle's `PINS-zeta23.env` with the deposited add-on's.
- Figures: both relabeled SVG files rendered through the Typst module of the scratch area (`review/_final/figs.typ`, `fig-1.png`, `fig-2.png`) and looked at.
- No web page was opened for this report; bibliographic facts were taken as verified in `WORK/facts/literature.md`.
