# Review of WORK/paper.md: receipts and numbers

Reviewer lens: every number, date, time, duration, count, hash, version and commit, checked against
the receipt bundles under `WORK/extracted`, `REPO/CHECKSUMS.sha256`, `REPO/README.md`,
`REPO/DEPOSIT_MAP.md`, the add-on sources under `REPO/sources`, and the numeric notes
(`RESULTS.md`, `CUBE_NUMERIC.md`). Reviewed 2026-11-10 (local). The paper was not edited. Nothing
outside WORK was modified (the record's `verify_deposit.sh` was run read-only with its temporary
directory inside WORK, since removed).

Abbreviations: `EX` = `WORK/extracted`; `REPO` = `/home/joeyxyxyz/repos/qrh-comparator-receipts`;
`V6` = `REPO/sources/qrh-zeta23-addon-v6`.

## Verdict

The receipts side of the paper is in good order. Three items should be fixed before print (two
wordings that the receipts contradict, and the DOI placeholder); the rest are minor. No verdict,
theorem count, time stamp, hash, pin or numeric statistic in the paper disagrees with its source.

## What was checked and found correct

- All eleven runs: label, start, end, exit code, wall clock, kernels, verdict or result line, theorem
  count and definition count, from `logs/<label>.start|.end|.exit|.time`, the Comparator logs and the
  reports. Durations recomputed from start and end agree with the `time` files to within one second
  (run 1: 17:43:45 to 19:38:23 = 1:54:38 against 1:54:37; run 11: 00:02:37 to 00:17:52 = 15:15 against
  15:15.27). "At most 16 minutes in each of runs 3 to 11" holds (maximum 15:15.27, run 11).
- Appendix A, row by row: all 22 tarball hash prefixes equal `CHECKSUMS.sha256`; the chronological
  order 1, 3, 4, 2, 6, 5, 7, 8, 9, 10, 11 is right; one boot identifier
  (`03b05777-b2cf-4d67-a0bc-6f8134e30cbb`) and `job_af_unix_<label> denied` in all eleven facts files;
  `attempt_started` is cold for runs 1 and 2, warm for runs 6 to 11, absent for runs 3 to 5.
- The table of the runs 3 to 6 and the pins table: every entry agrees with the receipts
  (`RECEIPT.md`, `RECEIPT-zeta23.md`, `PINS.env`, `PINS-zeta23.env`).
- Controls: 5 + 16 = 21, 6 accepted and 15 rejected, 4 NanoDa-only skipped, 17:31:27 to 17:32:07 on
  2026-10-27, about twelve minutes before run 1 (`EX/qrh-receipt/receipt/facts.tsv`).
- Kernels: `Nanoda kernel accepts the solution` is in the logs of runs 2 and 6 to 11 and in no other;
  `Lean default kernel accepts the solution` is in all eleven.
- Per-module counts recomputed from the sources against the axiom lines of each `audit.out`: 40 =
  14 + 12 + 8 + 6; 43; 87 with 8 in `Unconditional.lean`; 62 = 36 + 13 + 13; 124; 270; 334; 480; 534 =
  sum over 13 modules; `BohrLandauPartial` 139, `BohrLandauClosure` 64; 27 and 2 unclaimed in
  `ReservoirMass` and `Cube`; 23 Lean files in add-on v6; 18 mirrors; `SimpleEigenvalues.lean` 581
  lines, 4 definitions, 4 claimed. Run 11: 255 statements in the report block, 279 with a leading `@`,
  534 axiom reports, all three standard axioms (one report wrapped over three lines).
- All 17 Lean blocks of the paper occur verbatim (whitespace collapsed) in the receipts or sources
  named for them. Appendix B: all 29 rows have the right module and first run; every tag agrees with
  `DEPOSIT_MAP.md` (or, for the two Mathlib-only lemmas, with the README of add-on v6).
- `sha256sum -c CHECKSUMS.sha256`: 27 entries (21 tarballs, 6 other files). `verify_deposit.sh` re-run
  at commit `f03aaa9` with network: every step ok, `VERIFY=OK`. Manifest hashes `a20b1b1d…` (run 2's
  receipt) and `0c37cc13…` (deposited add-on) confirmed; the five Lean sources hashed in run 6 are
  byte-identical to the deposited add-on.
- Numerics: every figure in the paragraph and table of "A numerical illustration" equals
  `RESULTS.md` or `CUBE_NUMERIC.md` (400 zeros, 14.134725, 679.742198, 414 against 414.557, 3.3e-10,
  mean 0.99744, sd 0.3709 against 0.4221, minimum 0.2434, the four table rows, KS 0.0508 / 0.247 and
  0.3285 / 2.7e-38, slopes 4.52 [4.07, 5.05] and 3.71 [3.26, 4.23] against 3.62 / 2.67 and 1.71 / 0.79,
  0.145 against 0.2263 and 1).
- Arithmetic in the text: 5/6 and 3/4 at sigma_1 = 3/4; the window 1/sigma_1 <= a <= 1/(2 - 2 sigma_1)
  nonempty exactly for sigma_1 >= 2/3; delta_0 = (log T)^(-2/5) giving (log T)^(3/5); 5/9 = 1/3 + 2/9;
  the counterexample 10 > 8 (and 10 <= 12 for the corrected bound); 534 - 255 = 279.

## Findings

### F1 (major). Introduction: "nothing had been compiled" contradicts the receipts

- Location: *The artifacts and what was added*. "Runs 1 and 2 started from trees in which nothing had
  been compiled and ended with the verdict PASS." Same paragraph: "the protocol reserves PASS for runs
  that start from nothing compiled".
- Evidence: `EX/qrh-receipt/receipt/RECEIPT.md`: "Compiled dependency files before the run | 106968
  files, digest `a12ec201639976add458307f6cfd34fe9592474b706e6b1ea0a8378cc18ee93f`" and "Mathlib |
  `d13f23b723b8a846827a245b89c10fc7d3f11612`, prebuilt cache (lake exe cache get); cache complete: yes";
  its own definition is narrower: "This was a cold run: nothing of the proof had been compiled on this
  machine before Comparator compiled it in its sandbox." Run 2, `EX/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`:
  "nothing of the challenge, the solution or the Zeta23 library had been compiled on this machine", with
  "`deps_compiled_files` | 52108" and "`mathlib_oleans` | 8313". The paper itself says later (*The trust
  base*) that the Mathlib cache "was downloaded, not compiled in the sandbox", and defines cold correctly
  in *Cold and warm runs*.
- Replacement: "Runs 1 and 2 started from trees in which nothing of the challenge or of the proof had
  been compiled (the compiled dependencies, Mathlib's prebuilt cache among them, were in place; see
  *The trust base*) and ended with the verdict PASS." and "…report ACCEPTED; the protocol reserves PASS
  for runs in which nothing of the challenge or the proof was compiled beforehand, and this paper keeps
  the two words apart."

### F2 (major). Definition counts are presented as counts of compared bodies; they are counts of `def` lines

- Location: *Runs 3 to 6: the library judged*, table: "| 4 | `mnf-library-v2` | 43 | 17, bodies compared |"
  (likewise "41, bodies compared", "23, bodies compared"). Appendix A: "Definitions are compared by
  name, type and body from run 4 on; the receipts of runs 1 and 2 give no count."
- Evidence.
  (a) The count is a regular-expression count of `def` lines in the challenge sources:
  `V6/scripts/z23_density_check.py` line 100: `defs = re.findall(r"^(?:noncomputable )?def (\S+)", challenge_src, re.M)`.
  (b) Comparator's own log shows that, without holes, only the theorems are export targets and
  definitions are reached through the statements: `EX/qrh-mnf-v2-receipt/mnf-v2/logs/mnf-library-v2.log`
  line 96, "Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, MNF.RH.zeta_order_ge_one, … MNF.RH.spectralGapHyp_three_eighths_iff, propext, … outParam] from MNFChallenges.RH"
  (43 theorem names, no definition), where run 3's log (`EX/qrh-mnf-receipt/mnf/logs/mnf-library.log`
  line 90) ends the same list with the 17 holes "… MNF.RH.ZeroFreeRightOf, MNF.RH.Counter,
  MNF.RH.signGate, …, MNF.RH.MultiplicityBoundOne] from MNFChallenges.RH". The kit says the same:
  `REPO/sources/qrh-comparator-kit/docs/PROTOCOL.md`: "exports the challenge statement and every
  definition it refers to".
  (c) Some counted definitions are referred to by no claimed statement. `MNF.RH.Counter`
  (`REPO/sources/qrh-mnf-addon-v2/MNFChallenges/Gap.lean` line 21: "def Counter : Set ℂ := …") occurs in
  no line of the `audit.out` of runs 4, 5 or 6 (grep count 0); it is used only by three unclaimed lemmas
  and inside a proof. `Zeta23.BL.CG`, `meanSquareB` and `A₀` are `def`s of the run 11 mirror
  `MNFChallengesD/ReservoirMass.lean` (copy in `REPO/notes/density-field-2026-11-03/zeta23-tree/`, sha256
  `8d7b4643…` as in the receipt's listing) and occur in no printed statement of run 11's `audit.out`;
  the generator excludes every statement that mentions them (`V6/scripts/z23_gen_density_challenge.py`:
  "or a constant fixed by Classical.choose (CG, meanSquareB, A₀)"). `CG`'s challenge-side body takes
  `Classical.choose` of a theorem whose challenge-side proof is `sorry`, which by the paper's own second
  lesson could not have been compared and accepted.
  (d) A rough reachability count by this reviewer (names in the printed statements, closed under the
  bodies of the counted definitions; a heuristic, not a receipt): 16 of 17 in run 4, 39 of 41 in run 5,
  about 88 of 110 in run 11 (the unclaimed supporting mirrors `Core`, `Gap`, `Hypotheses`, `Counting`
  contribute definitions such as `SpeiserTheorem`, `MultiplicityBoundOne`, `cMT` that no statement of
  runs 7 to 11 mentions).
  So the reports' sentence "17 definitions in the challenge, all compared by name, type and body
  (definition_names is empty)" establishes that no definition is a hole; it is not a count of compared
  bodies. No verdict is affected: every definition a claimed statement refers to was compared.
- Replacement. Table cells: "17, none a hole", "41, none a hole", "23, none a hole" (run 3 stays "17, as
  holes"), with one sentence under the table: "From run 4 on no definition is listed as a hole, so
  Comparator compares by name, type and body every definition that a claimed statement refers to. The
  counts are the `def` declarations of the challenge sources, as the report generator counts them; a few
  are referred to by no claimed statement (for example `MNF.RH.Counter`) and were therefore not compared,
  so each count is an upper bound." Appendix A: replace the sentence by "Runs 2 and 4 to 11 list no
  definition hole, so every definition a claimed statement refers to is compared by name, type and
  body; 'Def' counts the `def` declarations in the challenge sources and is an upper bound for the
  bodies compared (in runs 10 and 11, for instance, `Zeta23.BL.CG`, `meanSquareB` and `A₀` are counted
  and no claimed statement refers to them); the receipts of runs 1 and 2 give no count." Add to
  *Errata*, under "Found while preparing this paper": "The reports of runs 4 to 11 say that the N
  definitions of the challenge were 'all compared by name, type and body'; N counts `def` lines, and
  Comparator compares those a claimed statement refers to."

### F3 (major). Placeholder DOI

- Location: *Availability*. "The Zenodo record of this paper has the DOI 10.5281/zenodo.XXXXXXX."
- Evidence: the paper itself; `WORK/review/ASSEMBLY_NOTES.md`: "Placeholder: 'The Zenodo record of this
  paper has the DOI 10.5281/zenodo.XXXXXXX' (Availability)".
- Replacement: reserve the DOI in the Zenodo upload form before the PDF is built and print it; if that
  is not possible, "This paper is deposited on Zenodo; its DOI is on the record's landing page and in
  the README of the repository."

### F4 (minor). Date line is a day ahead of the text's own "read on" dates

- Location: title block. "Date: 2026-11-11".
- Evidence: the paper's references say "Documentation, read 2026-11-10" and "default branch as read on
  2026-11-10"; `WORK/review/ASSEMBLY_NOTES.md`: "Date line 2026-11-11 is the UTC date of run 11; the
  assembly was done on 2026-11-10 local time."
- Replacement: the date of the deposit, or "Date: 2026-11-11 (UTC)" if the deposit is made on that day.

### F5 (minor). "Mirrors are generated at run time" is not true of runs 4 and 5

- Location: *Challenges as module-for-module mirrors*. "Mirrors are generated at run time and fixed by
  hash in the receipt."
- Evidence: the add-ons of runs 3 to 5 ship the challenge files and copy them:
  `REPO/sources/qrh-mnf-addon-v3/MANIFEST.sha256` lists "MNFChallenges/Core.lean" …
  "MNFChallenges/SturmLiouville.lean"; `REPO/sources/qrh-mnf-addon-v3/scripts/mnf_prepare.sh` line 69:
  `cp -r "$ADDON_DIR/MNFChallenges" "$TREE/MNFChallenges"`. Only the zeta23 add-ons generate them in the
  tree (`REPO/sources/qrh-zeta23-addon/MNFChallenges/` holds only `theorem_list.txt`; `V6/README.md`:
  "`scripts/z23_gen_density_challenge.py` writes `MNFChallengesD/*.lean`").
- Replacement: "In runs 3 to 5 the generated challenge files ship in the add-on tarball; in runs 6 to
  11 they are generated in the tree at run time. In both cases the receipt lists their sha256."

### F6 (minor). `verify_deposit.sh` does not re-derive "every hash the record cites"

- Location: *Contributions*, item 1. "a script, `verify_deposit.sh`, that re-derives every hash the
  record cites and re-reads every verdict from the deposited bundles".
- Evidence: `REPO/verify_deposit.sh` step 6 fetches two files only
  ("…/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean", "…/zeta23/Challenge.lean");
  `REPO/README.md` also cites "`ChallengeDeps.lean` `8f9a7e7b…`, `comparator.json` `610d95c6…`", which the
  script does not re-derive, and the receipts cite tool and toolchain hashes that cannot be re-derived
  from the deposit. *Verifying the record offline* describes the script correctly.
- Replacement: "a script, `verify_deposit.sh`, that re-derives the hashes of the deposited files,
  re-reads every verdict from the bundles and compares the judged sources with the add-on tarballs".

### F7 (minor). Two duration formats side by side, unexplained

- Location: *Runs 1 and 2: the two replications*. "started at 2026-10-27T17:43:45Z, took 1:54:37" and
  "took 21:01.50"; table of *Runs 3 to 6*, column "Wall clock" ("12:43.44", "5:55.36").
- Evidence: the values are copied correctly from `logs/<label>.time` ("Elapsed (wall clock) time
  (h:mm:ss or m:ss): 1:54:37", "… 21:01.50"), but "1:54:37" is h:mm:ss and "21:01.50" is m:ss with
  hundredths, and a reader can take the second for 21 hours.
- Replacement: "took 1 h 54 min 37 s" and "took 21 min 1.5 s"; column header "Wall clock (min:s)".

### F8 (minor). Inconsistent digit grouping

- Location: *Runs 1 and 2: the two replications*. "The proof is 316 files and 102265 lines", against
  "2,924 project files and 486,490 lines" in the previous paragraph.
- Evidence: the two receipts print the numbers differently ("2,924 project files, 486,490 lines";
  "316 files, 102265 lines"); the paper copied both.
- Replacement: "316 files and 102,265 lines".

### F9 (minor). Sign of the pole term changes between sections

- Location: *The milestone for distances above one sixth*. "The Montgomery–Vaughan term and the term
  $N^{1-s}/(1-s)$ are of order $N^{2-2\sigma_1}$".
- Evidence: steps 1 and 4 of the paper and Appendix B write $N^{1-s}/(s-1)$, as does the source
  (`V6/Zeta23/BL/BohrLandauClosure.lean` line 993: `(⌈T⌉₊ : ℂ) ^ (1 - ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) - 1)`).
- Replacement: "and the term $N^{1-s}/(s-1)$".

### F10 (minor). Figure 1 prints a GUE count that differs from the table

- Location: *A numerical illustration*, caption of Figure 1. "Panel A: fraction of the total spacing
  length in spacings below a threshold … against GUE and Poisson; panel B: histogram of the spacings."
- Evidence: `WORK/figures/cascade.svg` has the labels "0 below 0.2 (GUE 3.4, Poisson 72)" (panel A) and
  "(GUE expects 3.3, Poisson 72);" (panel B), and says "Panel A uses the exact GUE law, panel B the
  Wigner surmise."; the paper's table has 3.4 (`RESULTS.md`: expected below 0.2, surmise 3.3, exact 3.4).
- Replacement: add to the caption "Panel A uses the exact GUE spacing law, panel B the Wigner surmise,
  which is why the expected number of spacings below 0.2 reads 3.4 in one and 3.3 in the other."

### F11 (minor). Figure 2 labels a two-sided count "proved" and titles panel A "its support under RH"

- Location: *A numerical illustration*, caption of Figure 2. "Panel A is a schematic: the data lie on
  one axis and the shaded zones contain no data; their labels give the status of statements."
- Evidence: `WORK/figures/cube.svg` has the labels "reservoir |delta| >= Delta: O(T^(1-c)) zeros,
  proved", "A. The cube (delta1, delta2, s) and its support under RH" and "line delta = 0 (the 0.0e
  zone)". The paper says of the zero-density estimate: "The statement counts zeros to the right of the
  line; the two-sided form over $N_{\mathrm{off}}$ is not a theorem of the layer."
- Replacement: add to the caption "The label 'O(T^(1-c)) zeros, proved' on the outer zone refers to the
  one-sided estimate of run 10 (the two-sided form follows by the reflection but is not a receipted
  statement), and 'its support under RH' in the panel title describes where the measure would lie if
  RH held, not a result." Better: regenerate the figure without the three labels.

### F12 (minor). Statements that go stale when the repository is pushed

- Location: *Verifying the record offline*. "Run at commit `f03aaa9` while this paper was prepared, it
  ended in `VERIFY=OK`." and "the 27 listed files: the 21 tarballs and six other top-level files".
- Evidence: both are true now (`git -C REPO rev-parse --short HEAD` = f03aaa9; re-run for this review:
  `VERIFY=OK`; `CHECKSUMS.sha256` has 27 entries). But the documents the paper sends readers to still
  describe an older record: `REPO/README.md` line 3, "One record, seventeen artifacts, eight receipts",
  against the paper's "21 tarballs (the kit, nine add-ons, eleven receipt bundles)"; `REPO/README.md`,
  section "sources/", lists five of the ten unpacked folders; `REPO/zenodo-metadata.json` says "Five
  receipt bundles" and "every definition compared by body: 40, 43 and 87 theorems", which is wrong for
  run 3 (17 holes) and is listed in `CHECKSUMS.sha256`.
- Replacement: before the deposit, update the README header and its `sources/` list, write new Zenodo
  metadata for the paper, re-run `verify_deposit.sh` at the pushed commit, and print that commit and
  the then-current number of listed files; or keep the sentence as "Run at commit `f03aaa9` (the commit
  that added run 11), it ended in `VERIFY=OK`; later commits change documents only."
