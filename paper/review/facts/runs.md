# Fact sheet: the eleven Comparator runs

Written 2026-11-10 (local date of the writing session; run 11's receipt is stamped 2026-11-11 UTC).
Every entry carries its evidence as `path` + short exact quote. Path prefixes:

- `EX/` = `WORK/extracted/` (the eleven receipt bundles, unpacked; checked in this session to be file-for-file identical to the contents of the tarballs in REPO, by extracting each tarball again and running `diff -rq`).
- `REPO/` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/`.

Rule followed: where two sources disagree the receipt is preferred, and the disagreement is listed in section 8.

Quoting convention: quotes are exact in their characters; where the source file is hard-wrapped (README.md, DEPOSIT_MAP.md, NOTICE, PROTOCOL.md, the add-on READMEs) the line breaks inside a quote are joined into spaces. Tab-separated facts are quoted with their tab. An ellipsis "..." inside a quote marks an omission made here; the character "…" is the source's own. The Lean code blocks are copied from the receipts without change.

Vocabulary used below, as the receipts use it: a run's **label** is the name of its systemd job (`qrh-main`, `zeta23-main`, ...); **cold** and **warm** are the receipts' own words (the files `logs/<label>.type` and the facts `attempt_started_<label>`); **PASS** is the verdict word of runs 1 and 2 only; **ACCEPTED** is the result word of runs 3 to 11.

## 1. Master table

Times are UTC, copied from `logs/<label>.start` and `logs/<label>.end`. "Duration" is the wall clock printed by `/usr/bin/time` in `logs/<label>.time`. Thm = theorem names in the Comparator configuration; Def = definitions in the challenge.

| # | label | what was judged | tree | type | kernels | Thm | Def | start (UTC) | end (UTC) | duration | exit | verdict line (verbatim) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `qrh-main` | OpenAI's `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` | openai/math `adc7f124` | cold | Lean kernel | 1 | none listed (see 3.1) | 2026-10-27T17:43:45Z | 2026-10-27T19:38:23Z | 1:54:37 | 0 | `**Verdict: PASS**` |
| 2 | `zeta23-main` | Anthropic's zeta23, 17 statements | anthropics/formal-math `16a5ce41`, `zeta23/` | cold | Lean kernel and NanoDa | 17 | "no definition holes" (see 3.2) | 2026-10-28T11:08:56Z | 2026-10-28T11:29:58Z | 21:01.50 | 0 | `**Verdict: PASS**` |
| 3 | `mnf-library` | MNF.RH v1 on a copy of run 1's tree | copy of run 1's tree | warm w.r.t. OpenAI's files (see 3.3) | Lean kernel | 40 | 17, listed as `definition_names` (holes; bodies not compared) | 2026-10-28T00:20:02Z | 2026-10-28T00:32:46Z | 12:43.44 | 0 | `**Result: MNF_LIBRARY=ACCEPTED**` |
| 4 | `mnf-library-v2` | MNF.RH v2 on a copy of run 1's tree | copy of run 1's tree | warm w.r.t. OpenAI's files | Lean kernel | 43 | 17, name, type and body | 2026-10-28T03:25:44Z | 2026-10-28T03:39:13Z | 13:28.87 | 0 | `**Result: MNF_LIBRARY=ACCEPTED**` |
| 5 | `mnf-library-v3` | MNF.RH v3 (with `SturmLiouville/`) on a copy of run 1's tree | copy of run 1's tree | warm w.r.t. OpenAI's files | Lean kernel | 87 | 41, name, type and body | 2026-10-29T05:56:47Z | 2026-10-29T06:10:47Z | 14:00.38 | 0 | `**Result: MNF_LIBRARY=ACCEPTED**` |
| 6 | `zeta23-mnf` | MNF.RH and the restatement of zeta23's Theorems A to D, on run 2's tree | run 2's checkout | warm | Lean kernel and NanoDa | 62 | 23, name, type and body | 2026-10-29T02:06:38Z | 2026-10-29T02:12:34Z | 5:55.36 | 0 | `**Result: MNF_ZETA23=ACCEPTED**` |
| 7 | `zeta23-density` | density layer, add-on v2 | run 2's checkout | warm | Lean kernel and NanoDa | 124 | 66, name, type and body | 2026-11-03T21:05:57Z | 2026-11-03T21:13:50Z | 7:53.23 | 0 | `**Result: MNF_DENSITY=ACCEPTED**` |
| 8 | `zeta23-density-v3` | density layer, add-on v3 (Bohr-Landau for delta > 1/6) | run 2's checkout | warm | Lean kernel and NanoDa | 270 | 76, name, type and body | 2026-11-03T22:03:08Z | 2026-11-03T22:09:37Z | 6:29.61 | 0 | `**Result: MNF_DENSITY=ACCEPTED**` |
| 9 | `zeta23-density-v4` | density layer, add-on v4 (Bohr-Landau for every delta > 0) | run 2's checkout | warm | Lean kernel and NanoDa | 334 | 81, name, type and body | 2026-11-04T00:52:20Z | 2026-11-04T00:58:43Z | 6:22.34 | 0 | `**Result: MNF_DENSITY=ACCEPTED**` |
| 10 | `zeta23-density-v5` | density layer, add-on v5 (displacement sum; zero-density estimate) | run 2's checkout | warm | Lean kernel and NanoDa | 480 | 98, name, type and body | 2026-11-04T14:38:23Z | 2026-11-04T14:45:29Z | 7:06.02 | 0 | `**Result: MNF_DENSITY=ACCEPTED**` |
| 11 | `zeta23-density-v6` | density layer, add-on v6 (pair-measure module; no real zeros in (0,1)) | run 2's checkout | warm | Lean kernel and NanoDa | 534 | 110, name, type and body | 2026-11-11T00:02:37Z | 2026-11-11T00:17:52Z | 15:15.27 | 0 | `**Result: MNF_DENSITY=ACCEPTED**` |

Notes on the table.

- The run numbers are the record's (REPO/README.md and REPO/DEPOSIT_MAP.md section 10), not chronological: by start time the order is 1, 3, 4, 2, 6, 5, 7, 8, 9, 10, 11. Run 6 (2026-10-29T02:06:38Z) precedes run 5 (2026-10-29T05:56:47Z); run 2 (2026-10-28T11:08:56Z) follows runs 3 and 4.
- End minus start, computed here from the two stamps (whole seconds): run 1 1:54:38; run 2 21:02; run 3 12:44; run 4 13:29; run 5 14:00; run 6 5:56; run 7 7:53; run 8 6:29; run 9 6:23; run 10 7:06; run 11 15:15. These agree with the timer values to within one second.
- All eleven job scripts were launched on the same boot of the same machine: every `job_boot_id_<label>` fact is `03b05777-b2cf-4d67-a0bc-6f8134e30cbb` (e.g. `EX/qrh-receipt/receipt/facts.tsv`: "job_boot_id_qrh-main	03b05777-b2cf-4d67-a0bc-6f8134e30cbb"; `EX/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`: "job_boot_id_zeta23-density-v6	03b05777-b2cf-4d67-a0bc-6f8134e30cbb").
- Machine, from run 1's receipt (`EX/qrh-receipt/receipt/RECEIPT.md`): "8 CPUs, 37 GB RAM, 39 GB swap, kernel 7.0.0-38-generic, Landlock ABI 8".

## 2. Pins, by tree

### 2.1 OpenAI tree (runs 1, 3, 4, 5)

| item | value | evidence |
|---|---|---|
| repository, commit | https://github.com/openai/math at `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | `EX/qrh-receipt/receipt/RECEIPT.md`: "module `OAI.NumberTheory.DirichletL.Nonvanishing` of https://github.com/openai/math at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`" |
| commit date and subject | 2026-10-06T14:58:50-07:00, "Initial commit" | `EX/qrh-receipt/receipt/facts.tsv`: "oai_commit_date	2026-10-06T14:58:50-07:00", "oai_commit_subject	Initial commit" |
| upstream head when fetched | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` (newer than the pin) | RECEIPT.md: "OpenAI repository head at fetch time \| 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (NEWER than pinned)" |
| Lean | v4.34.1 | RECEIPT.md: "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release); release files verified: yes (7 files match the pinned sha256 of the v4.34.1 release)" |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612`, prebuilt cache | RECEIPT.md: "Mathlib \| `d13f23b723b8a846827a245b89c10fc7d3f11612`, prebuilt cache (lake exe cache get); cache complete: yes" |
| Comparator | tag v4.34.0, commit `d03acab154d269c06e60e4de7e4cc85deebff94b`, built with Lean v4.34.1 | RECEIPT.md: "Comparator \| v4.34.0 `d03acab154d269c06e60e4de7e4cc85deebff94b`, built with leanprover/lean4:v4.34.1 (upstream pins leanprover/lean4:v4.34.0)" |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` | RECEIPT.md: "lean4export \| `076e8e57707e813375e8f9da8bf989799ace9680`" |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, version 0.1.18, static | RECEIPT.md: "landrun \| `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (landrun version 0.1.18), static: yes" |
| NanoDa | not used | RECEIPT.md: "It is one kernel (Lean's own). No second kernel was run." |
| trusted statement file | `ComparatorChallenges/QuasiRiemannHypothesis.lean`, sha256 `065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5`; config `QuasiRiemannHypothesis.json`, sha256 `46ebb7edc11f69536210f502b4bcbd36bbaf3f0872c16748b6c8ce43991bf320` | `EX/qrh-receipt/receipt/PINS.env`: `SHA_CHALLENGE_LEAN="065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5"`, `SHA_CHALLENGE_JSON="46ebb7edc11f69536210f502b4bcbd36bbaf3f0872c16748b6c8ce43991bf320"` |
| third-party libraries in the proof | PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0` and rellich-kondrachov `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`, each with OpenAI's patch | PINS.env: `PNT_COMMIT="c39a751132c88b6e8080b74c74023fd95b3d8be0"          # AlexKontorovich/PrimeNumberTheoremAnd (+ OpenAI patch)`, `RELLICH_COMMIT="70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"      # abenenson/rellich-kondrachov (+ OpenAI patch)` |

Runs 3 to 5 use the same tools: each add-on works under its own directory and reaches the kit's tools through a link. Evidence: `REPO/sources/qrh-mnf-addon/scripts/mnf_prepare.sh`: `ln -sfn "$TOOLS" "$MNFWORK/tools"`; `EX/qrh-mnf-receipt/mnf/logs/mnf-library.job.sh`: `lake env "/home/qrh/qrh-work/mnf/tools/comparator/.lake/build/bin/comparator" "MNFChallenges/RH.json"`. The receipts of runs 3 to 5 do not restate the pins; they point to run 1's receipt ("Main kit verdict ... **PASS** (RECEIPT.md)").

### 2.2 Anthropic tree (runs 2, 6, 7, 8, 9, 10, 11)

| item | value | evidence |
|---|---|---|
| repository, commit, directory | https://github.com/anthropics/formal-math at `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, directory `zeta23/` | `EX/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`: "Project: `zeta23/` of https://github.com/anthropics/formal-math at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (Alpöge–Furman, arXiv:2608.13637, formalized by Anthropic)" |
| note on the pin | main on 2026-10-27; `zeta23/` last changed at `2bafb8c8` (2026-08-28) | `EX/qrh-zeta23-receipt/receipt/PINS-zeta23.env`: `FM_COMMIT="16a5ce41304fcdaea4e0be7c132e1c361dc26da5"          # main on 2026-10-27; zeta23/ last changed at 2bafb8c8 (2026-08-28)` |
| Lean | v4.33.0-rc2 | RECEIPT-zeta23.md: "Lean (version 4.33.0-rc2, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release); toolchain binaries: yes (7 files match the pinned sha256 of the v4.33.0-rc2 release)" |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` | RECEIPT-zeta23.md facts table: "`mathlib_commit` \| 51e6992efd06126df61a496bebf8f49482a4e129" |
| Comparator | tag v4.33.0-rc2, commit `75c730e9b6ef5c2c3b334fad7c3d51fe20624c88`, built with Lean v4.33.0-rc2 | facts table: "`comparator_commit` \| 75c730e9b6ef5c2c3b334fad7c3d51fe20624c88", "`comparator_build_toolchain` \| leanprover/lean4:v4.33.0-rc2"; PINS-zeta23.env: `Z23_COMPARATOR_TAG="v4.33.0-rc2"` |
| lean4export | `9fb131bb100eb32ccf6836f14e4f8328d13b6792` | facts table: "`lean4export_commit` \| 9fb131bb100eb32ccf6836f14e4f8328d13b6792" |
| NanoDa | https://github.com/robsimmons/nanoda_lib at `68d5ca9db226849b41a6fff59d796ff19d0a8840`, binary sha256 `d883b3139c9aea661a861f60aecaf14631d5c0a929b8e49a100e2173dd3dfb15` | facts table: "`nanoda_commit` \| 68d5ca9db226849b41a6fff59d796ff19d0a8840", "`nanoda_sha256` \| d883b3139c9aea661a861f60aecaf14631d5c0a929b8e49a100e2173dd3dfb15"; PINS-zeta23.env: `Z23_NANODA_REPO="https://github.com/robsimmons/nanoda_lib"`. Each of runs 7 to 11 records the same binary hash again, e.g. `EX/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`: "nanoda_bin_sha256_zeta23-density-v6	d883b3139c9aea661a861f60aecaf14631d5c0a929b8e49a100e2173dd3dfb15" |
| landrun | the same binary as on the OpenAI tree: commit `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, version 0.1.18, static, sha256 `63a60219f6bd7bf61341730e95d1fcfd4b9d877e48d5d24759de010f6fbc6ea9` | facts table: "`landrun_commit` \| 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4", "`landrun_sha256` \| 63a60219f6bd7bf61341730e95d1fcfd4b9d877e48d5d24759de010f6fbc6ea9", "`landrun_static` \| yes"; the same sha256 in `EX/qrh-receipt/receipt/facts.tsv`: "landrun_sha256	63a60219f6bd7bf61341730e95d1fcfd4b9d877e48d5d24759de010f6fbc6ea9" |
| trusted statement files | `Challenge.lean` sha256 `6f2a4ba95ab8c5319e541a1cc1b3699c0ae8cef23ea8e68f958e11b07281761e`; `ChallengeDeps.lean` `8f9a7e7bb313bbada77d0dd1b71a80bda1c0580b71ba1dd0020b438d63a318e0`; `comparator.json` `610d95c6c84f13b3e2238b476fe45f0b28567108f536f67a0b9ed1586a2c68f1` | RECEIPT-zeta23.md: "the 17 theorems named in `comparator.json` (sha256 `610d95c6c84f13b3e2238b476fe45f0b28567108f536f67a0b9ed1586a2c68f1`), stated in `Challenge.lean` (sha256 `6f2a4ba95ab8c5319e541a1cc1b3699c0ae8cef23ea8e68f958e11b07281761e`), which imports only Mathlib and inlines the definitions of `ChallengeDeps.lean` (sha256 `8f9a7e7bb313bbada77d0dd1b71a80bda1c0580b71ba1dd0020b438d63a318e0`)" |

Runs 6 to 11 use the binaries run 2 installed (same work directory, same paths). Evidence: every job script of runs 2 and 6 to 11 runs `/home/qrh/qrh-zeta23-work/tools/comparator/.lake/build/bin/comparator` in `/home/qrh/qrh-zeta23-work/formal-math/zeta23` (e.g. `EX/qrh-zeta23-density-v6-receipt/logs/zeta23-density-v6.job.sh`); the facts file of each later bundle is cumulative and begins with run 2's tool facts (e.g. `EX/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`, 172 lines, lines 1 to 57 dated 2026-10-28). The pin files of add-ons v2 to v6 agree with one another on every non-comment line except the `D_*` lines (label, work directory, bundle name), checked in this session with `diff`.

## 3. The runs one by one

### 3.1 Run 1: `qrh-main`, OpenAI's 7/8 theorem

- Judged: one theorem. `EX/qrh-receipt/receipt/RECEIPT.md`: "Theorem: `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`". The whole challenge file, as the receipt prints it:

```lean
import Mathlib

namespace OAI

theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  sorry

end OAI
```

- Size of the proof: RECEIPT.md: "Proof size: 2,924 project files, 486,490 lines, plus 4 files of PrimeNumberTheoremAnd and 15 of rellich-kondrachov (with OpenAI's compatibility patches), on Mathlib `d13f23b723b8` and Lean v4.34.1".
- Axioms allowed: RECEIPT.md: "Axioms allowed: `propext`, `Quot.sound`, `Classical.choice`".
- Verdict: RECEIPT.md: "**Verdict: PASS**"; "Comparator's own closing lines: `Lean default kernel accepts the solution` and `Your solution is okay!`. This was a cold run: nothing of the proof had been compiled on this machine before Comparator compiled it in its sandbox."; `EX/qrh-receipt/receipt/facts.tsv`: "2026-10-27T19:38:56Z	verdict	PASS".
- Attempts: one. RECEIPT.md table: "| 1 | cold | 2026-10-27T17:43:45Z | 2026-10-27T19:38:23Z | 0 | ACCEPTED: Comparator accepted the proof |".
- Wall clock and memory: RECEIPT.md: "Wall clock | 1:54:37"; "Peak memory of the job (program memory plus swap, sampled each minute) | 5.6 GiB"; "Peak memory, largest single process | 7.0 GiB".
- Kernel: Lean's only (quote in 2.1). Log tail, `EX/qrh-receipt/logs/qrh-main.log`: "Running Lean default kernel on solution." / "Lean default kernel accepts the solution" / "Your solution is okay!". The log also shows "Build completed successfully (7061 jobs)." before the export.
- Definitions: the receipt gives no count of compared definitions for run 1; the challenge file defines nothing of its own (it is the nine lines above) and the statement mentions only Mathlib's `riemannZeta`. What the receipt says about definitions is the general sentence "with every definition it mentions identical on both sides".
- Controls run before the real run: RECEIPT.md: "Controls | 6 accepted, 15 rejected (expected 6 and 15); 4 nanoda-only projects skipped"; facts.tsv: "controls_accepted	6", "controls_rejected	15", "selftest_failures	0", "sandbox_holds_in_comparator	yes".
- After the run: RECEIPT.md: "After the run | OpenAI checkout verified: yes; trusted inputs: unchanged; proof sources: unchanged; checker binaries: unchanged; kit: unmodified".
- Deviation recorded by the receipt: "One deviation is built into the kit: Comparator and lean4export have no release for Lean 4.34.1, so their v4.34.0 sources were built with the 4.34.1 toolchain. Their own regression projects were run in that configuration as part of the controls." followed by "No others recorded."
- Not a Comparator run, but in the same bundle: `EX/qrh-receipt/receipt/BRIDGE.md` ("**Result: BRIDGE-OK**"), 21 audited theorems of `MNF.Bridge78`; the file says of itself: "This step is an ordinary Lean compile with `#print axioms`, run inside the sandbox; it is not a second Comparator run." It is not one of the eleven runs.
- Kit tarball: `qrh-comparator-kit.tar.gz`, sha256 `e0745073e49e9e2d3620a4a6472c9757819ab163388f56ac1aaf253bd92c46ea`. Receipt tarball: `qrh-receipt.tar.gz`, sha256 `d86705398e4858e034bb8f18397e28984ec6525699b31f1d794b230e1998fcbb`.

### 3.2 Run 2: `zeta23-main`, Anthropic's zeta23

- Judged: 17 theorems. `EX/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`: "Statements: the 17 theorems named in `comparator.json`"; "Proof: module `Solution` and the `Zeta23` library it imports: 316 files, 102265 lines, on Mathlib `51e6992efd06` and leanprover/lean4:v4.33.0-rc2".
- The 17 names, as listed by the receipt: `two_thirds_on_critical_line`, `two_thirds_on_critical_line_cumulative`, `two_thirds_simple_on_critical_line`, `two_thirds_simple_on_critical_line_cumulative`, `five_sixths_distinct`, `five_sixths_distinct_cumulative`, `montgomery_taylor_on_critical_line`, `montgomery_taylor_simple_on_critical_line_mult`, `montgomery_taylor_simple_on_critical_line_mult_cumulative`, `montgomery_taylor_distinct_mult`, `montgomery_taylor_distinct_mult_cumulative`, `dirichlet_two_thirds_on_critical_line`, `dirichlet_two_thirds_simple_on_critical_line`, `dirichlet_five_sixths_distinct`, `dirichlet_montgomery_taylor_on_critical_line`, `dirichlet_montgomery_taylor_simple_on_critical_line_mult`, `dirichlet_montgomery_taylor_distinct_mult`.
- Form of the headline statement (the receipt prints the whole of `Challenge.lean`; these lines copied from it):

```lean
theorem two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry
```

```lean
theorem two_thirds_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry
```

  So the 2/3 statements are liminf statements in epsilon form ("liminf ≥ 2/3"); the strict "more than two thirds" of the paper's title corresponds, in the challenge file, to the Theorem D statements with the constant `cMT`, whose docstring in the same file reads "1/c₁* (= 3/2 − cot(1/√2)/√2 = 0.67250…), with c₁* = `cMT`" and whose statements have the factor `(2 - 1 / cMT - ε)`. The receipt's own gloss: "They are proportions of zeros in windows `(T, 2T]` for large `T`, in the ε-form shown, counted with multiplicity on the left and as distinct points on the right."
- Definitions: no definition holes. RECEIPT-zeta23.md: "Axioms allowed: `propext`, `Quot.sound`, `Classical.choice`; no definition holes"; PINS-zeta23.env: `Z23_CONFIG="comparator.json"                                     # 17 theorem names, no definition holes, enable_nanoda true`. The receipt gives no count of compared definitions.
- Verdict: "**Verdict: PASS**"; "Comparator accepted the proof. Its own closing line: `Your solution is okay!`. This was a cold run: nothing of the challenge, the solution or the Zeta23 library had been compiled on this machine before Comparator compiled it in its sandbox. Kernels that replayed the proof: Lean's kernel and NanoDa."
- Run line: "Run: cold, started 2026-10-28T11:08:56Z, ended 2026-10-28T11:29:58Z, exit 0, wall clock 21:01.50, largest process 6.9 GiB; machine: 8 CPUs, 37 GB RAM, 39 GB swap".
- Kernels, log tail (`EX/qrh-zeta23-receipt/logs/zeta23-main.log`, also printed in the receipt): "Running nanoda kernel on solution" / "Nanoda kernel accepts the solution" / "Running Lean default kernel on solution." / "Lean default kernel accepts the solution" / "Your solution is okay!". Before it: "Build completed successfully (8887 jobs)."
- Deviations: the receipt's section "## Deviations" reads "none".
- After the run (facts table of the receipt): "`trusted_files_after` | unchanged", "`deps_after` | unchanged", "`dep_lakefiles_after` | unchanged", "`tools_after` | unchanged", "`addon_after` | unmodified", "`audit_rc` | 0".
- Axiom audit: 17 lines of the form "'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]" under "## Axiom reports (`scripts/PrintAxioms.lean` of the project, plain `lean`, sandboxed)".
- A recorded fact that does not match the deposited add-on (see section 8, item D9): facts table "`addon_manifest_sha256` | a20b1b1d9e5dff52cbd6aaef82119172ef87cf5ab160e039d15f94f73f0b1086".
- Add-on tarball: `qrh-zeta23-addon.tar.gz`, sha256 `958abb9f8a2a9e4b87597956344da0967fb6d635d187a861ea3337bd9b22da1f`. Receipt tarball: `qrh-zeta23-receipt.tar.gz`, sha256 `e0b9a4d97a04dff75f25cca69f28e684a785bd5f633ea8d0763085be7ea364e5`.

### 3.3 Runs 3, 4, 5: MNF.RH on OpenAI's tree

Common to the three. Challenge `MNFChallenges/RH.json`, solution module `MNF.RH.Unconditional`, on a fresh copy of run 1's tree. Evidence: `EX/qrh-mnf-receipt/mnf/MNF_LIBRARY.md`: "The library run below is a second, separate Comparator run: its challenge (`MNFChallenges/RH.lean`, every proof `sorry`) states the MNF theorems and the definitions they use; its solution (`MNF.RH.Unconditional`) proves them, using OpenAI's theorem where the 7/8 region is needed."; "tree: a copy of the verified tree at `/home/qrh/qrh-work/mnf-tree`". Kernel: Lean's only; the three configurations have `"enable_nanoda": false` (`REPO/sources/qrh-mnf-addon/MNFChallenges/RH.json`, and the v2 and v3 copies) and the three logs end "Lean default kernel accepts the solution" / "Your solution is okay!" with no NanoDa line.

Cold or warm. These three bundles contain no `.type` file and no `attempt_started_*` fact, and the words "cold" and "warm" do not occur in them (checked with `grep -ril`). What they record is that the tree is a copy of the already-compiled run 1 tree and that Comparator built only the new modules: `EX/qrh-mnf-receipt/mnf/logs/kit.log`: "copying the verified tree to /home/qrh/qrh-work/mnf-tree (this is the slow part: several GB)"; `EX/qrh-mnf-receipt/mnf/logs/mnf-library.log` has 5 "Built" lines (the challenge module and the four `MNF.RH.*` modules) and "Build completed successfully (7065 jobs)."; the v2 log has 8 "Built" lines and the v3 log 18. The record's README states the status in words: `REPO/README.md`: "The MNF runs are warm with respect to the external proof files by design (the checked tree is reused, as the kit's protocol prescribes); they are cold with respect to the library itself."

| | run 3 | run 4 | run 5 |
|---|---|---|---|
| report | `EX/qrh-mnf-receipt/mnf/MNF_LIBRARY.md` | `EX/qrh-mnf-v2-receipt/mnf-v2/MNF_LIBRARY.md` | `EX/qrh-mnf-v3-receipt/mnf-v3/MNF_LIBRARY.md` |
| result line | "**Result: MNF_LIBRARY=ACCEPTED**" | "**Result: MNF_LIBRARY=ACCEPTED**" | "**Result: MNF_LIBRARY=ACCEPTED**" |
| job line | "Comparator job `mnf-library`: exit 0, started 2026-10-28T00:20:02Z, ended 2026-10-28T00:32:46Z" | "Comparator job `mnf-library-v2`: exit 0, started 2026-10-28T03:25:44Z, ended 2026-10-28T03:39:13Z" | "Comparator job `mnf-library-v3`: exit 0, started 2026-10-29T05:56:47Z, ended 2026-10-29T06:10:47Z" |
| counts | "40 theorems, 17 definitions named in the challenge config" | "43 theorems named in the challenge config; 17 definitions in the challenge, all compared by name, type and body (definition_names is empty)" | "87 theorems named in the challenge config; 41 definitions in the challenge, all compared by name, type and body (definition_names is empty)" |
| what Comparator checked, in the report's words | "checked that every definition and statement agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice" | "checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice" | same sentence as run 4 |
| tree additions | "plus `MNF/`, `MNFChallenges/`, `MNF_Audit.lean` and two `lean_lib` lines appended to `lakefile.lean`" | same as run 3 | "plus `MNF/`, `SturmLiouville/`, `MNFChallenges/`, `MNF_Audit.lean` and three `lean_lib` lines appended to `lakefile.lean`" |
| timer | "Elapsed (wall clock) time (h:mm:ss or m:ss): 12:43.44" | "13:28.87" | "14:00.38" |
| axiom reports in `audit.out` | 40, all `[propext, Classical.choice, Quot.sound]` | 43, all the same | 87, all the same |
| listing hash of the library files (`mnf_library_files`) | `cef4d42cffff4a8c8838d0d7669352a5e94843d26c00bbbb0b54f6d0cef7fe81` | `16cdfffbb49bdbaea79b564b69bbc37521498b9c4e9ac9f19cde404755ababc9` | `97ccb702619a423b2d300d6c179e9f754c757645a95d3604203b073c7d3240ee` |
| `lakefile.lean` after the append | `4c9e5551480166cab734284e852c84711d3684eeb8104fcec233567a9e4d5a43` | `4c9e5551480166cab734284e852c84711d3684eeb8104fcec233567a9e4d5a43` | `7a9fd35b2df3c848dc1da63c764c23c0d1551e80fff5aeed2c6d1cbedee4c72a` |
| add-on tarball | `qrh-mnf-addon.tar.gz` `295ee9c6086730e9e0592b36e989452943d18d7b2ef1f05aee276002ff0fa7df` | `qrh-mnf-addon-v2.tar.gz` `933c5ba89388b045fe7a6b7d0a067c56e063f4033bfec80a9196c2bf55a03d3e` | `qrh-mnf-addon-v3.tar.gz` `3668e13824776b259141df844a0f6a1243447d94c548b90bca891a2e9dafb447` |
| receipt tarball | `qrh-mnf-receipt.tar.gz` `f9180842f8c269b64d89ad0f236898e9164af3e5b39ef0c5e1b34561b8838d6b` | `qrh-mnf-v2-receipt.tar.gz` `c6142a402077b7f312eb22ab990dca3b92b7bdcaa94c26836dc5dc5b15d79eb6` | `qrh-mnf-v3-receipt.tar.gz` `023d7ada93e313296e7e9d88c82569fa65c704a2624149a67e5e74c762c8159a` |

Run 3 and definitions. In run 3 the 17 definitions are listed under `definition_names` in the configuration (`REPO/sources/qrh-mnf-addon/MNFChallenges/RH.json`, 40 `theorem_names`, 17 `definition_names`); in runs 4 and 5 that list is empty. What this changes is stated in the v2 add-on's README (`REPO/sources/qrh-mnf-addon-v2/README.md`): "In v2 the config's `definition_names` is empty, so Comparator compares every definition by name, type and body (in v1 the 17 definitions were listed as holes, which Comparator compares by name, type and universe levels only)." So run 3 did not compare definition bodies; runs 4 to 11 did.

Each report also says, under "How to read this": "The Riemann Hypothesis is not among the theorems." and "`SpeiserTheorem` and `DoubleZeroForcesLeftDerivZero` are hypotheses (explicit arguments), not axioms; nothing here asserts them." (all three reports).

No deviations section exists in these three reports and none of them lists a problem.

### 3.4 Run 6: `zeta23-mnf`

- Report: `EX/qrh-zeta23-mnf-receipt/mnf/MNF_ZETA23.md`. Result line: "**Result: MNF_ZETA23=ACCEPTED**".
- Judged: "its challenge (`MNFChallenges/*.lean`, every proof `sorry`, Mathlib only) states the MNF theorems and the definitions they use; its solution (`MNF.RH.Zeta23Restated`) proves them, delegating to zeta23's theorems where a proportion of zeros is asserted."
- Job line: "Comparator job `zeta23-mnf`: exit 0, started 2026-10-29T02:06:38Z, ended 2026-10-29T02:12:34Z (warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; cold with respect to MNF/)". Type file `EX/qrh-zeta23-mnf-receipt/logs/zeta23-mnf.type`: "warm". Timer: "5:55.36".
- Counts: "62 theorems named in the challenge config; 23 definitions in the challenge, all compared by name, type and body (definition_names is empty)"; facts: "mnf_theorems	62", "mnf_definitions	23".
- Kernels: "Lean's kernel and NanoDa replayed the solution."; log tail: "Nanoda kernel accepts the solution" / "Lean default kernel accepts the solution" / "Your solution is okay!"; "Build completed successfully (8891 jobs)."
- Tree: "the zeta23 checkout at `/home/qrh/qrh-zeta23-work/formal-math/zeta23` as checked by zeta23-main, plus `MNF/`, `MNFChallenges/`, `MNF_AuditB2.lean` and two `lean_lib` stanzas appended to `lakefile.toml`". Unlike runs 3 to 5 this is the checkout itself, not a copy.
- Hashes: "MNF files (sha256 listing): `6a77a635f4b4a782cc6b9e535bf398f72948fe41e6c329b8740aa8bfc058f06a`; lakefile.toml after the append: `b58855d79a113fb5cb39761d3a4d77fe4e5397ce319d775a20608a11a4f24eb1`"; facts: "mnf_files_after	unchanged".
- Axiom reports in `audit.out`: 62, all `[propext, Classical.choice, Quot.sound]`.
- The report's caution: "None of this discharges `SpectralGapHyp`, `AllZerosSimple`, `MultiplicityBoundOne` or `DerivativeNonvanishing`: a proportion of zeros, however large, is not a statement about every zero. Nothing here uses OpenAI's 7/8 theorem, and no sentence should put the two together as one result."
- Add-on tarball: `qrh-zeta23-addon.tar.gz` (the same tarball as run 2), sha256 `958abb9f8a2a9e4b87597956344da0967fb6d635d187a861ea3337bd9b22da1f`. Receipt tarball: `qrh-zeta23-mnf-receipt.tar.gz`, sha256 `1476f56809c5739866e538d84d41670d573dc37fb56f74ddcc1709da065c1eef`.

### 3.5 Runs 7 to 11: the further layer on the zeta23 tree

Common to the five. Report `MNF_DENSITY.md`; challenge configuration `MNFChallengesD/Density.json`; solution module `MNF.RH.DensityAll`; the tree is run 2's checkout with the layer's files added. Common sentence of all five reports: "The run below is a second, separate Comparator run on the same tree: its challenge (`MNFChallengesD/*.lean`, every proof `sorry`, Mathlib only) states the theorems of the density layer and the definitions they use; its solution (`MNF.RH.DensityAll`) proves them, delegating to zeta23's theorems where it restates them. Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice; Lean's kernel and NanoDa replayed the solution." Common tree line: "tree: the zeta23 checkout at `/home/qrh/qrh-zeta23-work/formal-math/zeta23` as checked by zeta23-main, plus the layer's files under `MNF/`, `Zeta23/` and `MNFChallengesD/`, `MNF_AuditDensity.lean`, and `lean_lib` stanzas appended to `lakefile.toml`". Common lakefile hash after the append: `51b09c56356db2ea0d62034a534601e551d07f32f6db18efde66d77d629e18a9`. All five type files read "warm"; all five logs end "Nanoda kernel accepts the solution" / "Running Lean default kernel on solution." / "Lean default kernel accepts the solution" / "Your solution is okay!"; all five record "density_files_after	unchanged".

Common note recorded by every one of the five receipts (a note, not a deviation section): "sorries outside the claim set: Zeta23/BohrLandau.lean: meanSquare_strip, rightHalfBound_of_meanSquare (not in the claim set)" (fact `density_sorries_outside_claims`). From run 10 on the report explains them: "The two `sorry` lemmas of `Zeta23/BohrLandau.lean` (the analytic inputs as first named) are kept unchanged for the reproducibility of the v2/v3 receipts, are not in the claim set, and no claimed theorem depends on them; both statements are proved in `BohrLandauClosure.lean`." (`EX/qrh-zeta23-density-v5-receipt/density-v5/MNF_DENSITY.md`).

| | run 7 | run 8 | run 9 | run 10 | run 11 |
|---|---|---|---|---|---|
| bundle directory under `EX/` | `qrh-zeta23-density-receipt/density/` | `qrh-zeta23-density-v3-receipt/density-v3/` | `qrh-zeta23-density-v4-receipt/density-v4/` | `qrh-zeta23-density-v5-receipt/density-v5/` | `qrh-zeta23-density-v6-receipt/density-v6/` |
| report title | "The density layer on the zeta23 tree (QRH zeta23 add-on v2, step B3)" | "... (QRH zeta23 add-on v3, step B3)" | "... (QRH zeta23 add-on v4, step B3)" | "... (QRH zeta23 add-on v5, step B3)" | "... (QRH zeta23 add-on v6, step B3)" |
| job line | "Comparator job `zeta23-density`: exit 0, started 2026-11-03T21:05:57Z, ended 2026-11-03T21:13:50Z" | "Comparator job `zeta23-density-v3`: exit 0, started 2026-11-03T22:03:08Z, ended 2026-11-03T22:09:37Z" | "Comparator job `zeta23-density-v4`: exit 0, started 2026-11-04T00:52:20Z, ended 2026-11-04T00:58:43Z" | "Comparator job `zeta23-density-v5`: exit 0, started 2026-11-04T14:38:23Z, ended 2026-11-04T14:45:29Z" | "Comparator job `zeta23-density-v6`: exit 0, started 2026-11-11T00:02:37Z, ended 2026-11-11T00:17:52Z" |
| counts | "124 theorems named in the challenge config; 66 definitions in the challenge, all compared by name, type and body (definition_names is empty)" | "270 theorems named in the challenge config; 76 definitions in the challenge, ..." | "334 theorems named in the challenge config; 81 definitions in the challenge, ..." | "480 theorems named in the challenge config; 98 definitions in the challenge, ..." | "534 theorems named in the challenge config; 110 definitions in the challenge, ..." |
| facts `density_theorems` / `density_definitions` | 124 / 66 | 270 / 76 | 334 / 81 | 480 / 98 | 534 / 110 |
| warm with respect to (end of the job line) | "cold for every module this add-on introduces" | "cold for every module v3 introduces" | "cold for every module v4 introduces" | "cold for every module v5 introduces" | "cold for every module v6 introduces" |
| timer | 7:53.23 | 6:29.61 | 6:22.34 | 7:06.02 | 15:15.27 |
| axiom reports in `audit.out` | 124, all the standard three | 270, all the standard three | 334, all the standard three | 480, all the standard three | 534, all the standard three |
| layer files, listing hash (`density_files_sha256`) | `9345643db224c306fd12fdc7bc08aababe56fd208e881635d492f6dad78ede7b` | `da64044f58f523a24544ddcdda17626886466a696823f3bb8c05c1c8ec48dbd9` | `a049074cd3e4f14208f75b9d61851248faeca1625fe73933bf16aa1c30827ba2` | `3d854a3ada21af0bcbca6e2029f6fc70bca9abe17f12ca4cc40713e02c8d9d7c` | `b520f013f967505f84490e4c0844101029ea0a730781b8aadb00ad952feebb60` |
| add-on tarball | `qrh-zeta23-addon-v2.tar.gz` `5dc41dfff1d998e340af4802bbcf538f252099939692fbee407b7e253eb627fc` | `qrh-zeta23-addon-v3.tar.gz` `c0958d53657f532035baf81bf3bcf5068377351ca8db687f4888c99c0233daa2` | `qrh-zeta23-addon-v4.tar.gz` `fb74e8a28fde97141b0d150f0cdc1399ba0aa2e7da76ce87975be12cf0d04a90` | `qrh-zeta23-addon-v5.tar.gz` `2d2cf0589c409ba72363657fbe6d7039b277bb2ec6c171f42a906033d50eb453` | `qrh-zeta23-addon-v6.tar.gz` `99575a1e8e267695b96f73e911522f5c9f12673741a0c57a1c06452c24a508e6` |
| receipt tarball | `qrh-zeta23-density-receipt.tar.gz` `975b21780c2c84ee84334d8115177a8858f87297731ccd108a4424782a5419fc` | `qrh-zeta23-density-v3-receipt.tar.gz` `0588555dccdcefcb08479e34050c64048ef152ac0ba9d7632be4b7da62c2aaf0` | `qrh-zeta23-density-v4-receipt.tar.gz` `0d1919e42cbe45408d719536fc3c45ecdaa106bb1c83470e12b063006372f56a` | `qrh-zeta23-density-v5-receipt.tar.gz` `37a806b20c4ef5abf9bed06f127746e46d2184b928a75a0efcaa06de1a5ef863` | `qrh-zeta23-density-v6-receipt.tar.gz` `ca07a500aa8384b96b03f3480053cd48271bb157a04155de42342ca21254a90c` |

Counting of the axiom reports: `audit.out` wraps one long report over three lines in each of the five bundles ("'AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq' depends on axioms: [propext," / " Classical.choice," / " Quot.sound]"); it is a standard report. The axiom table inside each `MNF_DENSITY.md` has the same count with the single value "Classical.choice, Quot.sound, propext" (checked for runs 9 and 11: 334 and 534 rows).

Full "warm" wording of run 11, which names everything compiled earlier in the tree (`EX/qrh-zeta23-density-v6-receipt/density-v6/MNF_DENSITY.md`): "(warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; compiled earlier in this tree (step B2): warm for Core, Gap, Hypotheses, Counting, Zeta23Restated; compiled earlier in this tree (v2-v5 runs): MNF/RH/GapDensity MNF/RH/Density MNF/RH/Strip MNF/RH/DensityPartial MNF/Extension/InjectionEjection Zeta23/Superlinear Zeta23/OffLine Zeta23/BohrLandau Zeta23/BL/DPMV Zeta23/BL/DPMVexp Zeta23/BL/JensenDisc Zeta23/BL/BohrLandauPartial Zeta23/BL/BohrLandauClosure MNF/RH/ReservoirMass Zeta23/Density/StripDensity; cold for every module v6 introduces)".

Each run re-judges the previous one plus the new modules: `REPO/DEPOSIT_MAP.md` section 10: "Each run re-judges everything of the previous one plus the new modules; run 11 is the complete layer."

What each run added, in the receipts' own "How to read this" words (short extracts; the Lean statements are in each report's "What was proved" block):

- Run 9 (first appearance of the full theorem): statement block line "Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau" and axiom table row "| `Zeta23.BL.bohrLandau_full` | Classical.choice, Quot.sound, propext |" (`EX/qrh-zeta23-density-v4-receipt/density-v4/MNF_DENSITY.md`, lines 429 and 773). The name `bohrLandau_full` does not occur in run 8's report (count 0).
- Run 10: "`MNF/RH/ReservoirMass.lean`: the reservoir mass Σ m(ρ)·|Re ρ − 1/2| over 0 < Im ρ ≤ T (the total displacement of the zeros from the line, with multiplicity) equals ∫₀^{1/2} NOff(δ) dδ (layer cake), is ≤ A·T·(log T)^{3/5} for large T ... Classically weaker than Littlewood (1924) and Selberg (1946)"; "`Zeta23/Density/StripDensity.lean`: a zero-density estimate with a power saving (Carlson's method, single-window form): `Zeta23.Density.density_single_window` ... weaker than Carlson's exponent 4σ₁(1 − σ₁), which is not proved here. A count, not a zero-free region: it excludes no individual zero."
- Run 11: "`MNF/RH/Cube.lean`: the strip seen through three coordinates of a pair of zeros ... These equivalences RELOCATE RH, simplicity and the gap; they do not prove them, and the cubic small-distance law of the zeros is the GUE prediction, not a theorem."; "Also: ζ has no real zero in (0,1), from the tree's one-term Euler–Maclaurin representation."
- Runs 10 and 11, closing bullet: "None of this proves, weakens or replaces `SpectralGapHyp` (RH for Δ ≥ 1/2; an open zero-free strip for 0 < Δ < 1/2); `OnLineDensityOne` follows from RH and is not known to imply it; a zero-density estimate is not a zero-free region. Nothing here uses OpenAI's 7/8 theorem, and no sentence should put the two together as one result."

## 4. Tarballs and full sha256

Source: `REPO/CHECKSUMS.sha256`. `sha256sum -c CHECKSUMS.sha256` was run in this session in REPO and every one of its 27 entries reported OK. The record holds 21 tarballs: the kit, 9 add-ons, 11 receipt bundles.

| run | add-on (or kit) tarball | sha256 | receipt tarball | sha256 |
|---|---|---|---|---|
| 1 | `qrh-comparator-kit.tar.gz` | `e0745073e49e9e2d3620a4a6472c9757819ab163388f56ac1aaf253bd92c46ea` | `qrh-receipt.tar.gz` | `d86705398e4858e034bb8f18397e28984ec6525699b31f1d794b230e1998fcbb` |
| 2 | `qrh-zeta23-addon.tar.gz` | `958abb9f8a2a9e4b87597956344da0967fb6d635d187a861ea3337bd9b22da1f` | `qrh-zeta23-receipt.tar.gz` | `e0b9a4d97a04dff75f25cca69f28e684a785bd5f633ea8d0763085be7ea364e5` |
| 3 | `qrh-mnf-addon.tar.gz` | `295ee9c6086730e9e0592b36e989452943d18d7b2ef1f05aee276002ff0fa7df` | `qrh-mnf-receipt.tar.gz` | `f9180842f8c269b64d89ad0f236898e9164af3e5b39ef0c5e1b34561b8838d6b` |
| 4 | `qrh-mnf-addon-v2.tar.gz` | `933c5ba89388b045fe7a6b7d0a067c56e063f4033bfec80a9196c2bf55a03d3e` | `qrh-mnf-v2-receipt.tar.gz` | `c6142a402077b7f312eb22ab990dca3b92b7bdcaa94c26836dc5dc5b15d79eb6` |
| 5 | `qrh-mnf-addon-v3.tar.gz` | `3668e13824776b259141df844a0f6a1243447d94c548b90bca891a2e9dafb447` | `qrh-mnf-v3-receipt.tar.gz` | `023d7ada93e313296e7e9d88c82569fa65c704a2624149a67e5e74c762c8159a` |
| 6 | `qrh-zeta23-addon.tar.gz` (as run 2) | `958abb9f8a2a9e4b87597956344da0967fb6d635d187a861ea3337bd9b22da1f` | `qrh-zeta23-mnf-receipt.tar.gz` | `1476f56809c5739866e538d84d41670d573dc37fb56f74ddcc1709da065c1eef` |
| 7 | `qrh-zeta23-addon-v2.tar.gz` | `5dc41dfff1d998e340af4802bbcf538f252099939692fbee407b7e253eb627fc` | `qrh-zeta23-density-receipt.tar.gz` | `975b21780c2c84ee84334d8115177a8858f87297731ccd108a4424782a5419fc` |
| 8 | `qrh-zeta23-addon-v3.tar.gz` | `c0958d53657f532035baf81bf3bcf5068377351ca8db687f4888c99c0233daa2` | `qrh-zeta23-density-v3-receipt.tar.gz` | `0588555dccdcefcb08479e34050c64048ef152ac0ba9d7632be4b7da62c2aaf0` |
| 9 | `qrh-zeta23-addon-v4.tar.gz` | `fb74e8a28fde97141b0d150f0cdc1399ba0aa2e7da76ce87975be12cf0d04a90` | `qrh-zeta23-density-v4-receipt.tar.gz` | `0d1919e42cbe45408d719536fc3c45ecdaa106bb1c83470e12b063006372f56a` |
| 10 | `qrh-zeta23-addon-v5.tar.gz` | `2d2cf0589c409ba72363657fbe6d7039b277bb2ec6c171f42a906033d50eb453` | `qrh-zeta23-density-v5-receipt.tar.gz` | `37a806b20c4ef5abf9bed06f127746e46d2184b928a75a0efcaa06de1a5ef863` |
| 11 | `qrh-zeta23-addon-v6.tar.gz` | `99575a1e8e267695b96f73e911522f5c9f12673741a0c57a1c06452c24a508e6` | `qrh-zeta23-density-v6-receipt.tar.gz` | `ca07a500aa8384b96b03f3480053cd48271bb157a04155de42342ca21254a90c` |

The pairing of add-on to receipt for runs 7 to 11 is the one of the table in `REPO/DEPOSIT_MAP.md` section 10 (e.g. "| 11 | `zeta23-density-v6` | `qrh-zeta23-addon-v6.tar.gz` `99575a1e…` | `qrh-zeta23-density-v6-receipt.tar.gz` `ca07a500…` | 534 (110) | ACCEPTED 2026-11-11 00:02–00:17 UTC |") and of the contents table of `REPO/README.md`. The receipts themselves do not contain the tarball hashes (see section 8, item D10); they contain per-file listings and listing hashes (`library_sha256.txt`, `mnf_sha256.txt`, `density_sha256.txt`).

## 5. Sandbox facts (landrun, AF_UNIX, network)

What every run records (all eleven):

- Launch mode: "systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G" (fact `launch_mode_<label>` in every facts file; printed in every report, e.g. `EX/qrh-mnf-receipt/mnf/MNF_LIBRARY.md`: "launch: systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G; AF_UNIX sockets in the job: denied").
- From inside the job's own unit: "job_af_unix_<label>	denied" and "job_stack_kb_<label>	1048576" (every facts file). The probe is in the job script itself, e.g. `EX/qrh-receipt/logs/qrh-main.job.sh`: `socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)` printing "allowed" or "denied".
- landrun is the sandbox launcher handed to Comparator: every job script exports `COMPARATOR_LANDRUN=".../tools/bin/landrun"` and `COMPARATOR_LEAN4EXPORT=...` (e.g. `EX/qrh-zeta23-density-v6-receipt/logs/zeta23-density-v6.job.sh`: `export COMPARATOR_LANDRUN="/home/qrh/qrh-zeta23-work/tools/bin/landrun"`).

What runs 1, 2, 6 and 7 to 11 record in addition, in the minute before launch:

- "sandbox_enforcing	yes", "sandbox_tcp	blocked", "af_unix_restricted	yes", and a `probes_boot_id` equal to the job's boot id. Evidence: `EX/qrh-receipt/receipt/facts.tsv` at 2026-10-27T17:43:34Z; `EX/qrh-zeta23-receipt/receipt/facts.tsv` at 2026-10-28T11:08:55Z to 11:08:56Z; `EX/qrh-zeta23-density-v6-receipt/receipt/facts.tsv` at 2026-10-29T02:06:38Z (run 6), 2026-11-03T21:05:57Z (run 7), 2026-11-03T22:03:07Z to 22:03:08Z (run 8), 2026-11-04T00:52:20Z (run 9), 2026-11-04T14:38:22Z to 14:38:23Z (run 10), 2026-11-11T00:02:36Z to 00:02:37Z (run 11).
- Run 1's receipt summarizes: "Sandbox enforcing / inside Comparator / AF_UNIX restricted / TCP in sandbox | yes / yes / yes / blocked" and "Inside the run's own unit | AF_UNIX sockets denied; stack limit 1048576 kB". Run 2's receipt: "AF_UNIX sockets in the job: denied; sandbox enforcing: yes; outbound TCP in the sandbox: blocked".

What runs 3, 4 and 5 do not record: their own facts files (9 lines each) have no `sandbox_enforcing`, `sandbox_tcp`, `af_unix_restricted` or `probes_boot_id` line of their own. They record the launch mode, "job_af_unix_mnf-library	denied" (and the v2, v3 analogues), the stack limit and the boot id, which equals the boot id of run 1's probes and controls ("probes_boot_id	03b05777-b2cf-4d67-a0bc-6f8134e30cbb" in `EX/qrh-receipt/receipt/facts.tsv`). The network probe for the OpenAI-tree sandbox is therefore the one in run 1's receipt, same boot, same landrun binary.

Controls. The 21 control projects (6 expected acceptances, 15 expected rejections) were run once, in run 1's kit, with the OpenAI-tree checker: `REPO/sources/qrh-zeta23-addon/README.md`: "The main kit's phase 3 controls (6 accepted, 15 rejected) were run with Comparator v4.34.0 on Lean v4.34.1, not with the rc2 checker this add-on builds; the rc2 checker is the release matching the project's toolchain, with the same compare and axiom logic (its Main.lean differs in the NanoDa plumbing and in not printing a separate kernel-acceptance line)." One of the controls tests the sandbox inside Comparator: facts "control-sandbox_write	ok (exit 0)" then "sandbox_holds_in_comparator	yes".

What the sandbox is, in the protocol's words (`REPO/sources/qrh-comparator-kit/docs/PROTOCOL.md`): "landrun, Landlock, systemd, the Linux kernel | They are the sandbox. Before the real run, and again in the same boot at launch, the kit proves by behaviour that the sandbox denies a forbidden write and that the socket restriction holds; one control makes a proof file attempt forbidden writes while Comparator itself compiles it."; "Every Comparator launch, the controls included, happens inside a systemd unit with `RestrictAddressFamilies=~AF_UNIX`, as the README asks."; "The kit builds landrun without cgo and refuses to go on unless the binary is static."

## 6. What a PASS and an ACCEPTED mean, in the receipts' own words

### 6.1 PASS, run 1 (`EX/qrh-receipt/receipt/RECEIPT.md`, sections "What a PASS means" and "What it does not mean", verbatim)

> 1. The theorem the proof files prove is the statement above, with every definition it mentions identical on both sides.
> 2. The proof rests on no axiom other than the three listed.
> 3. Lean's kernel re-checked the exported proof term and everything it depends on, Mathlib's part included.

> - It is not a check that the Lean statement matches the paper's English. The statement is a few lines; read it.
> - It is not the Riemann Hypothesis. Zeros with 1/2 < Re s <= 7/8 are untouched by this theorem.
> - It is one kernel (Lean's own). No second kernel was run.
> - It trusts: Lean's kernel and the released Lean toolchain; Comparator and lean4export; Mathlib's definitions and its prebuilt cache; OpenAI's challenge file and lakefile (read when the kit was written, pinned by sha256); landrun, Landlock, systemd and the Linux kernel for the sandbox; this machine and whoever operated it.

### 6.2 PASS, run 2 (`EX/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md`, verbatim)

> 1. The theorems the proof files prove are the statements above, with every definition they mention identical on both sides.
> 2. The proofs rest on no axiom other than the three listed.
> 3. Lean's kernel and nanoda re-checked the exported proof terms and everything they depend on, Mathlib's part included.

> - It is not a check that the Lean statements match the paper's English, nor of the paper itself. The statements are the `Challenge.lean` printed above; read it. They are proportions of zeros in windows `(T, 2T]` for large `T`, in the ε-form shown, counted with multiplicity on the left and as distinct points on the right.
> - It is not the Riemann Hypothesis and says nothing about any individual zero. A proportion of zeros on the line, however large, is not a statement about every zero.
> - It is an independent repetition of a check Anthropic reports having run itself (Comparator + NanoDa, AUDIT.md of the project); it is not a registry admission and not a first verification.
> - It trusts: Lean's kernel and the released toolchain and NanoDa; Comparator and lean4export; Mathlib's definitions and its prebuilt cache; the project's challenge files and lakefile (pinned by sha256); landrun, Landlock, systemd and the Linux kernel for the sandbox; this machine and whoever operated it.

### 6.3 ACCEPTED (runs 3 to 11)

The reports have no section titled "What ACCEPTED means". What they say is the sentence under the result line.

- Run 3: "Comparator built both in its sandbox, exported both, and checked that every definition and statement agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice." (`EX/qrh-mnf-receipt/mnf/MNF_LIBRARY.md`)
- Runs 4 and 5: "Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice." (`EX/qrh-mnf-v2-receipt/mnf-v2/MNF_LIBRARY.md`)
- Runs 6 to 11: the same sentence, ending "...Classical.choice; Lean's kernel and NanoDa replayed the solution." (`EX/qrh-zeta23-mnf-receipt/mnf/MNF_ZETA23.md`; the five `MNF_DENSITY.md`)
- In run 1's attempts table the word appears as the outcome of the Comparator job, distinct from the verdict: "| 1 | cold | 2026-10-27T17:43:45Z | 2026-10-27T19:38:23Z | 0 | ACCEPTED: Comparator accepted the proof |".

The conditions under which the report scripts print ACCEPTED are stated in the add-ons, not in the receipts:

- Runs 3 to 5, `REPO/sources/qrh-mnf-addon/README.md`: "ACCEPTED requires: Comparator exit 0 with its acceptance line; the job launched with AF_UNIX denied; the audit compile clean (no error, no `sorry`); exactly one axiom report per theorem, each within the permitted three." The v2 README adds: "and (v2) no definition holes in the config."
- Runs 7 to 11, docstring of `REPO/sources/qrh-zeta23-addon-v6/scripts/z23_density_check.py`: "MNF_DENSITY=ACCEPTED requires / - the Comparator job finished with exit 0 and its log ends in Comparator's acceptance line, with NanoDa's acceptance line present (the pinned configuration enables it); / - the job ran in the restricted unit (AF_UNIX denied), in the same boot as the sandbox probes; / - the files the run used are unchanged afterwards; / - the audit compile exited 0 with no error and no `sorry` in its output; / - every theorem named in the challenge config has exactly one axiom report, listing no axiom other than propext, Classical.choice, Quot.sound. / Otherwise REJECTED (Comparator said no, or a condition failed) or INCOMPLETE." (the slashes mark the line breaks of the docstring)

### 6.4 Why runs 3 to 11 say ACCEPTED and not PASS

The kit's protocol reserves PASS for cold runs (`REPO/sources/qrh-comparator-kit/docs/PROTOCOL.md`, section "Re-runs: only a cold run certifies"): "A **cold** run starts from a tree in which nothing has been compiled. That is the situation Comparator's assumption 2 describes, and only a cold run can end in PASS." and "If Comparator accepts in a warm run the verdict is PROVISIONAL, not PASS, because of what a warm run leaves open." Reading offered by this sheet, not a quoted fact: that passage is about re-running the same proof in a used tree; the add-on runs are a different case (new files judged on a tree whose upstream part was compiled by an accepted cold run). Their reports use the separate word ACCEPTED and state the warm status in the job line (runs 6 to 11) or leave it to the README (runs 3 to 5). No document read here states in so many words why the add-on reports say ACCEPTED instead of PASS. The paper should keep the two words apart: PASS for runs 1 and 2, ACCEPTED for runs 3 to 11.

## 7. Erratum on the prose of the run 9 report

Source: `REPO/DEPOSIT_MAP.md` section 10, verbatim:

> Erratum (2026-11-04). The report inside the run 9 bundle (`density-v4/MNF_DENSITY.md`, block `## How to read this`) carries the sentence "Bohr–Landau itself is NOT proved …", inherited from the v2/v3 report generator, where it was true; for run 9 it is false, as the same report's statement block and axiom table show (`Zeta23.BL.bohrLandau_full` with standard axioms). The verdict, the audit and the hashes of run 9 are unaffected; the generator is corrected in add-on v5 and the run 10 report carries the corrected prose; the run 9 bundle is not altered.

Checked against the bundles in this session:

- The stale sentence is in run 9's report: `EX/qrh-zeta23-density-v4-receipt/density-v4/MNF_DENSITY.md`, block "## How to read this": "Bohr–Landau itself is NOT proved: `Zeta23/BohrLandau.lean` names its two analytic inputs as `sorry` lemmas, which are not in the claim set and on which no claimed theorem depends."
- The same report proves the theorem: line 429 "Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau"; line 773 "| `Zeta23.BL.bohrLandau_full` | Classical.choice, Quot.sound, propext |".
- The same sentence is in the reports of runs 7 and 8, where it is true (run 8 proves only delta > 1/6; `bohrLandau_full` does not occur in run 8's report).
- Run 10's report carries the corrected prose: "Bohr–Landau (1914) is PROVED on this tree — `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau`: for every δ > 0 the nontrivial zeros with 0 < Im ρ ≤ T and |Re ρ − 1/2| ≥ δ, with multiplicity, number ≤ C_δ·T for T ≥ 2".
- `REPO/NOTICE` records the generator fix: "scripts/z23_density_check.py of add-on v5 corrects a stale sentence of the v2–v4 report generator (DEPOSIT_MAP.md §10, Erratum)."
- `REPO/README.md` item 10 repeats the erratum: "Erratum: the run 9 report's "How to read this" block carries a stale sentence ("Bohr–Landau itself is NOT proved"), true for runs 7–8 and false for run 9, as that report's own axiom table shows; the verdict, audit and hashes of run 9 are unaffected, the generator is corrected in add-on v5, and the bundle is not altered".

A second stale phrase in the same block, not mentioned by the erratum (the block is identical in the reports of runs 7, 8 and 9): "`Zeta23/BL/*.lean`: a Dirichlet-polynomial mean-value inequality (two forms) and Jensen-disc inequalities, Mathlib-only, the first lemmas toward Bohr–Landau." By run 8 `Zeta23/BL/` also holds `BohrLandauPartial.lean`, and by run 9 `BohrLandauClosure.lean` (run 10's job line lists both as "compiled earlier in this tree (v2/v3/v4 runs)"), so "the first lemmas toward" understates runs 8 and 9. It is prose only.

## 8. Cross-check of REPO/README.md (and DEPOSIT_MAP.md) against the receipts

### 8.1 Agreements (checked item by item)

- Run 1: README "Verdict **PASS**, cold run, Lean kernel, 2026-10-27, 1 h 54 min" against receipt "**Verdict: PASS**", "Run type | cold", "Wall clock | 1:54:37", start 2026-10-27T17:43:45Z. Agrees.
- Run 2: README "17 statements ... Verdict **PASS**, cold run, Lean kernel and NanoDa, 2026-10-28, 21 min" against receipt "Run: cold, started 2026-10-28T11:08:56Z ... wall clock 21:01.50". Agrees.
- Runs 3 to 6: README theorem and definition counts 40; 43 and 17; 87 and 41; 62 and 23, and the dates 2026-10-28, 2026-10-28, 2026-10-29, 2026-10-29. Agree with the reports (run 3's 17 definitions are discussed in D1).
- Runs 7, 9, 10, 11: README counts 124/66, 334/81, 480/98, 534/110 and dates 2026-11-03, 2026-11-04, 2026-11-04, 2026-11-11. Agree.
- README pins table: both commits, both Lean versions, both Mathlib commits, both Comparator commits (`d03acab1`, `75c730e9`), both lean4export commits (`076e8e57`, `9fb131bb`), NanoDa `68d5ca9d`, landrun `811cfff5` (static), and the four statement-file hash prefixes `065f8c9a…`, `6f2a4ba9…`, `8f9a7e7b…`, `610d95c6…`. All agree with the receipts (section 2).
- README contents table: every eight-character hash prefix agrees with `CHECKSUMS.sha256`.
- README's quotation "From `RECEIPT.md`" uses the receipt's words exactly; it runs the four bullets of "What it does not mean" together as one paragraph. Its quotation "From `MNF_LIBRARY.md`" is the second bullet of "How to read this", verbatim.
- DEPOSIT_MAP section 10 table (runs 7 to 11): labels, tarball names, hash prefixes, counts 124 (66), 270 (76), 334 (81), 480 (98), 534 (110) and UTC windows 21:05–21:13, 22:03–22:09, 00:52–00:58, 14:38–14:45, 00:02–00:17 all agree with the receipts.
- DEPOSIT_MAP header: v3 MNF receipt "ACCEPTED 2026-10-29 05:56–06:10 UTC, 87 theorems, 41 definitions" and the four full hashes it prints (`023d7ada…159a`, `0d1919e4…f56a`, `37a806b2…f863`, `ca07a500…a90c`) agree with the receipts and with `CHECKSUMS.sha256`.

### 8.2 Discrepancies and stale statements

- D1 (definitions in run 3). README lists run 3 as "40 theorems, ACCEPTED" and says the library was judged "with its own challenge file (every proof `sorry`) and, from v2 on, every definition compared by name, type and body". The receipt says "40 theorems, 17 definitions named in the challenge config". Not a contradiction, but the paper must not give run 3 a "definitions compared by body" entry: its 17 definitions were listed as holes (section 3.3). `REPO/zenodo-metadata.json` is wrong on this point for run 3: "was judged by Comparator as a further run with its own challenge file and every definition compared by body: 40, 43 and 87 theorems on OpenAI's tree (v1, v2, v3 ...)".
- D2 (run 8, definitions and kernels). README item 8: "270 theorems, ACCEPTED 2026-11-03" gives no definition count and no kernels. Receipt: "270 theorems named in the challenge config; 76 definitions in the challenge" and "Lean's kernel and NanoDa replayed the solution". README item 9 likewise omits the kernels; the receipt of run 9 has both.
- D3 (cold or warm, runs 7 to 11). `REPO/DEPOSIT_MAP.md` section 10 opens: "Five further Comparator runs on the zeta23 checkout that run 2 checked (cold under the kit's launcher, AF_UNIX denied, Lean kernel and NanoDa, every definition compared by body)." Read as describing the five runs, "cold" disagrees with the receipts: all five type files read "warm" and every report says "warm with respect to the Zeta23 library ... cold for every module v<N> introduces". The working ledger uses "cold" the same way (`REPO/notes/density-field-2026-11-03/DENSITY_LEDGER.md`: "**Cold run of add-on v2 on the qrh account: MNF_DENSITY=ACCEPTED**"), apparently to distinguish the run on the `qrh` account from the dry run on the author's account. Prefer the receipt: warm, with the stated qualification.
- D4 (cold or warm, runs 3 to 5). README: "The MNF runs are warm with respect to the external proof files by design ...; they are cold with respect to the library itself." The bundles of runs 3 to 5 do not record a run type at all (no `.type` file, no `attempt_started_*` fact, the words absent); the status follows from the kit log and the build log (section 3.3). `REPO/zenodo-metadata.json` says "Warm/cold status, kernels used and every deviation are stated in each receipt", which is not true of the three bundles of runs 3 to 5.
- D5 (header counts). README line 3: "One record, seventeen artifacts, eight receipts". The record now holds 21 tarballs, of which 11 are receipt bundles (`CHECKSUMS.sha256`, 21 lines ending `.tar.gz`, 11 ending `receipt.tar.gz`). Stale.
- D6 (header date). README line 3: "Joey Messina, 2026-10-29; extended 2026-11-04." Run 11 is dated 2026-11-11 in the same file. Stale. Likewise the title of DEPOSIT_MAP section 10, "(2026-11-03/04)", although its table includes run 11 of 2026-11-11.
- D7 (dates of runs 7 and 8). README: "Added 2026-11-04 (runs 7–10) and 2026-11-11 (run 11)". Runs 7 and 8 ran on 2026-11-03 UTC (the same README dates them "ACCEPTED 2026-11-03" in items 7 and 8). The "added" date is the date of the README edit, not of the runs.
- D8 ("five bundles"). README: "(Six runs, five bundles: run 2 and run 6 share the zeta23 tree and are two bundles of one add-on.)". Runs 1 to 6 have six receipt tarballs and five kit or add-on tarballs; the sentence is true only if "bundles" means the latter, and its second half calls the receipts "two bundles". `REPO/zenodo-metadata.json` says "Five receipt bundles", which is one short for runs 1 to 6 and describes only the record of 2026-10-29.
- D9 (add-on manifest hash of run 2). Run 2's receipt records "`addon_manifest_sha256` | a20b1b1d9e5dff52cbd6aaef82119172ef87cf5ab160e039d15f94f73f0b1086" (recorded 2026-10-28T11:02:12Z). The `MANIFEST.sha256` inside the deposited `qrh-zeta23-addon.tar.gz` has sha256 `0c37cc131458750d46b23d272f4adb8813a373618aa16724b096ef609ae09bc8` (computed in this session from the tarball and from `REPO/sources/qrh-zeta23-addon/MANIFEST.sha256`). So the add-on that launched run 2 was not byte-for-byte the deposited tarball. The deposited add-on contains the files of the later step (run 6: `MNF/RH/Zeta23Restated.lean`, `scripts/z23_mnf.sh`), which is consistent with the add-on having been extended between run 2 (2026-10-28) and run 6 (2026-10-29); no document read in this session says so, and the hash `a20b1b1d…` occurs nowhere in REPO outside the facts files. What run 2 judged is unaffected (the upstream commit, the three statement-file hashes and the tool hashes are all in the receipt), but the sentence "every receipt bundle carries the exact job script that ran" is the safe one; "run 2 was launched by the deposited add-on tarball" cannot be claimed.
- D10 (do the receipts cite the tarball hashes). README, section "sources/": "The tarballs in the root are canonical: their hashes are the ones the receipts cite". No receipt bundle contains the sha256 of any kit or add-on tarball (searched for the eight-character prefix of all ten). The receipts cite per-file hashes and listing hashes; the link from a receipt to its add-on tarball is made by `verify_deposit.sh`, as README says elsewhere ("checks that the library files each MNF receipt hashed are byte-identical to those in the matching add-on tarball").
- D11 (sources list). README, section "sources/", names `sources/qrh-comparator-kit`, `sources/qrh-mnf-addon`, `-v2`, `-v3`, `sources/qrh-zeta23-addon`; the directory also holds `qrh-zeta23-addon-v2` to `-v6`. Stale.
- D12 (who did what). README: "The Lean files of runs 7–9 (2026-11-03/04) were written with Claude Code ..."; runs 10 and 11 are not mentioned there. `REPO/NOTICE` covers them ("Added 2026-11-04 (run 10, add-on v5)", "Added 2026-11-11 (run 11, add-on v6)").
- D13 (zenodo-metadata.json). The file describes the record of 2026-10-29 (runs 1 to 6, `upload_type` "dataset") and says the library proves the density-one statement "with two literature facts as explicit hypotheses"; README says both are theorems on the zeta23 tree since runs 7 and 9. It is frozen in `CHECKSUMS.sha256`; a new deposit needs new metadata.
- D14 (run numbering). README numbers the runs 1 to 11 in an order that is not chronological (section 1, first note). The numbering is consistent across README, DEPOSIT_MAP and NOTICE; the receipts carry no run numbers, only labels.

None of D1 to D14 touches a verdict, a count of theorems, a time stamp or a tarball hash: on those the README, the DEPOSIT_MAP and the receipts agree throughout.

## 9. Other notes the receipts record

- Run 1, upstream moved: "OpenAI repository head at fetch time | 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (NEWER than pinned)". The run is of the pinned commit.
- Run 1, tool versions of record: "elan 4.2.4 (227caca13 2026-08-25)", "go version go1.24.7 linux/amd64" (`EX/qrh-receipt/receipt/facts.tsv`); run 2: "rustc 1.93.1 (01f6ddf75 2026-02-11) (built from a source tarball)" for building NanoDa.
- Run 1, dependencies: "Compiled dependency files before the run | 106968 files, digest `a12ec201639976add458307f6cfd34fe9592474b706e6b1ea0a8378cc18ee93f`"; fact "deps_added_during_run	76".
- Run 2, dependencies: "`deps_compiled_files` | 52108", "`mathlib_oleans` | 8313".
- Second statement on the OpenAI tree, not run: `EX/qrh-receipt/receipt/PINS.env`: `OAI_CONFIG_DIRICHLET="ComparatorChallenges/DirichletSevenEighths.json"   # optional second run, same solution module`. No receipt for it is in the record. Likewise on the zeta23 tree: `Z23_CONFIG_XIPRIME="comparator-xiprime.json"                     # the second topic (6 statements); not run by this add-on`.
- The dry runs on the author's account mentioned by the add-on READMEs and the ledger are not among the eleven runs and are not receipts: `REPO/sources/qrh-zeta23-addon/README.md`: "It is not the receipt: the work directory, user and session differ".
- Two Comparator acceptances mentioned in the record lie outside the eleven runs and have no bundle among the eleven: the standalone Sturm–Liouville project (`REPO/README.md`: "accepted again on 2026-11-03, Lean kernel and NanoDa") and the MNF2 algebra at the OpenAI pin (`REPO/DEPOSIT_MAP.md` section 10: "the MNF2 package's algebra (also ACCEPTED at the OpenAI pin on 2026-11-03)"). Nothing in `WORK/extracted` documents either.

## 10. Open questions

1. D9: which version of the zeta23 add-on launched run 2 (manifest hash `a20b1b1d…`), and is it archived anywhere? If not, the paper should say that run 2's add-on is documented by the receipt's job script and pins, and that the deposited tarball is the version that also carries run 6's step.
2. D3 and D4: the paper's table should use the receipts' wording (runs 1 and 2 cold; runs 6 to 11 warm with the stated qualification; runs 3 to 5 on a copy of the compiled run 1 tree, no run type recorded). Does the author want the DEPOSIT_MAP sentence "(cold under the kit's launcher, ...)" reworded before the deposit, given that DEPOSIT_MAP is named authoritative for framing?
3. Section 6.4: the kit's protocol says "only a cold run can end in PASS" and labels a warm acceptance of the same proof "PROVISIONAL". Should the paper state explicitly that the ACCEPTED runs are warm with respect to the upstream trees and therefore rest on the two cold PASS runs plus the unchanged-files checks, rather than being independent cold certifications?
4. D1: run 3 compared definitions as holes only. Should the paper's table show "17 (names and types only)" for run 3, or drop the definition count for that run as README does?
5. D5, D6, D11, D12, D13: README header counts, README "sources/" list, README "Who did what" and `zenodo-metadata.json` are stale relative to eleven runs. They are outside WORK and were not modified. Are they to be updated before the Zenodo deposit (which would change `CHECKSUMS.sha256` for `zenodo-metadata.json`)?
6. Definitions compared in runs 1 and 2: the receipts give no count. The paper's table should say "none listed" or "no definition holes" rather than a number.
7. The controls (6 accepted, 15 rejected) were run with Comparator v4.34.0 on Lean v4.34.1 only; the checker used for runs 2 and 6 to 11 (v4.33.0-rc2) was exercised on one upstream test project in a dry run on the author's account, per the add-on README, not in a receipt. Should the paper say so in its threats-to-validity discussion?
