// The harness pulls this file in with #include, which does not pass on the template's definitions; rtable needs this import.
#import "/template.typ": rtable

= The checking protocol <sec-the-checking-protocol>

All eleven runs were made on one laptop, in a single boot, with the launcher of one _kit_, written for run 1 and documented in its `docs/PROTOCOL.md`; nine _add-ons_ reuse that launcher for the later runs.
Who and what produced the scripts and documents is stated in~@sec-authorship-and-use-of-ai-tools.

== The two artifacts under test and their trusted statement files <sec-the-two-artifacts-under-test-and-their-trusted-statement-fil>

Run 1 judged `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in OpenAI's repository~@openai-math at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, not at the newer upstream head.
The trusted statement is the repository's own challenge file, unmodified: nine lines that import only Mathlib~@mathlib and state the theorem with `sorry` for its proof.

Run 2 judged the 17 theorems named in `zeta23/comparator.json` of Anthropic's repository~@anthropic-formal-math at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, the formalization of the theorem of Alpöge and Furman~#cite(<alpoge-furman>).
They are stated in the project's own `Challenge.lean`, unmodified, which imports only Mathlib.

Both statement files are pinned by sha256.
Neither run is claimed as a first verification: OpenAI's repository ships the Comparator configuration with an instruction for running it, and run 2’s receipt calls that run "an independent repetition of a check Anthropic reports having run itself".
The kit's protocol records that OpenAI's own catalogue of these formalizations, `lean/formalization.yaml`, "carries `review: status: unchecked`".

#rtable(
  columns: (auto, 1fr, 1fr),
  align: (left, left, left),
  header: ([], [OpenAI tree (runs 1, 3 to 5)], [Anthropic tree (runs 2, 6 to 11)]),
  [Repository, commit], [openai/math `adc7f1241b42`], [anthropics/formal-math `16a5ce41304f`, `zeta23/`],
  [Lean], [v4.34.1], [v4.33.0-rc2],
  [Mathlib], [`d13f23b723b8`], [`51e6992efd06`],
  [Comparator], [v4.34.0 `d03acab154d2`, built with Lean v4.34.1], [v4.33.0-rc2 `75c730e9b6ef`],
  [lean4export], [`076e8e57707e`], [`9fb131bb100e`],
  [NanoDa], [not used], [robsimmons/nanoda\_lib `68d5ca9db226`],
  [landrun], [`811cfff51cea`, version 0.1.18, static], [the same binary],
  [Statement files (sha256)], [`QuasiRiemannHypothesis.lean` `065f8c9a01d2`], [`Challenge.lean` `6f2a4ba95ab8`; `ChallengeDeps.lean` `8f9a7e7bb313`; `comparator.json` `610d95c6c84f`],
)

Hashes are cut to twelve hexadecimal digits; the receipt bundles of runs 1 and 2 give them in full.

== Comparator and what an acceptance means <sec-comparator-and-what-an-acceptance-means>

Comparator~@comparator is the Lean FRO's judge for a statement one can read and a proof one cannot.
It takes a _challenge_ module, which states theorems without proofs, a _solution_ module, which states them with proofs, and a configuration naming the theorems, the permitted axioms and any definitions to be treated as holes.
It builds both modules inside a sandbox, exports them with lean4export~#cite(<lean4export>), checks that the statements are identical, definition by definition, and that the proofs use no axiom outside the permitted list, and replays the exported proofs through the kernel of Lean~#cite(<lean4>).
It prints `Your solution is okay!` and exits 0 only if all of this succeeds.
Runs 2 and 6 to 11 also replayed the export with NanoDa~#cite(<nanoda>), an independent type checker.
The permitted axioms were always `propext`, `Quot.sound` and `Classical.choice`.

An acceptance means exactly this: each named statement of the solution is the statement of the challenge, with every definition it mentions identical on both sides; the proofs rest on no other axiom; and the kernel, or both kernels, re-checked the exported proof terms and all they depend on, Mathlib's part included.
It does not mean that a Lean statement says what a paper's English says, and it says nothing about the Riemann hypothesis.
By the kit's protocol, the mathematics of OpenAI's argument was not read.
Nor was the paper of Alpöge and Furman~@alpoge-furman compared with the statements of zeta23: in the README's words, "this record does not check the paper, only the Lean statements".

A definition listed as a hole is compared by name, type, universe levels and safety level only, not by body.
Run 3 listed its 17 definitions as holes; run 2 and runs 4 to 11 list none, so there the body of every definition that a claimed statement refers to is compared.
Run 1’s challenge file defines nothing of its own, and its statement uses only what Mathlib provides, the function `riemannZeta` included; OpenAI's configuration is pinned by sha256, and the bundle holds no copy of it.
The standalone repository was archived on 2026-10-20, a week before run 1, and since 2026-10-14 its README has advised migrating to `lake comparator` and `lake check`, which ship with Lean 4.35.0~#cite(<lean-4-35>).
The two artifacts pin Lean 4.34.1 and 4.33.0-rc2, both older than that release, and the runs use the standalone tags v4.34.0 and v4.33.0-rc2.

== The trust base <sec-the-trust-base>

The results trust Lean's kernel and released toolchain, and NanoDa where it ran; Comparator and lean4export; Mathlib's definitions and its prebuilt cache, which was downloaded, not compiled in the sandbox; the challenge files and the projects' build configuration; the sandbox (landrun, Landlock, systemd, the Linux kernel); and the machine and its operator.
In the protocol's words, "A receipt is a record, not a cryptographic proof."
The solution is not trusted: only Comparator compiles it, inside the sandbox.

On the OpenAI tree Comparator and lean4export, having no release for Lean 4.34.1, were built from their v4.34.0 sources with that toolchain.
That this checker rejects what it should was tested with 21 control projects, five written for the kit (a wrong statement, an extra axiom and a `sorry` among them) and sixteen from Comparator's own regression suite: 6 were accepted and 15 rejected, as expected, minutes before run 1.
They were not repeated with the v4.33.0-rc2 checker of runs 2 and 6 to 11, and four upstream projects that need NanoDa were skipped; for those runs they are evidence about the launcher and the sandbox only.

== The sandbox and the launcher <sec-the-sandbox-and-the-launcher>

Every Comparator launch of the eleven runs and of the controls goes through one script, as an unprivileged user without sudo rights, in a systemd user unit with four properties: `RestrictAddressFamilies=~AF_UNIX`, which the kit says Comparator's README asks for; `SystemCallArchitectures=native`, so that 32-bit system calls cannot bypass it; `OOMPolicy=continue`, so that an exit code survives an out-of-memory kill; and `LimitSTACK=1G`, for the recursive kernel replay.
For its build and export steps Comparator calls landrun~#cite(<landrun>), which uses Linux's Landlock: sandboxed code may read the whole disk, write only inside its build folder and `/dev`, and open no TCP connection.

Before a launch the scripts probe by behavior that a write outside the allowed directory, an outbound TCP connection and, under the unit's properties, the creation of an AF\_UNIX socket are denied.
The job then records, from inside its unit, that it could not create such a socket; all eleven runs record this, with the same boot identifier.
Runs 3 to 5 record no probes of their own; run 1’s, from the same boot, stand for their tree.

== Cold and warm runs <sec-cold-and-warm-runs>

In the kit's vocabulary a _cold_ run starts from a tree in which nothing of the challenge or the proof has been compiled, and only a cold run can end in the verdict PASS; an acceptance in a _warm_ re-run of a used tree is labeled PROVISIONAL, because a hostile proof compiled earlier could have prepared the ground.

Runs 1 and 2 are cold and carry the verdict PASS.
Runs 3 to 11 judge new files on a tree in which an earlier run had already compiled the upstream proof.
Their reports say ACCEPTED.
In the kit that word names the outcome of an attempt, from which a verdict is derived; the add-ons use it as their result, and it is not a verdict of the kit.
By the kit's own rule these runs are warm: its receipt generator says of a second statement judged on OpenAI's tree after the main run that "it reuses the proof files the main run compiled", so that "it can be PROVISIONAL at best"; the README says of the library runs that they are "warm with respect to the external proof files by design"; and of the ways in which files compiled earlier could prepare the ground the protocol says: "The kit closes none of these for warm runs; it only labels the result."
With respect to everything compiled before the run, ACCEPTED therefore certifies no more than the kit's PROVISIONAL would, and this paper keeps it apart from PASS for that reason.

What limits the exposure is recorded run by run.
Runs 3 to 5 each start from a fresh copy of run 1’s compiled tree, made after run 1’s receipt had recorded its trusted inputs, proof sources and checker binaries as unchanged and after the launch script had verified the checkout again, and compile only the add-on's modules; their bundles record no run type.
Runs 6 to 11 work in run 2’s checkout and are recorded as warm; each is cold only for the modules its add-on introduces, which the launch script enforces.
The five library modules of run 6 were therefore already compiled in runs 7 to 11, and in runs 8 to 11 so were the modules of the earlier layer runs (run 11 records fifteen of them, and its script requires only `Cube` and its mirror to be uncompiled); Comparator's export and the kernel replay still covered every claimed theorem with all it depends on.
(Until its revision of 2026-11-11 the record's register called runs 7 to 11 "cold"; the receipts are followed here.)

A report says ACCEPTED only if Comparator exited with code 0 after its acceptance line (and NanoDa's where enabled), the job ran in the restricted unit with AF\_UNIX denied, the audit compile was clean (see~@sec-lessons-learned) and, from run 4 on, the configuration has no definition holes.
For everything compiled before them (the upstream libraries and, in runs 7 to 11, the modules of this work that earlier runs had compiled), these nine acceptances rest on the runs that compiled it.

Most of the receipted runs were not the first time Comparator judged their statements.
Before run 2 a dry run of the add-on's scripts on the author's own account, in a separate work directory, had ended with Comparator accepting the 17 statements (README of the add-on, which adds that two findings of that run were folded back into the scripts; the files of the dry run are not in the record).
Before runs 4 and 5 the statements that need only Mathlib were judged by a locally built Comparator on the author's own account, outside the kit's systemd unit (README files of add-ons v2 and v3; in the words of the former, "that pre-check is not the receipt").
Before each of runs 7 to 11 the same configuration had been accepted on the author's account with both kernels, in what the README of each add-on calls a "warm pre-check, outside the launcher"; the notes hold the logs of such pre-checks and, for each of these five add-ons, the report of a dry run that ended ACCEPTED.
A receipted run thus repeated, as the unprivileged user and under the kit's launcher, an outcome already seen in whole or, for runs 4 and 5, in part, and the failures recorded in~@sec-lessons-learned all occurred in pre-checks.
Apart from the controls, of which fifteen were rejected as intended, the record holds no receipted run that ended REJECTED.

== Receipts and the verifier <sec-receipts-and-the-verifier>

Artifacts, tools and toolchains are pinned by commit or sha256.
Runs 1 and 2 checked them before the run and again after it (run 1: checkout, trusted inputs, proof sources, checker binaries and kit; run 2: trusted files, compiled dependencies, their build configuration, tools and add-on).
The later runs checked less.
Runs 3 to 5 verified OpenAI's checkout and the add-on's manifest before the run and recorded no check after it.
Runs 6 to 11 checked, before the run, the add-on's manifest and five pinned files of the zeta23 checkout (the two statement files, the configuration, the dependency manifest and the toolchain file) and, after it, the files the launch script had hashed (the added sources, their mirrors, the configuration, the audit file and the lakefile) and the three statement files; the checker and toolchain binaries were not hashed again after run 2, except that runs 7 to 11 each record the hash of the NanoDa binary, the same as in run 2.
The kit and each add-on are checked against their own manifests.
Each run leaves a bundle with the exact job script, Comparator's full log, time stamps, exit code, time-stamped facts and a report.
For runs 1 and 2 the report is a receipt that prints the whole challenge file and the verdict; for runs 3 to 11 it gives a result line, the statements as Lean's `#check` prints them, a table of axiom reports and a block of fixed prose, "How to read this", that the report generator carries, beside a sha256 listing of the files judged.
In runs 7 to 11 the statement list omits those Lean prints with a leading `@` (279 of 534 in run 11); the bundle's `audit.out` has all.

The record holds 21 tarballs (the kit, nine add-ons, eleven receipt bundles) and a checksum file.
Its script `verify_deposit.sh`, which runs neither Lean nor Comparator, re-derives the hashes, re-reads each verdict from the bundles and compares the judged Lean sources with the add-on tarballs; @sec-verifying-the-record-offline says exactly what it checks.

A gap in provenance: run 2’s receipt records an add-on manifest hash (`a20b1b1d…`) other than that of the deposited add-on (`0c37cc13…`), which also carries run 6’s step, so another version launched run 2.
The evidence is that it was an earlier one: the pins file copied into run 2’s bundle is the deposited add-on's file without its last six lines, the block added for run 6.
That version is not in the record; what run 2 judged is fixed by its receipt.

== Challenges as module-for-module mirrors <sec-challenges-as-module-for-module-mirrors>

For runs 3 to 11 a generator script writes the challenge from the author's sources.
From run 4 on, each source module gets a _mirror_: the module itself with every non-Mathlib import replaced by the import of the corresponding mirror or dropped, and every proof replaced by `sorry`; everything else stays verbatim and in order.
Run 11 has 18 mirrors; its configuration lists theorems of 13 of them, the _claim set_, and the other five supply definitions.
In runs 3 to 5 the challenge files were generated beforehand and ship in the add-on tarball, under its manifest; in runs 6 to 11 they are generated in the tree at run time.
The receipts list their sha256 (run 4’s lists only the root challenge file and the configuration).

Two consequences follow.
First, the challenge of runs 3 to 11 is derived mechanically from the solution's own sources, so the comparison of statements in these runs compares the library with a copy of itself: it cannot detect a statement that is wrong or vacuous.
What these runs add to an ordinary build is the sandboxed compile; the check that the claimed statements, from run 4 on with the bodies of the definitions they use, can be stated in challenge modules that import nothing but Mathlib and one another; the axiom check; and the kernel replay.
Second, the challenge files of runs 6 to 11 are in no bundle and in no add-on tarball.
Those of run 11 can be read in `notes/density-field-2026-11-03/zeta23-tree/MNFChallengesD/`; that copy has the sha256 values of the receipt's listing.
For runs 6 to 10 a reader has to regenerate them with the generator of the add-on concerned.
This was done in a scratch copy while this paper was reviewed, for each of runs 6 to 11, with the generator of the add-on on that add-on's sources, and the generated files had the sha256 values of the receipt's listing; the verifier does not make this comparison.

== Lessons learned <sec-lessons-learned>

*Mirror module by module.*
Run 3 used one challenge file, with holes.
When bodies were first compared, a pre-check of 2026-10-28 was rejected although the definitions were textually identical: Lean abstracts proof terms inside a definition into auxiliary lemmas named `<decl>._proof_n` and reuses one already created in the same module, so the single file gave `LeftCriticalStrip` the auxiliary lemma of `ShiftedZeroSpectrum`.
The mirror layout is the remedy.

*No theorem as a term in a claimed statement.*
Comparator compares a theorem reached from a statement in full, proof included, and in a challenge that proof is `sorry`; a pre-check of the same day found this.
The usual case is `.toFinset` of a finiteness theorem; the remedy is to take finiteness as a hypothesis.
(The logs of these two pre-checks are not deposited; the add-ons' documentation describes them.)

*Names a mirror cannot see.*
A claimed statement may mention neither a zeta23-internal name, which a mirror does not import, nor a constant fixed by `Classical.choose`, nor, by the previous lesson, a finiteness proof as a term.
The run 11 generator therefore omits 27 declarations of `MNF.RH.ReservoirMass` and 2 of `MNF.RH.Cube` (the pair-measure module) and claims existential statements instead; 13 helper lemmas of `MNF/Extension/InjectionEjection.lean`, named `aux_`, are in its mirror but not in the claim set.
The first pre-check of the pair-measure module failed to build: two unclaimed `aux_` lemmas had been copied into the mirror ("Unknown identifier `Zeta23.reflect`").
No proof was rejected, and the fix was in the generator alone; the hash of `Cube.lean` is the same in both pre-check logs and in the receipt.

*Two layers of axiom audit.*
An ordinary compile believes the compiled files it imports: when the kit was tested, a compiled file that merely claimed OpenAI's theorem made such a compile report success.
The audit compile (`#print axioms` and `#check` for each claimed theorem, compiled in the sandbox after the run) is therefore only a second layer under Comparator's axiom check and kernel replay: it must exit 0 with no error, no `sorry` in its output and exactly one report per claimed theorem, within the three axioms.
The tree of runs 7 to 11 keeps two `sorry` lemmas outside the claim set.

*Generated prose can lag behind Lean's output.*
The run 9 report says "Bohr–Landau itself is NOT proved", a sentence of fixed generator prose inherited from runs 7 and 8, where it was true, although the same report lists the theorem with the standard axioms (see~@sec-errata).
Where a report's prose and the statements Lean printed differ, the statements govern.
