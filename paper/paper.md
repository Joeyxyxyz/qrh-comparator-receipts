# Receipted Comparator Checks of Two Lean Proofs on Zeros of the Riemann Zeta Function, with Formalizations of the Bohr–Landau Theorem and a Zero-Density Estimate

Author: Joey Messina
Date: 2026-11-11 (UTC)
Repository: https://github.com/Joeyxyxyz/qrh-comparator-receipts

## Abstract

This paper reports eleven runs of Comparator, the Lean FRO's proof judge, under a pinned, sandboxed protocol, each with a published receipt. Two runs repeat checks of public Lean 4 proofs on zeros of the Riemann zeta function: OpenAI's theorem that zeta has no zeros with real part above 7/8, and zeta23, Anthropic's formalization of Alpöge and Furman's theorem that more than two thirds of the zeros are simple and on the critical line (as judged: for every $\varepsilon > 0$, a proportion at least $2/3 - \varepsilon$ at all large heights). Both ended in PASS: the pinned proof was accepted by the Lean kernel (and NanoDa for zeta23) against the pinned statement file, using only the axioms propext, Quot.sound and Classical.choice. Nine further accepted runs judge Lean files added to the verified trees: the author's library MNF.RH, and a layer formalizing the Bohr–Landau theorem, a zero-density estimate with a power saving weaker than Carlson's, a bound for the zeros' total displacement from the critical line that is far weaker than Littlewood's and Selberg's, two equivalences that restate, and do not prove, the Riemann hypothesis with simplicity and a zero-free-strip hypothesis of the author's library, and the absence of real zeros of zeta in (0,1). The analytic results are classical or weaker than classical ones; Lean zero-density estimates with stronger exponents, which imply the one-sided Bohr–Landau bound, were registered earlier by others, and earlier Lean proofs of the absence of real zeros exist. Nothing here proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line. The layer's Lean files (apart from four supporting files, which the author supplied), parts of MNF.RH, the scripts and this text were produced with Claude Code, Anthropic's coding agent, under the direction of the author, who conceived the MNF framework, set the goals, operated every run and is responsible for the claims.

Keywords: Riemann zeta function; zeros of the zeta function; Lean 4; Mathlib; Comparator; proof checking; reproducibility; Bohr–Landau theorem; zero-density estimate; AI-assisted formalization

## Introduction

This paper reports eleven runs of Comparator [@comparator], the Lean FRO's proof judge, made on one laptop between 2026-10-27 and 2026-11-11 (UTC) under a pinned, sandboxed protocol, each with a published receipt. Two runs re-check public machine-checked Lean 4 [@lean4] proofs about the zeros of the Riemann zeta function $\zeta$. Nine judge Lean files placed on top of the two verified trees: the author's library `MNF.RH`, and a further layer that includes formalizations of classical theorems on the zeros. The receipts, the scripts and the Lean sources are in a public repository, called *the record* below.

A machine-checked proof moves trust from the argument to the statement file, the kernel, the permitted axioms and the build. A reader who cannot follow 486,490 lines of Lean can still read a nine-line statement file and ask whether the kernel accepted the proof against exactly that statement, and from which sources. An ordinary build does not settle this, because it believes the compiled files it imports; Comparator compares statements and definitions, checks the axioms, and replays the exported proof through the kernel. A second party who repeats that check from pinned sources leaves a receipt that others can audit: a record, not a cryptographic proof.

### The artifacts and what was added

The first artifact is OpenAI's theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` [@openai-math; @openai-qrh]: $\zeta(s) \neq 0$ for $\operatorname{Re} s > 7/8$. The second is zeta23 [@anthropic-formal-math], Anthropic's formalization of the theorem of Alpöge and Furman [@alpoge-furman] that more than two thirds of the zeros of $\zeta$ are simple and on the critical line; its statement file holds 17 theorems. The arXiv listing of [@alpoge-furman] states that the proof was discovered autonomously by Claude (Anthropic) and verified and communicated by the listed authors; OpenAI's repository describes its manuscripts and proof artifacts as produced by an internal OpenAI model. Runs 1 and 2 started from trees in which nothing of the challenge or of the proof had been compiled (the compiled dependencies, Mathlib's prebuilt cache among them, were in place; see *The trust base*) and ended with the verdict PASS.

Runs 3 to 6 judge `MNF.RH`, the library of the author's "Messina Nullification Framework" (MNF), on each verified tree. MNF is the author's name for the framework these Lean files are written for; its "nullification" is the thresholding map $x \mapsto x\cdot\mathbf{1}[\lvert x\rvert \geq \Delta]$ on real numbers. The library's central notion, the "spectral gap hypothesis" at threshold $\Delta$, says that every nontrivial zero $\rho = \beta + i\gamma$ has $\beta = 1/2$ or $\lvert\beta - 1/2\rvert \geq \Delta$; the library proves that this is exactly the absence of zeros with $1/2 < \operatorname{Re} s < 1/2 + \Delta$. Runs 7 to 11 judge a further layer on the zeta23 tree; run 11 names 534 theorems. These counts are of theorem names in the Comparator configuration, auxiliary lemmas included; 75 of the 124 of run 7, for instance, are bookkeeping for the author's operators, with "no analytic content" in the words of the record's register (`DEPOSIT_MAP.md`). Runs 3 to 11 reuse compiled files of the verified trees and report ACCEPTED, the add-ons' word; the kit's protocol reserves PASS for runs in which nothing of the challenge or the proof was compiled beforehand and would call these runs warm (see *Cold and warm runs*). This paper keeps the two words apart.

### Contributions

The counting functions are those of *Notation* below. Counts are with multiplicity $m(\rho)$, over nontrivial zeros with $0 < \gamma \leq T$: $N(\sigma, T)$ counts those with $\beta \geq \sigma$, and $N_{\mathrm{off}}(\delta, T)$ those with $\lvert\beta - 1/2\rvert \geq \delta$.

1. **A protocol and its receipts**: a kit that pins sources, statement files, toolchain and checker by commit or sha256 hash and runs Comparator unprivileged and sandboxed; 21 control projects, run with the checker of run 1; and a script, `verify_deposit.sh`, that re-checks the sha256 of every deposited tarball, re-reads every verdict from the bundles and compares the judged Lean sources of runs 3 to 5 and 7 to 11 with the add-on tarballs (*Verifying the record offline* says what it covers and what it does not).
2. **Two replications**: cold PASS verdicts for both external artifacts.
3. **The `MNF.RH` library and its register** (the file `DEPOSIT_MAP.md` of the record) of what is proved, conditional, open, and withdrawn: 40, 43 and 87 theorems on OpenAI's tree and 62 on the zeta23 tree. The gap hypothesis is equivalent to the Riemann hypothesis (RH) for $\Delta \geq 1/2$ and, given OpenAI's theorem, for $\Delta > 3/8$; the zero-free strip it asks for is known for no $\Delta > 0$.
4. **Formalizations of classical results** on the zeta23 tree, judged with both kernels. The Bohr–Landau theorem [@bohr-landau-1914]: for every $\delta > 0$ there is $C_\delta$ with $N_{\mathrm{off}}(\delta, T) \leq C_\delta T$ for all $T \geq 2$ (run 9). A zero-density estimate with a power saving, by Carlson's method [@carlson-1920]: for $1/2 < \sigma_1 < \sigma \leq 1$ there is $C$ with $N(\sigma, T) \leq C\, T^{1 - (2\sigma_1 - 1)^2/(2\sigma_1)} (1 + \log T)^3$ for all $T \geq 2$ (run 10). A bound for the total displacement of the zeros from the critical line: $\sum_{0 < \gamma \leq T} m(\rho)\,\lvert\beta - 1/2\rvert \leq A\, T (\log T)^{3/5}$ for all large $T$ (run 10). The absence of real zeros: $\zeta(\sigma) \neq 0$ for real $0 < \sigma < 1$ (run 11).
5. **Two equivalences** from the pair-measure module, which is bookkeeping about sums over ordered pairs of zeros (run 11): every nontrivial zero is simple and on the critical line if and only if no nontrivial zero is multiple or shares its ordinate with another nontrivial zero; and the gap hypothesis at $\Delta$ holds if and only if no two distinct zeros with $\lvert\beta - 1/2\rvert < \Delta$ share an ordinate.

### What is not claimed

- Nothing in this work proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line. A zero-density estimate is a count and excludes no individual zero.
- The two external theorems belong to OpenAI and to Anthropic and Alpöge–Furman. Runs 1 and 2 repeat a check that both repositories ship and that Anthropic reports having run; they are not first verifications. A PASS means exactly that the pinned Lean proof was accepted by the Lean kernel (and by NanoDa [@nanoda] in run 2) against the pinned statement file, using only the axioms `propext`, `Quot.sound` and `Classical.choice`. No result here combines the two theorems.
- The Bohr–Landau theorem (1914), Carlson's zero-density theorem (1920) and the absence of real zeros in $(0,1)$ are classical. The contribution is their formalization and receipted checking, with a weaker exponent than Carlson's and a far weaker displacement bound than those of Littlewood [@littlewood-1924] and Selberg [@selberg-1946]. Lean zero-density estimates with stronger exponents were registered earlier by Mark Lewko [@lewko-density-34; @lewko-density-32; @lewko-density-3917; @lewko-density-improved], and earlier Lean proofs of the absence of real zeros exist [@axiom-zetazeros; @hubbard-goldbach-lean].
- The equivalences of the pair-measure module and of `MNF.RH` relocate RH, simplicity and the gap hypothesis; each side is as open as the other. "MNF", "spectral gap hypothesis", "nullification", "reservoir", "cube" and "degenerate" are the author's words, not standard terminology; each is defined in standard terms in the section that uses it.
- The numerical experiments on the first 400 zeros are exploratory, reproduce known behavior of the kind predicted by the Gaussian unitary ensemble (GUE) of random matrix theory [@montgomery-1973; @odlyzko-1987], and prove nothing.
- No unaided authorship is claimed. The Lean files of runs 7 to 11, except four supporting files supplied by the author, the additions to `MNF.RH` listed in *Authorship and use of AI tools*, the scripts and the documents, this paper's text included, were produced with Claude Code [@claude-code], Anthropic's coding agent, under the author's direction; the author conceived the MNF framework, set the goals, operated every run, and is responsible for the claims.

### Plan of the paper

*The checking protocol* describes Comparator, the trust base, the sandbox, the receipts and the lessons learned. *The first six runs and the MNF.RH library* reports the two replications and the library with its register. *The density layer: counting vocabulary and the Bohr–Landau theorem* and *A zero-density estimate, the displacement bound and the pair measure* present the layer of runs 7 to 11, citing earlier Lean work where each result is stated. *A numerical illustration, limitations and errata* gives exploratory numerics on the first 400 zeros, the limitations of the work and the errata of the record. *Reproducing and verifying the record* says how to verify the deposited files and how to repeat a run, and *Authorship and use of AI tools* states who and what produced each part. Appendix A tabulates the eleven runs, and Appendix B lists the principal Lean theorems with their register tags.

### Notation

Throughout, $\rho = \beta + i\gamma$ is a nontrivial zero of $\zeta$, so that $0 < \beta < 1$, and $m(\rho)$ is its multiplicity. The critical line is $\operatorname{Re} s = 1/2$; a zero is on the line if $\beta = 1/2$ and off the line otherwise. Every counting function runs over the zeros with $0 < \gamma \le T$ and weights each zero by $m(\rho)$.

| Notation | Lean | Zeros counted |
|---|---|---|
| $N(T)$ | `MNF.RH.Ncount 0 T` | all |
| $N_0(T)$ | `MNF.RH.N0 0 T` | $\beta = 1/2$ |
| $N_{\neq}(T)$ | `MNF.RH.NOffLine 0 T` | $\beta \ne 1/2$ |
| $N_{\mathrm{off}}(\delta, T)$ | `MNF.RH.NOff δ 0 T` | $\lvert\beta - 1/2\rvert \ge \delta$ |
| $N(\sigma, T)$, $\sigma = 1/2 + \delta$ | `NRight δ T`, in `MNF.RH` and with the same body in `Zeta23.BL` | $\beta \ge \sigma$ |

Thus $N(T) = N_0(T) + N_{\neq}(T)$. Three further symbols are used. $G(\Delta)$ is the spectral gap hypothesis at threshold $\Delta$ defined above (Lean: `MNF.RH.SpectralGapHyp Δ`). $D(T) = \sum_{0 < \gamma \le T} m(\rho)\,\lvert\beta - 1/2\rvert$ is the total displacement of the zeros from the critical line (Lean: `MNF.RH.reservoirMass T`). $P(T)$ is the sum of $m(\rho)\,m(\rho')$ over ordered pairs of distinct zeros with equal ordinates in $0 < \gamma \le T$ (Lean: `MNF.RH.offDiagonalCoincidentMass T`). RH is the Riemann hypothesis; in Lean statements it is Mathlib's proposition `RiemannHypothesis`. In the proof sketches, $N$ without an argument is the length of a Dirichlet polynomial.

In Lean each of these counts is a sum `∑ᶠ` of the multiplicity (`zeta_order`) over the zeros of the window, and $D(T)$ and $P(T)$ are sums `∑ᶠ` of the same kind. Mathlib's `∑ᶠ` is 0 by convention when infinitely many of its terms are nonzero; in the words of `Counting.lean`, such a count "would be vacuously 0 on an infinite set". The reading as a count therefore needs the fact that a window contains finitely many zeros. That fact is the theorem `MNF.RH.zerosIn_finite`, judged in runs 5 and 6. In runs 7 to 11 it is not in the claim set; the claimed proofs that use it depend on it, and the kernel replay covers what the claimed proofs depend on (see *Comparator and what an acceptance means*). The statement file of zeta23 says of its own counting function that finiteness "is proved on the solution side, not assumed"; no statement of finiteness is among the 17 theorems of run 2.

Lean statements are printed verbatim. In them `↑` is a coercion (from natural to real numbers, or from real to complex numbers). The statements quoted from the report of run 5 are in signature form, with named binders; in those quoted from the run 11 bundle a leading `@` appears where the first argument of the theorem is implicit. Times are UTC. Run numbers are the record's and are not chronological (Appendix A).

## The checking protocol

All eleven runs were made on one laptop, in a single boot, with the launcher of one *kit*, written for run 1 and documented in its `docs/PROTOCOL.md`; nine *add-ons* reuse that launcher for the later runs. Who and what produced the scripts and documents is stated in *Authorship and use of AI tools*.

### The two artifacts under test and their trusted statement files

Run 1 judged `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in OpenAI's repository [@openai-math] at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, not at the newer upstream head. The trusted statement is the repository's own challenge file, unmodified: nine lines that import only Mathlib [@mathlib] and state the theorem with `sorry` for its proof.

Run 2 judged the 17 theorems named in `zeta23/comparator.json` of Anthropic's repository [@anthropic-formal-math] at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, the formalization of the theorem of Alpöge and Furman [@alpoge-furman]. They are stated in the project's own `Challenge.lean`, unmodified, which imports only Mathlib.

Both statement files are pinned by sha256. Neither run is claimed as a first verification: OpenAI's repository ships the Comparator configuration with an instruction for running it, and run 2's receipt calls that run "an independent repetition of a check Anthropic reports having run itself". The kit's protocol records that OpenAI's own catalogue of these formalizations, `lean/formalization.yaml`, "carries `review: status: unchecked`".

| | OpenAI tree (runs 1, 3 to 5) | Anthropic tree (runs 2, 6 to 11) |
|---|---|---|
| Repository, commit | openai/math `adc7f1241b42` | anthropics/formal-math `16a5ce41304f`, `zeta23/` |
| Lean | v4.34.1 | v4.33.0-rc2 |
| Mathlib | `d13f23b723b8` | `51e6992efd06` |
| Comparator | v4.34.0 `d03acab154d2`, built with Lean v4.34.1 | v4.33.0-rc2 `75c730e9b6ef` |
| lean4export | `076e8e57707e` | `9fb131bb100e` |
| NanoDa | not used | robsimmons/nanoda_lib `68d5ca9db226` |
| landrun | `811cfff51cea`, version 0.1.18, static | the same binary |
| Statement files (sha256) | `QuasiRiemannHypothesis.lean` `065f8c9a01d2` | `Challenge.lean` `6f2a4ba95ab8`; `ChallengeDeps.lean` `8f9a7e7bb313`; `comparator.json` `610d95c6c84f` |

Hashes are cut to twelve hexadecimal digits; the receipt bundles of runs 1 and 2 give them in full.

### Comparator and what an acceptance means

Comparator [@comparator] is the Lean FRO's judge for a statement one can read and a proof one cannot. It takes a *challenge* module, which states theorems without proofs, a *solution* module, which states them with proofs, and a configuration naming the theorems, the permitted axioms and any definitions to be treated as holes. It builds both modules inside a sandbox, exports them with lean4export [@lean4export], checks that the statements are identical, definition by definition, and that the proofs use no axiom outside the permitted list, and replays the exported proofs through the kernel of Lean [@lean4]. It prints `Your solution is okay!` and exits 0 only if all of this succeeds. Runs 2 and 6 to 11 also replayed the export with NanoDa [@nanoda], an independent type checker. The permitted axioms were always `propext`, `Quot.sound` and `Classical.choice`.

An acceptance means exactly this: each named statement of the solution is the statement of the challenge, with every definition it mentions identical on both sides; the proofs rest on no other axiom; and the kernel, or both kernels, re-checked the exported proof terms and all they depend on, Mathlib's part included. It does not mean that a Lean statement says what a paper's English says, and it says nothing about the Riemann hypothesis. By the kit's protocol, the mathematics of OpenAI's argument was not read. Nor was the paper of Alpöge and Furman [@alpoge-furman] compared with the statements of zeta23: in the README's words, "this record does not check the paper, only the Lean statements".

A definition listed as a hole is compared by name, type, universe levels and safety level only, not by body. Run 3 listed its 17 definitions as holes; run 2 and runs 4 to 11 list none, so there the body of every definition that a claimed statement refers to is compared. Run 1's challenge file defines nothing of its own, and its statement uses only what Mathlib provides, the function `riemannZeta` included; OpenAI's configuration is pinned by sha256, and the bundle holds no copy of it. The standalone repository was archived on 2026-10-20, a week before run 1, and since 2026-10-14 its README has advised migrating to `lake comparator` and `lake check`, which ship with Lean 4.35.0 [@lean-4-35]. The two artifacts pin Lean 4.34.1 and 4.33.0-rc2, both older than that release, and the runs use the standalone tags v4.34.0 and v4.33.0-rc2.

### The trust base

The results trust Lean's kernel and released toolchain, and NanoDa where it ran; Comparator and lean4export; Mathlib's definitions and its prebuilt cache, which was downloaded, not compiled in the sandbox; the challenge files and the projects' build configuration; the sandbox (landrun, Landlock, systemd, the Linux kernel); and the machine and its operator. In the protocol's words, "A receipt is a record, not a cryptographic proof." The solution is not trusted: only Comparator compiles it, inside the sandbox.

On the OpenAI tree Comparator and lean4export, having no release for Lean 4.34.1, were built from their v4.34.0 sources with that toolchain. That this checker rejects what it should was tested with 21 control projects, five written for the kit (a wrong statement, an extra axiom and a `sorry` among them) and sixteen from Comparator's own regression suite: 6 were accepted and 15 rejected, as expected, minutes before run 1. They were not repeated with the v4.33.0-rc2 checker of runs 2 and 6 to 11, and four upstream projects that need NanoDa were skipped; for those runs they are evidence about the launcher and the sandbox only.

### The sandbox and the launcher

Every Comparator launch of the eleven runs and of the controls goes through one script, as an unprivileged user without sudo rights, in a systemd user unit with four properties: `RestrictAddressFamilies=~AF_UNIX`, which the kit says Comparator's README asks for; `SystemCallArchitectures=native`, so that 32-bit system calls cannot bypass it; `OOMPolicy=continue`, so that an exit code survives an out-of-memory kill; and `LimitSTACK=1G`, for the recursive kernel replay. For its build and export steps Comparator calls landrun [@landrun], which uses Linux's Landlock: sandboxed code may read the whole disk, write only inside its build folder and `/dev`, and open no TCP connection.

Before a launch the scripts probe by behavior that a write outside the allowed directory, an outbound TCP connection and, under the unit's properties, the creation of an AF_UNIX socket are denied. The job then records, from inside its unit, that it could not create such a socket; all eleven runs record this, with the same boot identifier. Runs 3 to 5 record no probes of their own; run 1's, from the same boot, stand for their tree.

### Cold and warm runs

In the kit's vocabulary a *cold* run starts from a tree in which nothing of the challenge or the proof has been compiled, and only a cold run can end in the verdict PASS; an acceptance in a *warm* re-run of a used tree is labeled PROVISIONAL, because a hostile proof compiled earlier could have prepared the ground.

Runs 1 and 2 are cold and carry the verdict PASS. Runs 3 to 11 judge new files on a tree in which an earlier run had already compiled the upstream proof. Their reports say ACCEPTED. In the kit that word names the outcome of an attempt, from which a verdict is derived; the add-ons use it as their result, and it is not a verdict of the kit. By the kit's own rule these runs are warm: its receipt generator says of a second statement judged on OpenAI's tree after the main run that "it reuses the proof files the main run compiled", so that "it can be PROVISIONAL at best"; the README says of the library runs that they are "warm with respect to the external proof files by design"; and of the ways in which files compiled earlier could prepare the ground the protocol says: "The kit closes none of these for warm runs; it only labels the result." With respect to everything compiled before the run, ACCEPTED therefore certifies no more than the kit's PROVISIONAL would, and this paper keeps it apart from PASS for that reason.

What limits the exposure is recorded run by run. Runs 3 to 5 each start from a fresh copy of run 1's compiled tree, made after run 1's receipt had recorded its trusted inputs, proof sources and checker binaries as unchanged and after the launch script had verified the checkout again, and compile only the add-on's modules; their bundles record no run type. Runs 6 to 11 work in run 2's checkout and are recorded as warm; each is cold only for the modules its add-on introduces, which the launch script enforces. The five library modules of run 6 were therefore already compiled in runs 7 to 11, and in runs 8 to 11 so were the modules of the earlier layer runs (run 11 records fifteen of them, and its script requires only `Cube` and its mirror to be uncompiled); Comparator's export and the kernel replay still covered every claimed theorem with all it depends on. (Until its revision of 2026-11-11 the record's register called runs 7 to 11 "cold"; the receipts are followed here.)

A report says ACCEPTED only if Comparator exited with code 0 after its acceptance line (and NanoDa's where enabled), the job ran in the restricted unit with AF_UNIX denied, the audit compile was clean (see *Lessons learned*) and, from run 4 on, the configuration has no definition holes. For everything compiled before them (the upstream libraries and, in runs 7 to 11, the modules of this work that earlier runs had compiled), these nine acceptances rest on the runs that compiled it.

Most of the receipted runs were not the first time Comparator judged their statements. Before run 2 a dry run of the add-on's scripts on the author's own account, in a separate work directory, had ended with Comparator accepting the 17 statements (README of the add-on, which adds that two findings of that run were folded back into the scripts; the files of the dry run are not in the record). Before runs 4 and 5 the statements that need only Mathlib were judged by a locally built Comparator on the author's own account, outside the kit's systemd unit (README files of add-ons v2 and v3; in the words of the former, "that pre-check is not the receipt"). Before each of runs 7 to 11 the same configuration had been accepted on the author's account with both kernels, in what the README of each add-on calls a "warm pre-check, outside the launcher"; the notes hold the logs of such pre-checks and, for each of these five add-ons, the report of a dry run that ended ACCEPTED. A receipted run thus repeated, as the unprivileged user and under the kit's launcher, an outcome already seen in whole or, for runs 4 and 5, in part, and the failures recorded in *Lessons learned* all occurred in pre-checks. Apart from the controls, of which fifteen were rejected as intended, the record holds no receipted run that ended REJECTED.

### Receipts and the verifier

Artifacts, tools and toolchains are pinned by commit or sha256. Runs 1 and 2 checked them before the run and again after it (run 1: checkout, trusted inputs, proof sources, checker binaries and kit; run 2: trusted files, compiled dependencies, their build configuration, tools and add-on). The later runs checked less. Runs 3 to 5 verified OpenAI's checkout and the add-on's manifest before the run and recorded no check after it. Runs 6 to 11 checked, before the run, the add-on's manifest and five pinned files of the zeta23 checkout (the two statement files, the configuration, the dependency manifest and the toolchain file) and, after it, the files the launch script had hashed (the added sources, their mirrors, the configuration, the audit file and the lakefile) and the three statement files; the checker and toolchain binaries were not hashed again after run 2, except that runs 7 to 11 each record the hash of the NanoDa binary, the same as in run 2. The kit and each add-on are checked against their own manifests. Each run leaves a bundle with the exact job script, Comparator's full log, time stamps, exit code, time-stamped facts and a report. For runs 1 and 2 the report is a receipt that prints the whole challenge file and the verdict; for runs 3 to 11 it gives a result line, the statements as Lean's `#check` prints them, a table of axiom reports and a block of fixed prose, "How to read this", that the report generator carries, beside a sha256 listing of the files judged. In runs 7 to 11 the statement list omits those Lean prints with a leading `@` (279 of 534 in run 11); the bundle's `audit.out` has all.

The record holds 21 tarballs (the kit, nine add-ons, eleven receipt bundles) and a checksum file. Its script `verify_deposit.sh`, which runs neither Lean nor Comparator, re-derives the hashes, re-reads each verdict from the bundles and compares the judged Lean sources with the add-on tarballs; *Verifying the record offline* says exactly what it checks.

A gap in provenance: run 2's receipt records an add-on manifest hash (`a20b1b1d…`) other than that of the deposited add-on (`0c37cc13…`), which also carries run 6's step, so another version launched run 2. The evidence is that it was an earlier one: the pins file copied into run 2's bundle is the deposited add-on's file without its last six lines, the block added for run 6. That version is not in the record; what run 2 judged is fixed by its receipt.

### Challenges as module-for-module mirrors

For runs 3 to 11 a generator script writes the challenge from the author's sources. From run 4 on, each source module gets a *mirror*: the module itself with every non-Mathlib import replaced by the import of the corresponding mirror or dropped, and every proof replaced by `sorry`; everything else stays verbatim and in order. Run 11 has 18 mirrors; its configuration lists theorems of 13 of them, the *claim set*, and the other five supply definitions. In runs 3 to 5 the challenge files were generated beforehand and ship in the add-on tarball, under its manifest; in runs 6 to 11 they are generated in the tree at run time. The receipts list their sha256 (run 4's lists only the root challenge file and the configuration).

Two consequences follow. First, the challenge of runs 3 to 11 is derived mechanically from the solution's own sources, so the comparison of statements in these runs compares the library with a copy of itself: it cannot detect a statement that is wrong or vacuous. What these runs add to an ordinary build is the sandboxed compile; the check that the claimed statements, from run 4 on with the bodies of the definitions they use, can be stated in challenge modules that import nothing but Mathlib and one another; the axiom check; and the kernel replay. Second, the challenge files of runs 6 to 11 are in no bundle and in no add-on tarball. Those of run 11 can be read in `notes/density-field-2026-11-03/zeta23-tree/MNFChallengesD/`; that copy has the sha256 values of the receipt's listing. For runs 6 to 10 a reader has to regenerate them with the generator of the add-on concerned. This was done in a scratch copy while this paper was reviewed, for each of runs 6 to 11, with the generator of the add-on on that add-on's sources, and the generated files had the sha256 values of the receipt's listing; the verifier does not make this comparison.

### Lessons learned

**Mirror module by module.** Run 3 used one challenge file, with holes. When bodies were first compared, a pre-check of 2026-10-28 was rejected although the definitions were textually identical: Lean abstracts proof terms inside a definition into auxiliary lemmas named `<decl>._proof_n` and reuses one already created in the same module, so the single file gave `LeftCriticalStrip` the auxiliary lemma of `ShiftedZeroSpectrum`. The mirror layout is the remedy.

**No theorem as a term in a claimed statement.** Comparator compares a theorem reached from a statement in full, proof included, and in a challenge that proof is `sorry`; a pre-check of the same day found this. The usual case is `.toFinset` of a finiteness theorem; the remedy is to take finiteness as a hypothesis. (The logs of these two pre-checks are not deposited; the add-ons' documentation describes them.)

**Names a mirror cannot see.** A claimed statement may mention neither a zeta23-internal name, which a mirror does not import, nor a constant fixed by `Classical.choose`, nor, by the previous lesson, a finiteness proof as a term. The run 11 generator therefore omits 27 declarations of `MNF.RH.ReservoirMass` and 2 of `MNF.RH.Cube` (the pair-measure module) and claims existential statements instead; 13 helper lemmas of `MNF/Extension/InjectionEjection.lean`, named `aux_`, are in its mirror but not in the claim set. The first pre-check of the pair-measure module failed to build: two unclaimed `aux_` lemmas had been copied into the mirror ("Unknown identifier `Zeta23.reflect`"). No proof was rejected, and the fix was in the generator alone; the hash of `Cube.lean` is the same in both pre-check logs and in the receipt.

**Two layers of axiom audit.** An ordinary compile believes the compiled files it imports: when the kit was tested, a compiled file that merely claimed OpenAI's theorem made such a compile report success. The audit compile (`#print axioms` and `#check` for each claimed theorem, compiled in the sandbox after the run) is therefore only a second layer under Comparator's axiom check and kernel replay: it must exit 0 with no error, no `sorry` in its output and exactly one report per claimed theorem, within the three axioms. The tree of runs 7 to 11 keeps two `sorry` lemmas outside the claim set.

**Generated prose can lag behind Lean's output.** The run 9 report says "Bohr–Landau itself is NOT proved", a sentence of fixed generator prose inherited from runs 7 and 8, where it was true, although the same report lists the theorem with the standard axioms (see *Errata*). Where a report's prose and the statements Lean printed differ, the statements govern.

## The first six runs and the MNF.RH library

Runs 1 and 2 repeat the Comparator checks of the two external theorems; runs 3 to 6 judge the author's Lean library `MNF.RH` on the two verified trees. Nothing in this section proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

### Runs 1 and 2: the two replications

Run 1 (label `qrh-main`) checked one theorem of OpenAI's repository [@openai-math] at commit `adc7f124`, the Lean theorem that accompanies the manuscript [@openai-qrh]. Its challenge file states, in the namespace `OAI`:

```lean
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  sorry
```

The receipt gives the proof's size as 2,924 project files and 486,490 lines, third-party files apart, on Lean v4.34.1. The run was cold (nothing of the proof had been compiled on the machine before), started at 2026-10-27T17:43:45Z, took 1 h 54 min 37 s, and ended with exit code 0 and the verdict PASS. Only Lean's kernel replayed the proof.

Run 2 (label `zeta23-main`) checked the 17 statements of Anthropic's zeta23 [@anthropic-formal-math] at commit `16a5ce41`, which formalizes the theorem of Alpöge and Furman [@alpoge-furman]: eleven statements about $\zeta$ and six about Dirichlet $L$-functions, each a proportion in $\varepsilon$-form. For example, `two_thirds_simple_on_critical_line` says that for every $\varepsilon>0$ and all large $T$, at least $(2/3-\varepsilon)(N(2T)-N(T))$ zeros with $T<\gamma\le 2T$ are simple and on the critical line. The words "more than two thirds" are the title of [@alpoge-furman]: in the statements judged here the constants are $2/3-\varepsilon$ and $5/6-\varepsilon$ and, in the statements with `montgomery_taylor` in their names, symbolic constants whose decimal values (0.67250 and 0.83625) are, in the register's words, "docstrings, not statements". The proof is 316 files and 102,265 lines, on Lean v4.33.0-rc2. The run was cold, started at 2026-10-28T11:08:56Z, took 21 min 1.5 s, and ended with exit code 0 and the verdict PASS. Lean's kernel and NanoDa [@nanoda] replayed the proof.

What a PASS certifies is stated in *Comparator and what an acceptance means*: the pinned proof was accepted by the Lean kernel (and by NanoDa in run 2) against the pinned statement file, using only the axioms `propext`, `Quot.sound` and `Classical.choice`. Neither run is a first verification (see *The two artifacts under test and their trusted statement files*).

### The MNF.RH library in standard terms

The library `MNF.RH` consolidates the files on RH of the author's earlier Lean collection (the "corpus"). Its vocabulary is the author's, not standard terminology. In standard terms:

- the "shifted zero spectrum" `ShiftedZeroSpectrum` is the set $S$ of the real numbers $\beta-1/2$ (no operator is involved);
- the spectral gap hypothesis $G(\Delta)$ of the Introduction is `SpectralGapHyp Δ`, defined as `SpectralGapProperty ShiftedZeroSpectrum Δ`: every point of $S$ is $0$ or has absolute value at least $\Delta$;
- "nullification" at threshold $\Delta$, `nullify Δ`, sends a real number $x$ to $x$ if $\lvert x\rvert\ge\Delta$ and to $0$ otherwise; by `gap_iff_nullify_id`, $G(\Delta)$ says that this map fixes every point of $S$.

`RiemannHypothesis` is Mathlib's own proposition [@mathlib]. The record's register tags each statement: `[PROVED]`, kernel-checked from Mathlib alone; `[PROVED | 7/8]`, from Mathlib plus OpenAI's theorem, hence exactly as reliable as run 1; `[CONDITIONAL]`, proved from explicit named hypotheses; `[LITERATURE]`, a published theorem stated as a hypothesis, not formalized; `[OPEN]`; `[WITHDRAWN]`. The statements below are as Lean prints them in the report of run 5.

The gap hypothesis is equivalent to a zero-free strip (the equivalence is tagged `[PROVED]`; neither side is proved):

```lean
MNF.RH.spectralGapHyp_iff_zeroFree_strip {Δ : ℝ} :
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 / 2 + Δ → riemannZeta s ≠ 0
```

For every real $\Delta$, $G(\Delta)$ holds if and only if $\zeta$ has no zeros with $1/2<\operatorname{Re}s<1/2+\Delta$.

For $\Delta\ge 1/2$ the hypothesis is equivalent to RH, with no input beyond Mathlib (the equivalence is `[PROVED]`; the right-hand side is `SpectralGapHyp Δ` unfolded):

```lean
MNF.RH.riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1 / 2 ≤ Δ) :
  RiemannHypothesis ↔ MNF.RH.SpectralGapProperty MNF.RH.ShiftedZeroSpectrum Δ
```

and for $\Delta>3/8$ it is equivalent to RH given OpenAI's theorem (the equivalence is `[PROVED | 7/8]`):

```lean
MNF.RH.riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3 / 8 < Δ) : RiemannHypothesis ↔ MNF.RH.SpectralGapHyp Δ
```

The reason is that $\lvert\beta-1/2\rvert<1/2$ at every nontrivial zero, and $\lvert\beta-1/2\rvert\le 3/8$ given OpenAI's theorem. The argument does not reach $\Delta=3/8$: by `spectralGapHyp_three_eighths_iff` (`[PROVED | 7/8]`), $G(3/8)$ holds if and only if every nontrivial zero has $\beta\in\{1/2,1/8,7/8\}$, and OpenAI's theorem leaves the line $\operatorname{Re}s=7/8$ open. This does not show that $G(3/8)$ fails to imply RH; it shows only where the argument from the bound $\lvert\beta-1/2\rvert\le 3/8$ stops. The threshold $3/8$ is relative to that theorem: the register lists smaller boundaries, announced as parameter refinements of OpenAI's argument (about $0.874957$ by Liu [@liu-2026]), as read and not run here, and none is used in this work. RH implies $G(\Delta)$ for every $\Delta$ (`gap_of_rh`). For smaller $\Delta>0$, $G(\Delta)$ is a zero-free strip next to the critical line, in the register's words "not known for any Δ > 0".

The conditional density theorem (`[CONDITIONAL]`):

```lean
MNF.RH.on_line_density_one_of_gap (hBL : MNF.RH.BohrLandau) (hN : MNF.RH.NcountSuperlinear) {Δ : ℝ} (hΔ : 0 < Δ)
  (hgap : MNF.RH.SpectralGapHyp Δ) (ε : ℝ) : ε > 0 → ∃ T₀, ∀ T ≥ T₀, (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0 0 T)
```

`BohrLandau` says that for every $\delta>0$ some $C$ gives $N_{\mathrm{off}}(\delta,T)\le CT$ for all $T\ge 2$ [@bohr-landau-1914]; `NcountSuperlinear` says that $cT\le N(T)$ for every $c>0$ and all large $T$. In run 5 both propositions are `[LITERATURE]` hypotheses, never asserted; on the zeta23 tree they become theorems in runs 7 and 9 (see *The density layer: counting vocabulary and the Bohr–Landau theorem*). The conclusion, $(1-\varepsilon)N(T)\le N_0(T)$ for all large $T$, follows from RH and is not known to imply it. The register calls the implication "folklore, not new mathematics", and the hypothesis $G(\Delta)$ is open.

Most other statements are multiplicity lemmas (for instance $m(\rho)=1$ if and only if $\zeta'(\rho)\ne 0$, and $m(1-\rho)=m(\rho)$), bookkeeping for counting functions, and equivalences that rewrite hypotheses of the corpus. Each equivalence relocates RH, simplicity or the gap hypothesis; each side is as open as the other. The register's summary: "Not RH, not simplicity, and no new technique toward either"; and, in one line, "the nullification framework re-expresses RH; it does not reduce it."

### What is open and what was withdrawn

The register lists as open: $G(\Delta)$, for each $\Delta>0$; the simplicity of the zeros (`AllZerosSimple`); and two realization hypotheses of Hilbert–Pólya type, namely a symmetric operator, or a Schrödinger operator with a confining potential, having every $(\rho-1/2)/i$ as an eigenvalue. RH follows at once from either (`rh_of_symmetric_operator`, `rh_of_realization`, both `[CONDITIONAL]`); of the first the register says that the route "has no content short of constructing the operator". Speiser's theorem [@speiser-1934], that RH holds if and only if $\zeta'$ has no zeros with $0<\operatorname{Re}s<1/2$, is, per the register, not in Mathlib and is kept as a named `[LITERATURE]` hypothesis.

Five items of the corpus were withdrawn: (1) an axiom on double zeros, cited to Levinson and Montgomery [@levinson-montgomery-1974], which the citation does not support (with Speiser's theorem it would give that RH implies the simplicity of all zeros, which is not a known theorem) and which survives only as an explicit hypothesis of `allZerosSimple_of_speiser_and_double_zero_hyp`; (2) an axiom $\zeta'(1-s)=-F(s)\zeta'(s)$ throughout the strip, where $\zeta(1-s)=F(s)\zeta(s)$, which is false as stated (the product rule leaves a term $\zeta(s)F'(s)$) and is replaced by the proved `deriv_reflect` at zeros; (3) statements over placeholder functions fixed by `Classical.choice`, which "say nothing about ζ"; (4) two hypotheses, withdrawn as such because they are now theorems; (5) the description of $G(1/2)$ as "a physical input", since it is RH verbatim.

### Runs 3 to 6: the library judged

| Run | Label | Theorems | Definitions | Kernels | Start (UTC) | Wall clock (min:s) | Result |
|---|---|---|---|---|---|---|---|
| 3 | `mnf-library` | 40 | 17, as holes | Lean | 2026-10-28T00:20:02Z | 12:43.44 | `MNF_LIBRARY=ACCEPTED` |
| 4 | `mnf-library-v2` | 43 | 17, none a hole | Lean | 2026-10-28T03:25:44Z | 13:28.87 | `MNF_LIBRARY=ACCEPTED` |
| 5 | `mnf-library-v3` | 87 | 41, none a hole | Lean | 2026-10-29T05:56:47Z | 14:00.38 | `MNF_LIBRARY=ACCEPTED` |
| 6 | `zeta23-mnf` | 62 | 23, none a hole | Lean and NanoDa | 2026-10-29T02:06:38Z | 5:55.36 | `MNF_ZETA23=ACCEPTED` |

In each run Comparator [@comparator] judged the library against a challenge with the same statements and every proof replaced by `sorry`; all exit codes are 0, and every axiom report lists only the three standard axioms.

Run 3 listed its 17 definitions as holes, so their bodies were not compared (see *Comparator and what an acceptance means*). Run 4 added three theorems, among them the strip equivalence above, and listed no holes: it is the first run in which the library's definition bodies were compared. The definition counts are the `def` declarations of the challenge sources, as the report generator counts them. From run 4 on Comparator compares by name, type and body every definition that a claimed statement refers to; a counted definition that no claimed statement refers to (`MNF.RH.Counter` is one) was not compared, so each count is an upper bound for the bodies compared. Run 5 added five files (`Counting`, `Reduction`, `Schrodinger`, `GapDensity` and the Sturm–Liouville file below); eight of its 87 theorems are the `[PROVED | 7/8]` statements of `Unconditional.lean`, the only file that imports OpenAI's library.

Run 6 judged, on the zeta23 tree, the 36 statements of `Core`, `Gap` and `Hypotheses`, the 13 of `Counting`, and 13 in `Zeta23Restated.lean`, tagged `[RESTATEMENT | zeta23]`: eleven restate zeta23's statements about $\zeta$ over the library's counting functions and two rewrite them. In the report's words they "hold by definitional unfolding and are exactly as reliable as the zeta23 receipt", and "a proportion of zeros, however large, is not a statement about every zero". The `[PROVED | 7/8]` statements are absent, since that tree has another Lean and Mathlib pin and no OpenAI library.

The result word of these runs is ACCEPTED, not PASS; *Cold and warm runs* gives the reason and the recorded status of each run. The numbering is the record's: run 6 ended before run 5 began.

Outside the eleven runs, the record mentions two further acceptances for which it holds no receipt. The register says that the injection and ejection algebra of the author's "MNF2" package (in the layer, the file `MNF/Extension/InjectionEjection.lean`) was "also ACCEPTED at the OpenAI pin on 2026-11-03", and the README that the Sturm–Liouville file, as a standalone project with its own Comparator challenge, was "accepted again on 2026-11-03, Lean kernel and NanoDa". They are not results of this paper. Run 1's bundle also holds `BRIDGE.md`, the report of an ordinary sandboxed compile of two earlier files of the author on OpenAI's tree (in its words, "it is not a second Comparator run"); according to the register, `Unconditional.lean`, judged in runs 3 to 5, has the same content as the second of them, restated over the library's definitions.

### The Sturm–Liouville file and its co-authorship

Run 5 also judged `SturmLiouville/SimpleEigenvalues.lean` (581 lines; four definitions, four statements), which concerns one-dimensional Schrödinger operators, not $\zeta$. Its main statement (`[PROVED]`) is

```lean
sturm_liouville_simple_eigenvalues (V : ℝ → ℝ) (hV : IsConfiningPotential V) (eigval : ℝ) : IsSimpleEigenvalue V eigval
```

that is: if $V$ is continuous on $\mathbb{R}$ with $V(x)\to+\infty$ as $\lvert x\rvert\to\infty$, then for every real $\lambda$ any two eigenfunctions of $-u''+Vu=\lambda u$ in $L^2(\mathbb{R})$ are proportional. The result is classical (the limit-point case of Weyl's theory). The library uses it only in `Schrodinger.lean`: in a hypothetical Schrödinger realization every level is a simple eigenvalue, but by `multiplicityDictionary_iff` the link from simple eigenvalues to $m(\rho)=1$ is then equivalent to `AllZerosSimple`, so the theorem gives no shortcut to simplicity.

The record's `NOTICE` states that this file was "co-authored by Aristotle (Harmonic)" on 2026-03-03, consolidated by the author, and ported to the Mathlib pin of OpenAI's tree with "proof-internal changes only". This paper takes "Aristotle (Harmonic)" to be the system of [@aristotle]; the record does not say so. The authorship of the rest of the library is given in *Authorship and use of AI tools*.

## The density layer: counting vocabulary and the Bohr–Landau theorem

Runs 7 to 9 added a Lean layer to the zeta23 tree, the checkout of Anthropic's zeta23 library checked in run 2 [@anthropic-formal-math]. The layer fixes a vocabulary for counting zeros by their distance from the critical line and proves, on that tree, the theorem of Bohr and Landau [@bohr-landau-1914]. The theorem is classical; the contribution is its formalization and the receipted check. Nothing in this section proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

The modules were first judged in run 7 (2026-11-03 UTC, 124 theorems), run 8 (2026-11-03, 270) and run 9 (2026-11-04, 334). Each run was ACCEPTED by Comparator with the Lean kernel and NanoDa, and every axiom report lists only `propext`, `Quot.sound` and `Classical.choice`. The layer's Lean files were produced with Claude Code [@claude-code] under the author's direction, the two Bohr–Landau files by parallel agents from a written plan; the author set the goals, operated every run and is responsible for the claims. The restatements and the reflection step delegate to supporting files that the author supplied on 2026-11-03; the record does not say which tool drafted them (see *Authorship and use of AI tools*).

Theorem statements are quoted as Lean printed them in the run 11 bundle (those with a leading `@` from its `audit.out`), definitions from the sources of add-on v6.

### Counting functions and two notions of density

The counting functions are those of *Notation*: each runs over the zeros with $0<\gamma\le T$ and weights a zero by $m(\rho)$.

Two notions of density are kept apart (from `MNF/RH/Density.lean`, docstrings omitted):

```lean
def ReservoirDensityOne : Prop :=
  ∀ δ > 0, ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T

def OnLineDensityOne : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T
```

The first is density one within every fixed distance of the line, with $T_0$ depending on $\delta$ and $\varepsilon$. The word "reservoir" in its name is the author's word for zeros off the line (here, those closer to it than $\delta$), not standard terminology. The second is density one on the line itself. The second implies the first, since $N_{\mathrm{off}}(\delta,T)\le N(T)-N_0(T)$ for $\delta>0$ (`Ncount_eq_near_add_off`, `N0_le_NNear`). The first is not known to give the second: it places no constraint on zeros off the line whose distance from it tends to zero. On the word "reservoir" the sources are not uniform: in `Density.lean` the $\delta$-reservoir is the set of zeros with $0<\lvert\beta-1/2\rvert<\delta$, in `ReservoirMass.lean` the reservoir is the set of all zeros off the line, and in `Cube.lean` the reservoir at threshold $\Delta$ is the set with $\lvert\beta-1/2\rvert\ge\Delta$.

Two facts are inherited from the tree and restated by delegation; neither is a result of this work. The first, `MNF.RH.ncountSuperlinear`, says that $N(T)\ge cT$ for every $c>0$ and all large $T$. It is derived from the main term of the zeta23 library's Riemann–von Mangoldt formula `riemannVonMangoldt_zeta` (classically [@von-mangoldt-1905]). The second is Theorem B of zeta23, which formalizes the theorem of Alpöge and Furman that for every $\varepsilon>0$ and all large $T$ a proportion at least $2/3-\varepsilon$ of the zeros are simple and on the line [@alpoge-furman], read as an upper bound:

```lean
MNF.RH.offLine_le_one_third : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ↑(MNF.RH.NOffLine 0 T) ≤ (1 / 3 + ε) * ↑(MNF.RH.Ncount 0 T)
```

The left side is $N_{\neq}(T)$. The step from Theorem B is bookkeeping: $N(T)$ is the on-line count plus the off-line count, and the simple zeros on the line number at most the on-line count. So the tree already bounds the proportion of zeros off the line by $1/3+\varepsilon$; the Bohr–Landau theorem is far stronger at each fixed distance and silent on zeros that approach the line.

### The Bohr–Landau theorem as formalized

The statement is a definition of the library (`MNF/RH/GapDensity.lean`), a proposition that earlier runs carried only as a named hypothesis:

```lean
def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T
```

The theorem, as Lean prints it in the reports of runs 9 to 11:

```lean
Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau
```

In words: for every $\delta>0$ there is $C_\delta$ such that $N_{\mathrm{off}}(\delta,T)\le C_\delta T$ for all $T\ge2$. The count is two-sided and with multiplicity, and the constant is existential; run 10 added an explicit dependence on $\delta$ (`Zeta23.BL.bohrLandau_explicit`). The declarations in `Zeta23.BL` cited here belong to this layer, not to Anthropic's library. A similarly named declaration `Zeta23.BL.bohrLandau`, in a supporting file, rests on two `sorry` lemmas and is in no claim set. The report of run 9 still says that Bohr–Landau is not proved; see *Errata*.

The theorem goes back to Bohr and Landau, who proved that $N(\sigma,T)=O(T)$ for each fixed $\sigma>1/2$; it is customarily cited to their two notes of 1914 [@bohr-landau-1914; @bohr-landau-1914b], which were not consulted for this paper. The source files cite Section 9.15 of [@titchmarsh] for the classical proof. The record describes the formal result as "Bohr–Landau 1914, formalized; not new mathematics".

The author is not aware of a prior Lean statement of the Bohr–Landau theorem in its two-sided form, as a count of the zeros with $\lvert\beta-1/2\rvert\ge\delta$. The searches behind this sentence were incomplete, and, according to the registry, the content of the theorem was available in Lean earlier: a zero-density estimate registered by Lewko on the Palomar registry [@palomar] on 2026-10-11 [@lewko-density-3917], on a different toolchain pin and not on the zeta23 tree, bounds $N(\sigma,T)$ by a power of $T$ with exponent below 1 for each fixed $\sigma>1/2$. That implies the one-sided bound and, with the reflection of step 7, the two-sided one. Earlier still, Fiori registered explicit zero-density bounds for short windows $(t-h,t+h]$ (Palomar entry of 2026-09-23, formalizing [@fiori-2026]), proved by Jensen's formula and by Littlewood's lemma; according to the entry's abstract they include a two-sided corollary, that a positive proportion of the zeros in such a window have $\alpha\le\beta\le1-\alpha$. Those results are conditional on published explicit bounds and numerical certificates taken as hypotheses, were not re-checked here, and are not the Bohr–Landau theorem.

### Architecture of the formal proof

The proof has two halves: a mean square of $\zeta$ on vertical lines to the right of $1/2$, and a count of zeros by Jensen's formula on disks, which the plan chose over Littlewood's lemma on rectangles because the latter was in neither Mathlib nor the tree. From the tree the proof takes the Euler–Maclaurin representation `Zeta0EqZeta`, a port from the PrimeNumberTheoremAnd project [@pnt-plus], the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen` [@montgomery-vaughan-1974], the lower bound $\lvert\zeta(2+it)\rvert\ge1/3$ and, for step 7, the reflection symmetry of the zeros with multiplicity (`zetaZeroConfig.reflect_mem`, `zetaZeroConfig.mult_reflect`); from Mathlib [@mathlib] it takes Jensen's formula and a cosine series for Bernoulli polynomials. The bulk is in `Zeta23/BL/BohrLandauPartial.lean` (139 theorems, run 8) and `Zeta23/BL/BohrLandauClosure.lean` (64 theorems, run 9). Every lemma of the layer named below is in the claim set.

**Step 1. Euler–Maclaurin** (`zeta_eq_euler_maclaurin`, `tail_by_parts`). From `Zeta0EqZeta`, for $\operatorname{Re}s>0$, $s\ne1$ and every integer $N\ge1$,
$$\zeta(s)=\sum_{n\le N}n^{-s}+\frac{N^{1-s}}{s-1}-\frac{N^{-s}}{2}-s\int_N^\infty\psi(u)\,u^{-s-1}\,du,\qquad\psi(u)=\{u\}-\tfrac12 .$$
A second integration by parts replaces $\psi(u)\,u^{-s-1}$ by $(s+1)\psi_2(u)\,u^{-s-2}$, where $\psi_2=(B_2(\{u\})-\tfrac16)/2$ is the continuous periodic antiderivative of $\psi$ that vanishes at the integers.

**Step 2. Fourier series of the second Bernoulli function** (`B2per_fourier`, `P_fourier`). $B_2(\{u\})=\sum_{\nu\ge1}\cos(2\pi\nu u)/(\pi^2\nu^2)$, from Mathlib's series.

**Step 3. First-derivative test for smooth phases** (`first_derivative_test_amp_smooth'`). If $F'\ge\lambda>0$ on $[a,b]$ with $F''$ continuous, and $G\ge0$ is continuously differentiable with $G'F'-GF''\le0$, then $\lvert\int_a^bG(x)e^{iF(x)}\,dx\rvert\le4G(a)/\lambda$. With $F(u)=2\pi\nu u-t\log u$ and $G(u)=u^{-\sigma-2}$ it bounds the $\nu$-th Fourier mode of the tail over $(x,\infty)$ by $\frac{8}{\pi\nu}x^{-\sigma-2}$ when $t\le\pi x$ (`tail_mode_bound'`); this is where the condition $t\le N$ enters.

**Step 4. Sharp approximate formula** (`tail_sharp`, `zeta_approx_sharp`). Summing the modes: for every $\sigma_0>0$ there is $C$ such that, for $s=\sigma+it\ne1$ with $\sigma_0\le\sigma\le2$, $0\le t\le N$ and $N\ge1$,
$$\Bigl\lvert\zeta(s)-\sum_{n\le N}n^{-s}-\frac{N^{1-s}}{s-1}\Bigr\rvert\le C\,N^{-\sigma}.$$
The source describes this as the shape of Theorem 4.11 of [@titchmarsh] on a narrower range.

**Step 5. Mean square on vertical lines** (`M1.dirichlet_meanSquare_le`, `meanSquareUnif_all`). The Dirichlet-polynomial mean value in Montgomery–Vaughan form, $\int_0^T\lvert\sum_{n\le N}a_nn^{-it}\rvert^2dt\le T\sum_{n\le N}\lvert a_n\rvert^2+26\sum_{n\le N}(n+1)\lvert a_n\rvert^2$, follows from the tree's inequality. With $N=\lceil T\rceil$ and step 4 it gives

```lean
@BLClosure.meanSquareUnif_all : ∀ {σ₁ : ℝ},
  1 / 2 < σ₁ →
    ∃ C, ∀ (σ : ℝ), σ₁ ≤ σ → ∀ (T : ℝ), 2 ≤ T → ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2 ≤ C * T
```

This is the $O(T)$ upper bound in the classical mean-value theorem for $\lvert\zeta(\sigma+it)\rvert^2$ on the lines $\sigma>1/2$ (the source cites Section 7.2 of [@titchmarsh]); the asymptotic formula $\sim\zeta(2\sigma)\,T$ is not proved.

**Step 6. Jensen on disks centered at $2+it$, averaged in $t$** (`sum_divisor_mul_log_le`, `geom_facts`, `count_le_integral`, `rightHalf_of_meanSquareUnif`). Fix $1/2<\sigma_1<1$ and $\sigma_1-1/2<\delta\le1/2$. For $t\ge3$ the disk of radius $R=2-\sigma_1$ about $2+it$ lies in $\operatorname{Re}s\ge\sigma_1$ and misses the pole, and a zero with $\beta\ge1/2+\delta$ lies in a concentric disk of smaller radius $r$ for all $t$ within a fixed distance $h$ of $\gamma$. The disk inequality `sum_divisor_mul_log_le` (from Jensen's formula) at each $t$, integrated over $3\le t\le T+3$ for $T\ge4$, bounds $2h\log(R/r)\,\bigl(N(\tfrac12+\delta,T)-N(\tfrac12+\delta,4)\bigr)$ by $T\log3$ plus the integral of the circle averages of $L=\tfrac12\log(1+\lvert\zeta\rvert^2)\le\tfrac12\lvert\zeta\rvert^2$, which Fubini's theorem and step 5 bound by a multiple of $T$. Hence $N(\tfrac12+\delta,T)=O(T)$ for every $\delta>\sigma_1-1/2$. For $0<\delta<1/2$ the choice $\sigma_1=1/2+\delta/2$ applies, and for $\delta\ge1/2$ the count is zero, which gives the right-half bound for every $\delta>0$ (`Zeta23.BL.rightHalf_all`).

**Step 7. Reflection** (`MNF.RH.NOff_eq_right_add_left`, `NLeft_eq_NRight`, `bohrLandau_of_right`). The map $\rho\mapsto1-\bar\rho$ preserves ordinate and multiplicity and exchanges the two half-strips, so $N_{\mathrm{off}}(\delta,T)=2N(\tfrac12+\delta,T)$ for $\delta>0$, and a right-half bound with constant $C$ gives `BohrLandau` with constant $2C$.

### The intermediate result for distances above one sixth

Run 8 had the Dirichlet-polynomial mean value and steps 6 and 7, but only the tree's bound for the Euler–Maclaurin tail, and reached

```lean
Zeta23.BL.bohrLandau_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ C * T
```

The obstacle is the error term: the tree bounds the tail of step 1 by $(\sigma+t)N^{-\sigma_1}/\sigma_1$ on $\sigma\ge\sigma_1$, which grows linearly in $t$. Its square, integrated over $1\le t\le T$, is of order $T^3N^{-2\sigma_1}$, which is $O(T)$ only if $N$ is at least of order $T^{1/\sigma_1}$. The Montgomery–Vaughan term and the term $N^{1-s}/(s-1)$ are of order $N^{2-2\sigma_1}$, which is $O(T)$ only if $N$ is at most of order $T^{1/(2-2\sigma_1)}$. For $N=T^a$ the window $1/\sigma_1\le a\le1/(2-2\sigma_1)$ is nonempty exactly when $\sigma_1\ge2/3$. The proof takes $a=3/2$ and obtains the mean square for $2/3\le\sigma_1<1$ (`Zeta23.BL.M3.meanSquareUnif_explicit`); step 6 needs $\delta>\sigma_1-1/2$, hence $\delta>1/6$. The source calls this "a limitation of this route, not a theorem about ζ". Step 4 removes the factor $t$ from the error, after which $N=\lceil T\rceil$ serves every $\sigma_1>1/2$.

### Corollaries

```lean
MNF.RH.reservoirDensityOne_unconditional : MNF.RH.ReservoirDensityOne
@MNF.RH.onLineDensityOne_of_gap_only : ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
```

The first has no hypothesis and is the classical consequence of the Bohr–Landau theorem, formalized: within every fixed distance of the critical line the zeros have density one, by the bound $C_\delta T$ and the superlinear growth of $N(T)$.

The second is conditional on the gap hypothesis $G(\Delta)$, in Lean `SpectralGapHyp Δ` (see *The MNF.RH library in standard terms*). Under it the zeros within $\Delta$ of the line are exactly the zeros on it (`NNear_eq_N0_of_gap`), so the instance $\delta=\Delta$ of the first corollary is density one on the line; the hypothesis is used only there.

The hypothesis is not weakened: for $\Delta\ge1/2$ it is the Riemann hypothesis, and for $0<\Delta<1/2$ it is an unproved zero-free strip $1/2<\operatorname{Re}s<1/2+\Delta$. The conclusion follows from the Riemann hypothesis and is not known to imply it: it allows infinitely many zeros off the line provided they number $o(N(T))$. The implication itself is folklore, not new mathematics. Neither corollary is progress on the Riemann hypothesis or on the gap hypothesis.

## A zero-density estimate, the displacement bound and the pair measure

This section covers the modules first judged in run 10 (`Zeta23/Density/StripDensity.lean`, `MNF/RH/ReservoirMass.lean`) and in run 11 (`MNF/RH/Cube.lean`). As in the previous section, the Lean statements are copied from the run 11 bundle, which re-judges the whole layer, those with a leading `@` from its `audit.out`. The three files were written with Claude Code [@claude-code] by parallel agents from written plans, under the author's direction (see *Authorship and use of AI tools*); for the third, the idea of restating the gap hypothesis as the statement that distinct zeros near the line have distinct ordinates is the author's (in the words of `NOTICE`, "reading the strip through the simplicity of the projected zeros"). The analytic results formalize classical theorems with weaker exponents than the literature; the rest is bookkeeping over finite sums of zeros. None of it proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

### The zero-density estimate

```lean
@Zeta23.Density.density_single_window : ∀ {σ₁ δ : ℝ},
  1 / 2 < σ₁ →
    σ₁ - 1 / 2 < δ →
      δ ≤ 1 / 2 →
        ∃ C,
          ∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3
```

With $\sigma = 1/2 + \delta$: for $1/2 < \sigma_1 < \sigma \le 1$ there is $C = C(\sigma_1, \sigma)$ such that, for all $T \ge 2$,

$$N(\sigma, T) \le C\, T^{\,1 - (2\sigma_1 - 1)^2/(2\sigma_1)}\, (1 + \log T)^3 .$$

At $\sigma_1 = 3/4$ the exponent is $5/6$: for each fixed $\sigma > 3/4$, $N(\sigma, T) = O(T^{5/6} (\log T)^3)$. Since $\sigma_1 < \sigma$ is strict and $C$ depends on $\sigma_1$, every saving below $(2\sigma - 1)^2/(2\sigma)$ is obtained and that value is not. The statement counts zeros to the right of the line; the two-sided form over $N_{\mathrm{off}}$ is not a theorem of the layer. It is a count, not a zero-free region: it excludes no individual zero and says nothing about zeros closer than $\delta$ to the line.

The result is classical in kind and weak in strength. Carlson's theorem [@carlson-1920] gives $N(\sigma, T) \ll T^{4\sigma(1-\sigma)+\varepsilon}$, and $4\sigma(1-\sigma) = 1 - (2\sigma-1)^2$; the saving here is smaller than Carlson's by the factor $1/(2\sigma_1)$ (at $\sigma_1 = 3/4$: Carlson's exponent $3/4$, against $5/6$ here). Ingham's exponent $3(1-\sigma)/(2-\sigma)$ [@ingham-1940] is smaller still for $1/2 < \sigma < 1$. Among the later improvements is the estimate $N(\sigma, T) \le T^{30(1-\sigma)/13 + o(1)}$ of Guth and Maynard [@guth-maynard]; Tao, Trudgian and Yang [@tao-trudgian-yang] tabulate the known exponents and add new ones. See also [@titchmarsh]. Stronger estimates also exist in Lean. Lewko registered four zero-density formalizations on the Palomar registry between 2026-10-07 and 2026-10-21 [@lewko-density-34; @lewko-density-32; @lewko-density-3917; @lewko-density-improved]; the statement file of [@lewko-density-3917], which was read, has Ingham's exponent near the line and a smaller exponent than the one above throughout (that its proof was accepted is the registry's report, not re-checked here; its Comparator configuration lists as holes the three definitions on which the statements rest, and the challenge and solution files at the registered commit define them identically). Those statements are one-sided, on another toolchain pin, and not on the zeta23 tree. Run 10 is an independent formalization of Carlson's method on that tree, with a weaker exponent, judged by Comparator with a published receipt.

The proof keeps the Jensen-disk argument of the Bohr–Landau proof (disks centered at $2 + it$, averaged over $t$; see step 6 of *Architecture of the formal proof*) and changes what is averaged. Below, $s = \sigma + it$ and $\mu$ is the Möbius function.

1. Mollifier. Let $M_X(s) = \sum_{n \le X} \mu(n) n^{-s}$ and $f_X = \zeta M_X$. For $\operatorname{Re} s > 1$, $f_X(s) - 1 = -\zeta(s) \sum_{n > X} \mu(n) n^{-s}$, so $-\log\lvert f_X(2+it)\rvert \le \pi^2/(3X)$ for $X \ge 4$. Zeros of $\zeta$ are zeros of $f_X$ of at least the same order, so the same disk inequality for $f_X$ counts them, and the center term, of order $T$ in the Bohr–Landau proof, becomes $O(T/X)$.
2. Product polynomial. With $S_N(s) = \sum_{n \le N} n^{-s}$, $S_N M_X = \sum_{m \le NX} c_m m^{-s}$, where $c_1 = 1$, $c_m = 0$ for $1 < m \le X \le N$, and $\lvert c_m\rvert \le d_X(m)$, the number of divisors of $m$ not exceeding $X$.
3. Divisor bound. $\sum_{m \le Y} d_X(m)^2 \le Y (1 + \log X)^3$, by counting common multiples; this elementary bound is the origin of the factor $(1 + \log T)^3$.
4. Window mean square. On a segment $t \in [a, a + \ell]$ of a line $\operatorname{Re} s = \sigma \ge \sigma_1$, the mean square of $S_N M_X$ is bounded by the Montgomery–Vaughan inequality [@montgomery-vaughan-1974] (the weighted Hilbert inequality behind it is zeta23's), and that of $(\zeta - S_N) M_X$ by the sharp approximate formula of run 9, $\lvert \zeta(s) - S_N(s) - N^{1-s}/(s-1)\rvert \le C_G N^{-\sigma}$ for $\sigma_1 \le \sigma \le 2$ and $0 \le t \le N$. The two are joined by $\lvert u + v\rvert^2 \le (1+\eta)\lvert u\rvert^2 + (1 + 1/\eta)\lvert v\rvert^2$ with a free $\eta > 0$.
5. $\varepsilon$-majorant. $\log\lvert f_X\rvert \le \tfrac12 \log(\varepsilon^2 + \lvert f_X\rvert^2)$, and Jensen's inequality for the concave logarithm bounds the average of this majorant over a segment of length $T$ by $\tfrac12(\varepsilon^2 + E)$ when the integral of $\lvert f_X\rvert^2$ over the segment is at most $T(1 + E)$. The Bohr–Landau proof used the majorant $\tfrac12\log(1 + \lvert\zeta\rvert^2) \le \tfrac12\lvert\zeta\rvert^2$, whose constant $1$ removes every saving.
6. Exponent arithmetic. With $X = \lfloor T^{\theta} \rfloor$, $N = \lceil T \rceil + 5$, $\varepsilon^2 = 1/X$ and $\theta = (2\sigma_1 - 1)/(2\sigma_1)$, the count is at most a constant times $T^{1-\kappa}(1 + \log T)^3$, where $\kappa = (2\sigma_1 - 1)^2/(2\sigma_1)$.

One approximate formula of length $N \approx T$ serves the whole window, and this costs the exponent. In the account of the proof plan (`strip/STRIP_PLAN.md` in the notes), the diagonal, off-diagonal and center terms balance at $X = T^{2\sigma_1 - 1}$, giving Carlson's exponent, only when $N \approx t$ on each dyadic window. With a single $N$ the term $N^{1-s}/(s-1)$, multiplied by $M_X$, is large at small $t$; its cross term moves the balance to $X = T^{\theta}$ and the saving to $\kappa$. The dyadic version, and with it Carlson's exponent, was a stretch target of the plan and is not proved.

### The displacement of the zeros from the line

Recall from *Notation* the total displacement of the zeros from the critical line, $D(T) = \sum_{0 < \gamma \le T} m(\rho)\, \lvert \beta - 1/2\rvert$. In Lean it is `MNF.RH.reservoirMass T`, the author's "reservoir mass", with "reservoir" as glossed in *Counting functions and two notions of density*.

```lean
MNF.RH.reservoirMass_eq_integral : ∀ (T : ℝ), MNF.RH.reservoirMass T = ∫ (δ : ℝ) in 0..1 / 2, ↑(MNF.RH.NOff δ 0 T)
MNF.RH.reservoirMass_le_rpow : ∃ A T₀, ∀ (T : ℝ), T₀ ≤ T → MNF.RH.reservoirMass T ≤ A * T * Real.log T ^ (3 / 5)
MNF.RH.meanDisplacement_tendsto_zero : Filter.Tendsto (fun T => MNF.RH.reservoirMass T / ↑(MNF.RH.Ncount 0 T))
  Filter.atTop (nhds 0)
```

These are the layer-cake identity $D(T) = \int_0^{1/2} N_{\mathrm{off}}(\delta, T)\, d\delta$, the bound $D(T) \le A\, T (\log T)^{3/5}$ for $T \ge T_0$ (a real power), and $D(T)/N(T) \to 0$: the mean displacement, with multiplicity, tends to zero.

The input is the Bohr–Landau bound with its dependence on $\delta$ made explicit (`Zeta23.BL.bohrLandau_explicit`): there are $A_1, B_1 \ge 0$ with $N_{\mathrm{off}}(\delta, T) \le (A_1\delta^{-5/2} + B_1)\,T$ for $0 < \delta \le 1/2$ and $T \ge 2$. The exponent $-5/2$ is $\delta^{-1}$ from the mean-square constant times $\delta^{-3/2}$ from the disk geometry; the classical dependence on $\delta$ is of order $\delta^{-1}$ up to a logarithm (the zbMATH review of [@littlewood-1924] records $N(\sigma, T) = O\left(\frac{T}{\sigma - 1/2}\log\frac{1}{\sigma - 1/2}\right)$). The bounds $c\,T\log T \le N(T) \le C\,T\log T$ for large $T$ are derived from zeta23's Riemann–von Mangoldt statement. Splitting the integral at $\delta_0 = (\log T)^{-2/5}$, the head is at most $\delta_0 N(T) \ll T(\log T)^{3/5}$ and the tail at most $(\tfrac23 A_1 \delta_0^{-3/2} + B_1/2)\,T$; the lower bound for $N(T)$ then gives $D(T) \le A' (\log T)^{-2/5} N(T)$ with another constant $A'$ (`reservoirMass_le_Ncount_mul`). The constants are named in the source; the receipted statements assert existence only. The signed sum vanishes, $\sum_{0 < \gamma \le T} m(\rho)(\beta - 1/2) = 0$ for every $T$ (`signedReservoir_eq_zero`), because the reflection $\rho \mapsto 1 - \bar\rho$ in the critical line is a multiplicity-preserving bijection of the window that negates each term.

These bounds are far weaker than the classical ones. The gain over the trivial $D(T) \le \tfrac12 N(T)$ is only the factor $(\log T)^{-2/5}$; Littlewood [@littlewood-1924] obtained $O(T \log\log T)$ for this sum, and Selberg's estimate $N(\sigma, T) \ll T^{1 - (\sigma - 1/2)/4} \log T$, uniform for $1/2 \le \sigma \le 1$ [@selberg-1946], gives $O(T)$ on integration over $\sigma$. That the mean displacement tends to zero is a theorem, and already a consequence of Littlewood's bound; under RH it is trivial, since then $D(T) = 0$. It restricts no individual zero, is consistent with infinitely many zeros off the line, and is silent on the gap hypothesis. The author is not aware of a prior Lean formalization of a bound for $D(T)$; the searches behind that sentence were limited.

### The pair measure

For a real function $f$ of three real variables, the module defines

$$\Pi_T(f) = \sum_{\rho} \sum_{\rho'} m(\rho)\, m(\rho')\, f\bigl(\beta - \tfrac12,\ \beta' - \tfrac12,\ \gamma - \gamma'\bigr),$$

the sum over ordered pairs of nontrivial zeros with $0 < \gamma, \gamma' \le T$ (Lean: `pairSum T f`). The author calls the three coordinates "the cube"; in standard terms $\Pi_T$ is a finite weighted pair sum. Its marginals are rearrangements: $\Pi_T(1) = N(T)^2$; a function $g$ of the first coordinate alone gives $N(T) \sum_{\rho} m(\rho)\, g(\beta - \tfrac12)$, so the indicator of $\lvert a\rvert \ge \delta$ gives $N(T)\, N_{\mathrm{off}}(\delta, T)$ and $g(a) = \lvert a\rvert$ gives $N(T)\, D(T)$.

The atom at ordinate difference zero, $\Pi_T(\mathbf{1}[u = 0])$ with $u$ the third coordinate, equals $\sum_\rho m(\rho)^2 + P(T)$ (`coincidentMass_eq`), where $P(T)$ sums $m(\rho) m(\rho')$ over ordered pairs of distinct zeros with equal ordinates. The diagonal part lies between $N(T)$ and $N(T)^2$, and each zero off the line contributes $m(\rho)^2$ to $P(T)$ through its reflection $1 - \bar\rho$. With $N_{\neq}(T) = N(T) - N_0(T)$ the count of zeros off the line,

$$P(T) \le N_{\neq}(T)\, N(T) + N_0(T)\, N_{\neq}(T)$$

(`offDiagonalCoincidentMass_le`). With zeta23's Theorem B [@anthropic-formal-math] read as $N_{\neq}(T) \le (1/3 + \varepsilon) N(T)$ for large $T$, this gives $P(T) \le (5/9 + \varepsilon)\, N(T)^2$ for large $T$ (`offDiagonalCoincidentMass_le_five_ninths`); $\tfrac59 = \tfrac13 \cdot 1 + \tfrac23 \cdot \tfrac13$. Under RH, $N_{\neq}(T) = 0$ and the same inequality gives $P(T) = 0$; the constant $5/9$ is bookkeeping on top of Theorem B and says nothing about whether $P(T)$ vanishes.

The plan (`cube/CUBE_PLAN.md` in the notes) had the bound $P(T) \le N_{\neq}(T)\, N(T)$, hence the constant $1/3 + \varepsilon$, on the ground that a zero on the line has no distinct partner at its ordinate. The Claude Code agent assigned to that statement found it false as bookkeeping (`cube/NODE_REPORTS.md`): a double zero on the line sharing its ordinate with two simple zeros off the line, reflections of each other, gives $P = 10$ against $N_{\neq} N = 2 \cdot 4 = 8$. No such configuration is known for $\zeta$, but nothing proved on the tree excludes it (RH would). The statement was not admitted with a `sorry`; the bound above replaced it. None of this concerns pair correlation: the small-distance law of the zeros is the prediction of Montgomery's conjecture [@montgomery-1973], not a theorem.

### Degenerate zeros and two equivalences

In the author's vocabulary a nontrivial zero is degenerate if it is multiple or shares its ordinate with another nontrivial zero. A zero off the line is degenerate, its partner being $1 - \bar\rho$ (`degenerate_of_not_onLine`). The gap hypothesis $G(\Delta)$, in Lean `SpectralGapHyp Δ`, is in standard terms the zero-free strip $1/2 < \operatorname{Re} s < 1/2 + \Delta$ (see *The MNF.RH library in standard terms*); it is RH for $\Delta \ge 1/2$ and is unproved for every $\Delta > 0$.

```lean
MNF.RH.noDegenerate_iff : (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ¬MNF.RH.Degenerate ρ) ↔
  (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → MNF.RH.OnLine ρ) ∧ MNF.RH.AllZerosSimple
MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ MNF.RH.OrdinatesInjectiveOn (MNF.RH.bandZeros Δ)
MNF.RH.spectralGapHyp_iff_bandCoincidentMass : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (T : ℝ), MNF.RH.bandCoincidentMass Δ T = 0
```

Lean prints three statements; the second and the third are two forms of one equivalence. The first says that no nontrivial zero is degenerate if and only if every nontrivial zero is on the line (`OnLine ρ` is $\beta = 1/2$) and simple. The second says that the gap hypothesis at $\Delta$ holds if and only if no two distinct nontrivial zeros with $\lvert\beta - 1/2\rvert < \Delta$ share an ordinate; the third restates this through the pair sum, as the vanishing for every $T$ of $P(T)$ restricted to such zeros. The proofs use the reflection symmetry of the zeros, taken from the zeta23 library (`zetaZeroConfig.reflect_mem`), and elementary logic; the third also needs complex conjugation, for the zeros with negative ordinates, and the fact that no nontrivial zero is real, because the windows see positive ordinates only. These equivalences relocate RH with simplicity, and the gap hypothesis, to statements about coincident ordinates. Each side is as open as the other, and neither is proved.

### No real zeros in the interval (0,1)

```lean
@MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo : ∀ {σ : ℝ}, 0 < σ → σ < 1 → riemannZeta ↑σ ≠ 0
```

For real $0 < \sigma < 1$, $\zeta(\sigma) \ne 0$; hence every nontrivial zero has a nonzero ordinate (`nontrivial_zero_im_ne_zero`). The proof takes one term of Euler–Maclaurin, the tree's `Zeta0EqZeta` at $N = 1$ (a port from PrimeNumberTheoremAnd [@pnt-plus]):

$$\zeta(\sigma) = \frac{\sigma}{\sigma - 1} - \frac12 + \sigma J(\sigma), \qquad J(\sigma) = \int_1^\infty \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{\sigma + 1}}\, dx, \qquad \lvert J(\sigma)\rvert \le \frac{1}{2\sigma}.$$

A zero would require $\sigma J(\sigma) = 1/(1-\sigma) - 1/2 > 1/2$, against $\lvert \sigma J(\sigma)\rvert \le 1/2$.

The fact is classical and elementary; the source records only that it was absent from the tree and not found in Mathlib at the pinned commit. It is not new in Lean: AxiomMath's ZetaZerosV2 [@axiom-zetazeros] proved it by the same route in a file committed 2026-10-03, and goldbach-lean [@hubbard-goldbach-lean] has it as well (both files were read for this paper; neither was built or re-checked here). It concerns the real segment only, not the interior of the strip, and bears on neither RH nor the gap hypothesis.

## A numerical illustration, limitations and errata

### A numerical illustration

The first 400 ordinates ($\gamma_1 = 14.134725$ to $\gamma_{400} = 679.742198$) were recomputed in double-precision Python (scripts written with Claude Code [@claude-code] under the author's direction; no interval arithmetic) from sign changes of Hardy's function, by the Riemann–Siegel formula and then Euler–Maclaurin summation. The scan found 414 zeros below height 700, against 414.557 from the smooth term of the Riemann–von Mangoldt formula; eleven ordinates agree, to within $3.3\times 10^{-10}$, with tabulated values (the public tables of Odlyzko and the LMFDB); the comparison values are constants in the script, which was written with Claude Code and marks them "as recalled", and they were not read from the tables for this work.

The normalized spacings $s_n = (\gamma_{n+1}-\gamma_n)\log(\gamma_n/2\pi)/(2\pi)$, $1\le n\le 399$, have mean 0.99744, standard deviation 0.3709 (Wigner surmise, the approximation $(32/\pi^2)\,s^2e^{-4s^2/\pi}$ to the GUE spacing density: 0.4220) and minimum 0.2434.

| $x$ | spacings with $s_n < x$ | expected, exact GUE law | expected, Poisson (spacing density $e^{-s}$) |
|---|---|---|---|
| 0.2 | 0 | 3.4 | 72.3 |
| 0.3 | 4 | 11.0 | 103.4 |
| 0.5 | 29 | 45.1 | 157.0 |
| 1 | 224 | 213.0 | 252.2 |

The Kolmogorov–Smirnov distance of the spacings is 0.0508 from the exact GUE spacing law ($p \approx 0.247$) and 0.3285 from Poisson ($p \approx 2.7\times 10^{-38}$). Log-log slopes fitted on $0.25\le x\le 0.75$ are 4.52 (bootstrap 16–84% band $[4.07, 5.05]$) for the fraction of the total spacing length lying in spacings below $x$ and 3.71 ($[3.26, 4.23]$) for their number, against 3.62 and 2.67 for GUE and 1.71 and 0.79 for Poisson. The fitted slopes exceed the GUE values on this window; the notes rate this "a ~2-2.5 sigma effect on 400 zeros", in the direction expected for low zeros, and it is not presented here as a finding. Ordered pairs of distinct zeros at normalized distance at most 0.5 number 0.145 per zero (GUE 0.2263, Poisson 1).

![Figure 1 (exploratory; proves nothing). Normalized spacings of the first 400 zeros. Panel A: fraction of the total spacing length in spacings below a threshold $x$, against GUE and Poisson; panel B: histogram of the spacings. Panel A uses the exact GUE spacing law and panel B the Wigner surmise, which is why the expected number of spacings below 0.2 reads 3.4 in one and 3.3 in the other. The ordinates are uncertified; "re-located" means found again by a second formula, without error bounds. The threshold $x$ acts on spacings of ordinates: it is unrelated to the threshold $\Delta$ of the gap hypothesis, which concerns real parts, and to any zero-free strip. The image is `numeric/cascade.svg` of the record's notes with its text labels edited for this paper; the plotted data are unchanged.](figures/cascade-relabeled.svg)

![Figure 2 (exploratory; proves nothing). The pair measure of the first 400 zeros (the author's "cube"); in the image delta1 and delta2 are the values of $\beta - 1/2$ for the two zeros of a pair. Panel A is a schematic: the data lie on one axis and the shaded zones contain no data. The zone labels give the status of statements about all zeros and are not results of this computation: the zone $\lvert\beta - 1/2\rvert > 3/8$ contains no zeros by OpenAI's theorem and the reflection symmetry; the bound $O(T^{1-c})$ for the zeros with $\lvert\beta - 1/2\rvert \ge \Delta$ is Carlson's classical theorem, of which run 10 formalizes a weaker form for the right half; that the band $0 < \lvert\beta - 1/2\rvert < \Delta$ is empty is the gap hypothesis, which is unproved. The ticks marked D stand for $\pm\Delta$. That all 400 zeros are simple and on the line rests on the uncertified computation described above. Panel B: pairs per zero within normalized distance $x$, against GUE, Poisson and a cubic reference; the cubic law is a GUE prediction, not a theorem. The image is `numeric/cube.svg` of the record's notes with its text labels edited for this paper; the plotted data are unchanged.](figures/cube-relabeled.svg)

These computations are exploratory and prove nothing. They concern spacings of ordinates on the critical line, not real parts, and bear on none of RH, the simplicity of the zeros, or a zero-free strip. GUE statistics for the zeros are conjectural [@montgomery-1973], and the repulsion seen is known behavior [@odlyzko-1987]. With no spacing below 0.243, the small-$x$ exponents of the GUE law (4 and 3) are not observable; the slopes are finite-window values. The bands and $p$-values treat the spacings as independent and are indicative only. The ordinates are uncertified, and the completeness of the list rests on the count above, not on a Turing-style argument. That the zeros at these heights are on the critical line is known from rigorous computation [@platt-trudgian-2021].

### Limitations

*Mathematics.* Nothing here proves, or is evidence for, RH, the simplicity of the zeros, or a zero-free strip next to the critical line. The gap hypothesis stays open for every $\Delta>0$; the equivalences of the MNF library and of the pair-measure module only relocate it, or RH with simplicity. The Bohr–Landau theorem, the zero-density estimate and the displacement bound are counts and averages: they exclude no individual zero and are compatible with infinitely many zeros off the line. They are also weak: the density exponent $1-(2\sigma_1-1)^2/(2\sigma_1)$, receipted for the right half only, falls short of Carlson's $4\sigma_1(1-\sigma_1)=1-(2\sigma_1-1)^2$ [@carlson-1920] and of Lean estimates registered earlier [@lewko-density-3917]; the displacement bound $O(T(\log T)^{3/5})$ falls short of the classical $O(T\log\log T)$ [@littlewood-1924] and $O(T)$ [@selberg-1946]; and the receipted statements of all three are existential in their constants.

*Checks.* Each tree is pinned (Lean v4.34.1 with Mathlib `d13f23b7`; Lean v4.33.0-rc2 with Mathlib `51e6992e`); the results are statements about those versions. One operator made all eleven runs on one laptop in a single boot (*Authorship and use of AI tools* says what the record tells about the operation), and a receipt is a record, not a cryptographic proof. Every acceptance depends on everything listed in *The trust base*, and no tool checks that a Lean statement matches its English reading. Runs 3 to 11 reuse the compiled trees of runs 1 and 2, and runs 7 to 11 also the modules of this work compiled by the runs before them; they are reported as ACCEPTED, and under the kit's protocol, which reserves PASS for cold runs, they are warm runs, for which the kit closes none of the exposures it lists. Most of the receipted runs repeated an acceptance already obtained on the author's own account, and the challenges of runs 3 to 11 are generated from the solutions' own sources (see *Cold and warm runs* and *Challenges as module-for-module mirrors*). The 21 controls were run with one of the two checkers only, and run 2 was launched by an add-on version other than the deposited one (see *Receipts and the verifier*). All eleven runs used the standalone Comparator after its repository had been archived; its README says that only the Lake commands are guaranteed to receive further security and performance improvements.

### Errata

*The run 9 report.* Its block "How to read this", fixed prose of the report generator, says "Bohr–Landau itself is NOT proved", which was true for runs 7 and 8. For run 9 it is false: the same report prints `Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau` and lists it with the three standard axioms. Verdict, audit and hashes are unaffected. The generator was corrected in add-on v5, the reports of runs 10 and 11 carry the corrected prose, the register and the README record the erratum, and the bundle was not altered.

*A bound corrected before it was claimed.* The plan of the pair-measure module had the bound $P(T)\le N_{\neq}(T)\,N(T)$, hence an eventual constant $1/3+\varepsilon$. It is false as bookkeeping; *The pair measure* gives the counterexample. The error was found during the formalization, and the false statement is in no Lean declaration or receipt. Run 11 judged the corrected bound $P(T)\le N_{\neq}(T)\,(N(T)+N_0(T))$ (`MNF.RH.offDiagonalCoincidentMass_le`), with the eventual constants $2/3+\varepsilon$ and $5/9+\varepsilon$.

*Found while preparing this paper.* The "What was proved" block of the run 11 report prints only 255 of the 534 judged statements: its generator drops those that Lean prints with a leading `@`, `Zeta23.Density.density_single_window` among them; all 534 are in the axiom table and in `audit.out`. The reports of runs 4 to 11 say that the definitions of the challenge were "all compared by name, type and body"; the number they give counts `def` lines, and Comparator compares those that a claimed statement refers to (see *Runs 3 to 6: the library judged* and Appendix A). The notes give the standard deviation of the normalized spacing for GUE as 0.4221 (`numeric/RESULTS.md`); that value is a constant typed into `mnf_analysis.py` as "exact GUE sd", the Wigner surmise gives 0.4220, and a recomputation of the exact law made while this paper was reviewed gave 0.4243 (`numeric/gue_sd.py` in the notes).

*A provisional priority claim in the notes.* The working notes of run 10 (`strip/STRIP_PLAN.md`, `strip/STRIP_SCOPE_REPORTS_2026-11-04.md`) call its target "the first kernel-checked zero-density estimate with a power saving", subject to reading Lewko's Palomar entries. The registry entries have since been read, and the statement file of one of them (see *The zero-density estimate*); the description does not hold, and this paper makes no such claim.

*Corrected in the record while this paper was prepared.* Up to commit `f03aaa9`, which added run 11, the register and the README carried statements that this paper does not repeat. They were corrected at the commit cited in *Availability*, and the register lists them (its section 10, errata of 2026-11-11); the reports inside the bundles are unchanged. The reports of runs 3 to 5 say that `gap_below_bound_insufficient` "says a gap at Δ ≤ 3/8 cannot give it" (RH), and the register called the gap hypothesis "insufficient for every Δ ≤ 3/8" and the threshold "exact". The Lean statement concerns an abstract symmetric set of real numbers, not the zeros of $\zeta$; whether $G(\Delta)$ implies RH for such $\Delta$ is not decided by it (if RH holds, the implication holds trivially), and *The MNF.RH library in standard terms* says only where the argument stops. The README said that both authors report Comparator runs of their own; for OpenAI the files read show a configuration and an instruction, not a reported run. The register called runs 7 to 11 cold and said that every definition was compared by body; the receipts record warm runs, and the definition counts are upper bounds. The README and the register attributed the mean-square bound to Hardy and Littlewood; that attribution was not checked and is not made here. The README called the real-zero theorem a "new unconditional fact", meaning new to the tree; the fact is classical and has earlier Lean proofs (see *No real zeros in the interval (0,1)*).

### What would strengthen the work

The plan's route to Carlson's exponent, approximate formulas of length $N\approx t$ on dyadic windows, was a stretch target and was not carried out. Porting the layer to current Lean and Mathlib and re-judging it with the `lake comparator` that ships with Lean 4.35.0 [@lean-4-35] would end the dependence on two frozen pins and on the standalone Comparator, whose repository is now archived [@comparator]. A certified computation of the first 400 ordinates (interval arithmetic with a Turing-type completeness check, or a Lean-checked verification), which the record lacks, would replace the uncertified list of zeros behind the illustration and make its finite counts rigorous; the comparison with GUE would remain statistical, and nothing would follow beyond that height. Numerically, RH is verified up to height $3\cdot 10^{12}$ [@platt-trudgian-2021]. The controls could be repeated with the second checker, Mathlib compiled from source inside the sandbox, and the runs repeated by another operator on another machine. A cold run of the complete layer, on a fresh checkout in which Comparator compiles the zeta23 library and the layer together, would remove the warm status of runs 6 to 11; the same holds for the library on OpenAI's tree, at the cost of compiling OpenAI's proof again (1 h 54 min 37 s in run 1).

## Reproducing and verifying the record

### Verifying the record offline

In a copy of the record:

```
sha256sum -c CHECKSUMS.sha256
./verify_deposit.sh
```

The first command checks the sha256 of the 27 listed files: the 21 tarballs and six other top-level files. `README.md`, `sources/` and `notes/` are not listed.

The second needs `sha256sum`, `tar` and `python3` and runs neither Lean nor Comparator. It repeats the first check; checks in the bundles the verdict PASS, the run type cold and the pinned commit of runs 1 and 2, and the result line ACCEPTED of runs 3 to 11; checks that the Lean sources hashed by the receipts of runs 3 to 5 and 7 to 11 are byte-identical to those in the matching add-on tarball (not for run 6), and each add-on against its own manifest; and, with network access, compares the two upstream statement files at the pinned commits with the pins. Run at the commit cited in *Availability*, it ended in `VERIFY=OK`; the counts given here (27 listed files, 21 tarballs) are those of that commit.

The first establishes that the files are those the record cites; the second, that the bundles carry the verdicts reported here (for runs 2 and 7 to 11 also the theorem counts) and that the Lean sources hashed by the receipts of runs 3 to 5 and 7 to 11 are the published ones. Neither shows that a run took place as recorded; for that, in the protocol's words, "Anyone with the same kit can repeat the run."

### Repeating a run

The kit needs a Linux machine with Landlock and a systemd user session; its notes for a local run ask for at least 30 GB of memory and 100 GB of free disk. A setup script run as root creates the unprivileged account `qrh` and installs the kit read-only; every later phase runs as that account. On the laptop used here (8 CPUs, 37 GB of memory) the Comparator job took 1 h 54 min 37 s in run 1, 21 minutes in run 2 and at most 16 minutes in each of runs 3 to 11.

Each add-on is a tarball with a manifest, a README and an instruction file for Claude Code; the commands can also be typed by hand. A run on a verified tree takes three scripts. The first checks the add-on against its manifest, requires the PASS of the run whose tree it uses, puts the Lean files and the challenge in place and starts Comparator in a detached unit; the second reports the state of the job; the third writes the report and the bundle and ends in `ACCEPTED`, `REJECTED` or `INCOMPLETE`. The instructions state: "A REJECTED result is a real result."

A repeat depends on the servers that hold the pinned commits and Mathlib's prebuilt cache; the standalone Comparator repository is archived [@comparator], and its two pinned tags still resolved when this paper was prepared.

### Availability

The record is the public repository https://github.com/Joeyxyxyz/qrh-comparator-receipts; everything said here refers to commit `9a6a1d9760847fb63e071c73b5f6c9c85f766653`, which corrects documents of the record as listed in *Errata*; this paper, its source and its review record were added to the repository in the commit after it. It holds the 21 tarballs (the kit, nine add-ons, eleven receipt bundles), the checksum file, the verifier, the register, unpacked copies of the kit and the add-ons under `sources/`, and the working notes of runs 7 to 11 under `notes/`. The 23 Lean files of the complete layer are in `sources/qrh-zeta23-addon-v6/`. This paper is deposited on Zenodo. The register and `NOTICE` speak of a "Zenodo record of 2026-10-29", a deposit of runs 1 to 6 prepared at that date; no file of the record gives a DOI for it, and this paper does not rely on it. The repository's `zenodo-metadata.json` describes the deposit of this paper with a snapshot of the record. The two artifacts under test are not redistributed; the scripts fetch them at the pinned commits [@openai-math; @anthropic-formal-math].

### Licenses

The files authored for the record (the kit and add-on scripts and documents, the author's Lean files, the receipts) are under the Apache License 2.0, as `LICENSE` states. `NOTICE` names the third-party tools that the scripts download, which keep their own licenses, and the two quotations in the receipts: OpenAI's nine-line challenge file and Anthropic's `Challenge.lean`, both Apache-2.0. The text of this paper is under CC BY 4.0.

## Authorship and use of AI tools

The author, Joey Messina, conceived the MNF framework, set the goals, operated every run and is responsible for every claim.

One qualification of "operated": the kit and every add-on ship an instruction file written for a Claude Code session that, as the unprivileged user, starts the scripts, waits, runs the report script and reports the result. The README files of the kit and of the first three add-ons describe the run through such a session; those of the six later add-ons give the commands to type and offer the session as an alternative. The record attributes the operation of every run to the author. For runs 7 to 11 the working log says how each was started: for runs 7 to 10 a Claude Code session working with the author typed one command line into a terminal (copy the add-on to the unprivileged account, open a shell as that account, run the three scripts), and the author authorized it by entering his password; run 11 he started himself from a terminal window with the same command line. For runs 1 to 6 the record does not say whether the commands were typed by him or issued by such a session at his request.

The kit and add-on scripts, the documents of the record, the Lean files of runs 7 to 11 except four supporting files supplied by the author, and the text of this paper were produced with Claude Code [@claude-code], Anthropic's coding agent, under the author's direction. According to `NOTICE`, the larger files of runs 8 to 11 were written by parallel agents from written plans, merged, and corrected after adversarial reviews of the prose; the idea behind `Cube.lean` is recorded as the author's. `NOTICE` and the working log name no human reviewer: the log calls one of these reviewers a "workflow agent", and `NOTICE` speaks of "independent model reviewers" for the earlier files. The text of this paper was likewise reviewed by model reviewers before the deposit. The files of the record name no model version. The commit messages of the repository do: the four commits up to run 10 carry the trailer "Co-Authored-By: Claude Fable 5.1", and the commit of run 11 and the commits made while this paper was prepared "Co-Authored-By: Claude Fable 5.2". A trailer is attached to a commit, not to a file, and the record does not say which model wrote which Lean file.

`NOTICE` adds three qualifications. It attributes six files of `MNF.RH` (`Core`, `Gap`, `Hypotheses`, `Unconditional`, `Reduction` and `Schrodinger`) to the author's earlier corpus, consolidated on 2026-10-27/28, and says that the additions of 2026-10-28/29 were written with Claude Code: the files `Counting`, `Zeta23Restated` and `GapDensity`; the three gap theorems added in run 4 (`spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of` and `spectralGapHyp_three_eighths_iff`, which sit in `Hypotheses` and `Unconditional`); the proposition forms of `GapMechanism` and `SchrodingerRealization`; and the port of the Sturm–Liouville file. Four supporting files of the layer (`Zeta23/Superlinear.lean`, `OffLine.lean`, `BohrLandau.lean`, `MNFBridge.lean`) were supplied by the author. For the rest of the six corpus files, their consolidation of 2026-10-27/28 included, and for these four supporting files, the record does not say which tool, if any, drafted them. The Sturm–Liouville file of run 5 was co-authored by Aristotle (Harmonic); see *The Sturm–Liouville file and its co-authorship*. A problem file for Aristotle prepared on 2026-11-03 for the last step of the Bohr–Landau proof (notes, `aristotle/`) was, according to the plan document of run 9, superseded by the agents' proof of the same chain; it has no part in the layer. The corpus itself is not part of the record and was not examined for this paper; the register's inventory counts 241 documents and assigns the files outside the RH line to "Zenodo Vol 1 (operator core) and Vol 3 (physical applications)". That inventory lists "the aristotle stubs 1–3" and an "aristotle_stress_test_synthesis" within the RH line and `_aristotle` variants outside it, and the header of the Sturm–Liouville file calls its three corpus variants "all Aristotle". These names suggest that Aristotle's part in the corpus is not limited to that one file; the record does not say which statements of the six consolidated files, if any, descend from such outputs.

One of the two artifacts re-checked, zeta23, is Anthropic's, and according to its README its Lean code was written by Claude; the scripts that repeated its check, and this text, were produced with Claude Code, a product of the same company. In run 2's receipt "independent" can mean no more than another machine, another operator and another launcher. The acceptance itself is the output of Comparator [@comparator], of Lean's kernel [@lean4] and of NanoDa [@nanoda], not of a language model.

The correctness of the Lean proofs does not rest on who or what wrote them: every claimed theorem of runs 3 to 11 was accepted by Comparator and the Lean kernel, and in runs 6 to 11 by NanoDa, against a statement printed in its bundle. No tool checks that a Lean statement matches its English reading, or that the prose is right; where they differ, the Lean statements and the receipts govern.

## Acknowledgments

The theorem that $\zeta$ has no zeros with real part above $7/8$, and its Lean proof, are OpenAI's [@openai-math]. The theorem that more than two thirds of the zeros are simple and on the critical line belongs to Alpöge and Furman [@alpoge-furman] and to Anthropic, whose zeta23 formalizes it [@anthropic-formal-math]; a script of that project informed the structure of the kit's verification scripts. Comparator and lean4export are the Lean FRO's [@comparator; @lean4export]. Every file judged here builds on Mathlib [@mathlib], the work of its community. Aristotle (Harmonic) [@aristotle] co-authored the Sturm–Liouville file. The Euler–Maclaurin representation used here comes from the PrimeNumberTheoremAnd project [@pnt-plus] through zeta23; NanoDa [@nanoda] and landrun [@landrun] are the work of their authors. Naming them implies no endorsement.

## Appendix A. The eleven runs

Times are UTC, from the files `logs/<label>.start` and `logs/<label>.end` of each bundle; every exit code is 0. "Thm" is the number of theorem names in the Comparator configuration, "Def" the number of definitions in the challenge. The last two columns give the first eight hexadecimal digits of the sha256 of the add-on tarball (for run 1, of the kit) and of the receipt tarball; `CHECKSUMS.sha256` has them in full.

| Run | Label | What was judged | Thm | Def | Kernels | Date, start to end (UTC) | Verdict | Add-on | Receipt |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `qrh-main` | OpenAI's `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, openai/math at `adc7f124` | 1 | no count given | Lean | 2026-10-27, 17:43:45 to 19:38:23 | PASS | `e0745073` | `d8670539` |
| 2 | `zeta23-main` | Anthropic's zeta23, 17 statements, anthropics/formal-math at `16a5ce41` | 17 | not counted; no holes | Lean, NanoDa | 2026-10-28, 11:08:56 to 11:29:58 | PASS | `958abb9f` | `e0b9a4d9` |
| 3 | `mnf-library` | `MNF.RH` v1 on a copy of run 1's tree | 40 | 17, as holes | Lean | 2026-10-28, 00:20:02 to 00:32:46 | ACCEPTED | `295ee9c6` | `f9180842` |
| 4 | `mnf-library-v2` | `MNF.RH` v2 on a copy of run 1's tree | 43 | 17 | Lean | 2026-10-28, 03:25:44 to 03:39:13 | ACCEPTED | `933c5ba8` | `c6142a40` |
| 5 | `mnf-library-v3` | `MNF.RH` v3, with the Sturm–Liouville file, on a copy of run 1's tree | 87 | 41 | Lean | 2026-10-29, 05:56:47 to 06:10:47 | ACCEPTED | `3668e138` | `023d7ada` |
| 6 | `zeta23-mnf` | `MNF.RH` and the restatement of zeta23's Theorems A to D, in run 2's checkout | 62 | 23 | Lean, NanoDa | 2026-10-29, 02:06:38 to 02:12:34 | ACCEPTED | `958abb9f` | `1476f568` |
| 7 | `zeta23-density` | the layer, add-on v2: counting vocabulary, restatements of zeta23, the author's operator bookkeeping, first lemmas toward Bohr–Landau | 124 | 66 | Lean, NanoDa | 2026-11-03, 21:05:57 to 21:13:50 | ACCEPTED | `5dc41dff` | `975b2178` |
| 8 | `zeta23-density-v3` | add-on v3: adds Bohr–Landau for $\delta > 1/6$ | 270 | 76 | Lean, NanoDa | 2026-11-03, 22:03:08 to 22:09:37 | ACCEPTED | `c0958d53` | `0588555d` |
| 9 | `zeta23-density-v4` | add-on v4: adds Bohr–Landau for every $\delta > 0$ | 334 | 81 | Lean, NanoDa | 2026-11-04, 00:52:20 to 00:58:43 | ACCEPTED | `fb74e8a2` | `0d1919e4` |
| 10 | `zeta23-density-v5` | add-on v5: adds the displacement sum and the zero-density estimate | 480 | 98 | Lean, NanoDa | 2026-11-04, 14:38:23 to 14:45:29 | ACCEPTED | `2d2cf058` | `37a806b2` |
| 11 | `zeta23-density-v6` | add-on v6: adds the pair-measure module and the absence of real zeros in $(0,1)$ | 534 | 110 | Lean, NanoDa | 2026-11-11, 00:02:37 to 00:17:52 | ACCEPTED | `99575a1e` | `ca07a500` |

Runs 1 and 2 are cold. Runs 6 to 11 are recorded as warm, cold only for the modules each add-on introduces; the bundles of runs 3 to 5 record no run type. The numbering is the record's: by start time the order is 1, 3, 4, 2, 6, 5, 7, 8, 9, 10, 11. Runs 2 and 4 to 11 list no definition hole, so every definition that a claimed statement refers to is compared by name, type and body; "Def" counts the `def` declarations in the challenge sources and is an upper bound for the bodies compared (in run 11, for instance, `Zeta23.BL.CG`, `Zeta23.BL.meanSquareB` and `Zeta23.BL.A₀` are counted and no claimed statement refers to them); the receipts of runs 1 and 2 give no count. Each of runs 8 to 11 re-judges the layer of the previous run together with the new modules. Runs 2 and 6 share one deposited add-on tarball; run 2's receipt records another manifest hash, so a different version, by the evidence given in *Receipts and the verifier* an earlier one, launched run 2. The verifier does not compare the sources hashed in run 6 with that tarball; compared by hand for this paper, the five Lean sources are byte-identical.

## Appendix B. Principal Lean theorems

Names are as in the receipts. Modules under `Zeta23/BL/` and `Zeta23/Density/`, and the names in `Zeta23.BL`, `Zeta23.Density`, `BLClosure`, `M1` and `DPMV` listed below, belong to the layer of this work and not to Anthropic's library, in whose tree they are compiled. The readings use the symbols of *Notation*, among them $G(\Delta)$, $D(T)$, $N_{\neq}(T)$ and $P(T)$. Constants such as $C$, $A$, $B$ and $T_0$ are asserted to exist, not given. The tags are the register's: [PROVED], from Mathlib alone; [PROVED \| 7/8], from Mathlib and OpenAI's theorem; [PROVED \| this tree], on the zeta23 checkout, from Mathlib, the zeta23 library and sorry-free declarations of the layer (the supporting file `Zeta23/BohrLandau.lean` also holds two `sorry` lemmas, on which no claimed theorem depends: every axiom report lists only the three standard axioms); [CONDITIONAL], from explicit named hypotheses; [RESTATEMENT \| zeta23], a theorem of zeta23 under the library's names, or (the two rows of run 7) a short consequence of one, derived in the supporting files `Zeta23/Superlinear.lean` and `Zeta23/OffLine.lean` of this layer; [EXTERNAL \| run here], an artifact of others re-checked here. For the two Mathlib-only lemmas of run 7, which the register does not list, the tag is that of the README of add-on v6. The three statements of `Cube.lean` that carry the two equivalences (the second in two forms) are tagged [PROVED \| this tree], because their proofs use the reflection lemma `zetaZeroConfig.reflect_mem` of the zeta23 library, and the third also the real-zero theorem; until its revision of 2026-11-11 the register printed [PROVED] for them. "Run" is the first run that judged the statement. For the two rows of run 3 that mention the gap hypothesis, run 3 compared the library's definitions as holes; their bodies were first compared in run 4. No row proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

| Lean name | Module | Reading | Register tag | Run |
|---|---|---|---|---|
| `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` | `OAI.NumberTheory.DirichletL.Nonvanishing` (OpenAI) | $\zeta(s) \ne 0$ for $\operatorname{Re} s > 7/8$ | [EXTERNAL \| run here] | 1 |
| `two_thirds_simple_on_critical_line` | `Solution` (zeta23, Anthropic) | for every $\varepsilon > 0$ and all large $T$, the simple zeros on the line with $T < \gamma \le 2T$ number at least $(2/3 - \varepsilon)$ times all zeros in that window, the latter counted with multiplicity | [EXTERNAL \| run here] | 2 |
| `MNF.RH.riemannHypothesis_iff_gap_half` | `MNF/RH/Gap.lean` | for $\Delta \ge 1/2$: RH $\iff G(\Delta)$ | [PROVED] | 3 |
| `MNF.RH.riemannHypothesis_iff_gap_three_eighths` | `MNF/RH/Unconditional.lean` | for $\Delta > 3/8$: RH $\iff G(\Delta)$ | [PROVED \| 7/8] | 3 |
| `MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths` | `MNF/RH/Unconditional.lean` | RH $\iff$ $\zeta$ has no zeros with $1/2 < \operatorname{Re} s \le 7/8$ | [PROVED \| 7/8] | 3 |
| `MNF.RH.spectralGapHyp_iff_zeroFree_strip` | `MNF/RH/Hypotheses.lean` | for every real $\Delta$: $G(\Delta) \iff$ $\zeta$ has no zeros with $1/2 < \operatorname{Re} s < 1/2 + \Delta$ | [PROVED] | 4 |
| `sturm_liouville_simple_eigenvalues` | `SturmLiouville/SimpleEigenvalues.lean` | for continuous $V$ with $V(x) \to +\infty$ as $\lvert x\rvert \to \infty$, any two $L^2$ eigenfunctions of $-u'' + Vu = \lambda u$ are proportional (not a statement about $\zeta$) | [PROVED] | 5 |
| `MNF.RH.on_line_density_one_of_gap` | `MNF/RH/GapDensity.lean` | if Bohr–Landau, the superlinear growth of $N(T)$ and $G(\Delta)$ for some $\Delta > 0$ are assumed, then $N_0(T) \ge (1 - \varepsilon) N(T)$ for large $T$ | [CONDITIONAL] | 5 |
| `MNF.RH.twoThirdsSimpleOnLine` | `MNF/RH/Zeta23Restated.lean` | zeta23's `two_thirds_simple_on_critical_line` over the library's counting functions, by definitional unfolding | [RESTATEMENT \| zeta23] | 6 |
| `MNF.RH.ncountSuperlinear` | `MNF/RH/Density.lean` | for every $c > 0$, $N(T) \ge cT$ for large $T$ (from zeta23's Riemann–von Mangoldt formula) | [RESTATEMENT \| zeta23] | 7 |
| `MNF.RH.offLine_le_one_third` | `MNF/RH/Density.lean` | $N_{\neq}(T) \le (1/3 + \varepsilon) N(T)$ for large $T$ (zeta23's Theorem B read as an upper bound) | [RESTATEMENT \| zeta23] | 7 |
| `DPMV.dirichlet_mean_value` | `Zeta23/BL/DPMV.lean` | for $T > 0$: $\int_0^T \lvert\sum_{n \le N} a_n n^{-it}\rvert^2\,dt \le T \sum_n \lvert a_n\rvert^2 + \sum_{m \ne n} 2\,\lvert a_m\rvert\,\lvert a_n\rvert / \lvert\log(n/m)\rvert$ (the elementary form; the mean square of $\zeta$ uses the Montgomery–Vaughan form `M1.dirichlet_meanSquare_le`, step 5 of *Architecture of the formal proof*) | [PROVED] | 7 |
| `sum_divisor_mul_log_le` | `Zeta23/BL/JensenDisc.lean` | for $f$ analytic near the closed disk of radius $R$ about $c$, $f(c) \ne 0$, $0 < r < R$: the number of zeros within $r$ of $c$, counted with multiplicity, times $\log(R/r)$, is at most the average of $\log\lvert f\rvert$ on the circle of radius $R$ minus $\log\lvert f(c)\rvert$ | [PROVED] | 7 |
| `Zeta23.BL.bohrLandau_gt_sixth` | `Zeta23/BL/BohrLandauPartial.lean` | for every $\delta > 1/6$: $N_{\mathrm{off}}(\delta, T) \le C T$ for $T \ge 2$ | [PROVED \| this tree] | 8 |
| `BLClosure.zeta_approx_sharp` | `Zeta23/BL/BohrLandauClosure.lean` | for $\sigma_0 > 0$: $\lvert\zeta(s) - \sum_{n \le N} n^{-s} - N^{1-s}/(s-1)\rvert \le C N^{-\sigma}$ for $s = \sigma + it \ne 1$ with $\sigma_0 \le \sigma \le 2$ and integers $N \ge 1$ with $0 \le t \le N$ | [PROVED \| this tree] | 9 |
| `BLClosure.meanSquareUnif_all` | `Zeta23/BL/BohrLandauClosure.lean` | for $\sigma_1 > 1/2$: $\int_1^T \lvert\zeta(\sigma + it)\rvert^2\,dt \le C T$ for all $\sigma \ge \sigma_1$ and $T \ge 2$ | [PROVED \| this tree] | 9 |
| `Zeta23.BL.bohrLandau_full` | `Zeta23/BL/BohrLandauClosure.lean` | the Bohr–Landau theorem: for every $\delta > 0$ there is $C_\delta$ with $N_{\mathrm{off}}(\delta, T) \le C_\delta T$ for $T \ge 2$ | [PROVED \| this tree] | 9 |
| `MNF.RH.reservoirDensityOne_unconditional` | `Zeta23/BL/BohrLandauClosure.lean` | for every $\delta > 0$ and $\varepsilon > 0$: $N_{\mathrm{off}}(\delta, T) \le \varepsilon N(T)$ for large $T$ | [PROVED \| this tree] | 9 |
| `MNF.RH.onLineDensityOne_of_gap_only` | `Zeta23/BL/BohrLandauClosure.lean` | if $G(\Delta)$ holds for some $\Delta > 0$, then $N_0(T) \ge (1 - \varepsilon) N(T)$ for large $T$ | [CONDITIONAL] on the gap alone | 9 |
| `Zeta23.BL.bohrLandau_explicit` | `MNF/RH/ReservoirMass.lean` | $N_{\mathrm{off}}(\delta, T) \le (A\,\delta^{-5/2} + B)\,T$ for $0 < \delta \le 1/2$ and $T \ge 2$ | [PROVED \| this tree] | 10 |
| `MNF.RH.reservoirMass_eq_integral` | `MNF/RH/ReservoirMass.lean` | $D(T) = \int_0^{1/2} N_{\mathrm{off}}(\delta, T)\,d\delta$ | [PROVED] bookkeeping | 10 |
| `MNF.RH.reservoirMass_le_rpow` | `MNF/RH/ReservoirMass.lean` | $D(T) \le A\,T\,(\log T)^{3/5}$ for $T \ge T_0$ | [PROVED \| this tree] | 10 |
| `MNF.RH.meanDisplacement_tendsto_zero` | `MNF/RH/ReservoirMass.lean` | $D(T)/N(T) \to 0$ as $T \to \infty$ | [PROVED \| this tree] | 10 |
| `Zeta23.Density.density_single_window` | `Zeta23/Density/StripDensity.lean` | for $1/2 < \sigma_1$ and $\sigma_1 - 1/2 < \delta \le 1/2$: $N(1/2 + \delta, T) \le C\,T^{1 - (2\sigma_1 - 1)^2/(2\sigma_1)}\,(1 + \log T)^3$ for $T \ge 2$ | [PROVED \| this tree] | 10 |
| `MNF.RH.noDegenerate_iff` | `MNF/RH/Cube.lean` | no nontrivial zero is degenerate (multiple, or sharing its ordinate with another nontrivial zero) $\iff$ every nontrivial zero is simple and has $\beta = 1/2$ | [PROVED \| this tree]; an equivalence | 11 |
| `MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros` | `MNF/RH/Cube.lean` | for every real $\Delta$: $G(\Delta) \iff$ no two distinct nontrivial zeros with $\lvert\beta - 1/2\rvert < \Delta$ share an ordinate | [PROVED \| this tree]; an equivalence | 11 |
| `MNF.RH.spectralGapHyp_iff_bandCoincidentMass` | `MNF/RH/Cube.lean` | for every real $\Delta$: $G(\Delta) \iff$ for every $T$, the part of $P(T)$ from pairs with both zeros in $\lvert\beta - 1/2\rvert < \Delta$ is $0$ | [PROVED \| this tree]; an equivalence | 11 |
| `MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo` | `MNF/RH/Cube.lean` | $\zeta(\sigma) \ne 0$ for real $0 < \sigma < 1$ | [PROVED \| this tree] | 11 |
| `MNF.RH.offDiagonalCoincidentMass_le_five_ninths` | `MNF/RH/Cube.lean` | $P(T) \le (5/9 + \varepsilon)\,N(T)^2$ for large $T$ | [PROVED \| this tree] | 11 |

The first two rows are theorems of OpenAI and of Anthropic and Alpöge–Furman; runs 1 and 2 repeat checks of them and are not first verifications. The Bohr–Landau theorem [@bohr-landau-1914] and the absence of real zeros in $(0,1)$ are classical; the zero-density estimate follows Carlson's method [@carlson-1920] with a weaker exponent than Carlson's, and the displacement bound is far weaker than those of Littlewood [@littlewood-1924] and Selberg [@selberg-1946]. Lean formalizations of stronger zero-density estimates [@lewko-density-3917] and of the absence of real zeros [@axiom-zetazeros; @hubbard-goldbach-lean] were public earlier. The equivalences in the rows of runs 3, 4 and 11 relocate the Riemann hypothesis, simplicity or the gap hypothesis; each side is as open as the other.

## References

[alpoge-furman] Levent Alpöge and Ralph Furman. More than two thirds of the zeta zeros are simple and on the critical line. arXiv:2608.13637 [math.NT], v2 (19 August 2026). DOI 10.48550/arXiv.2608.13637.

[anthropic-formal-math] Anthropic. anthropics/formal-math, project `zeta23/` (Lean 4 formalization of the theorem of [alpoge-furman]). GitHub repository, commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (2026-10-27). https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5

[aristotle] Tudor Achim, Alex Best, Alberto Bietti, et al. (23 authors). Aristotle: IMO-level Automated Theorem Proving. arXiv:2510.01346 [cs.AI], v2 (10 October 2025).

[axiom-zetazeros] Axiom Math. ZetaZerosV2 (Lean formalization of arXiv:2609.02882), file `ZetaZeros/Analytic/RealSegment.lean`. GitHub repository AxiomMath/ZetaZerosV2, commit `1d7edeb4e67096f9da1b37cd4b763e8b73886655` (2026-10-03). https://github.com/AxiomMath/ZetaZerosV2/blob/1d7edeb4e67096f9da1b37cd4b763e8b73886655/ZetaZeros/Analytic/RealSegment.lean

[bohr-landau-1914] Harald Bohr and Edmund Landau. Sur les zéros de la fonction ζ(s) de Riemann. Comptes Rendus de l'Académie des Sciences (Paris), 158 (1914), 106–110.

[bohr-landau-1914b] Harald Bohr and Edmund Landau. Ein Satz über Dirichletsche Reihen mit Anwendung auf die ζ-Funktion und die L-Funktionen. Rendiconti del Circolo Matematico di Palermo, 37 (1914), 269–272.

[carlson-1920] F. Carlson. Über die Nullstellen der Dirichletschen Reihen und der Riemannschen ζ-Funktion. Arkiv för Matematik, Astronomi och Fysik, 15, No. 20 (1920/21), 28 pp.

[claude-code] Anthropic. Claude Code (an agentic coding tool that reads a codebase, edits files and runs commands). Documentation, read 2026-11-10. https://code.claude.com/docs/en/overview

[comparator] Lean FRO. Comparator (a judge for Lean proofs: challenge file against solution file). GitHub repository leanprover/comparator, archived by its owner on 2026-10-20; tags v4.34.0 (commit `d03acab154d269c06e60e4de7e4cc85deebff94b`) and v4.33.0-rc2 (commit `75c730e9b6ef5c2c3b334fad7c3d51fe20624c88`). https://github.com/leanprover/comparator

[fiori-2026] Andrew Fiori. Zero density theorems for short intervals. arXiv:2609.22624 (18 September 2026). Lean formalization: GitHub repository andrewfiori/ZeroDensityInShortIntervals; Palomar registry, entry PALOMAR-2026-09-23-000001 (registered 2026-09-23). https://data.palomar-registry.org/entries/PALOMAR-2026-09-23-000001-v1.json

[guth-maynard] Larry Guth and James Maynard. New large value estimates for Dirichlet polynomials. Annals of Mathematics (2), 203 (2026), no. 2, 623–675. DOI 10.4007/annals.2026.203.2.6.

[hubbard-goldbach-lean] Steve Hubbard. goldbach-lean (described by its repository as AI-written), file `entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean` (theorem `riemannZeta_real_neg`). GitHub repository sthubbar/goldbach-lean, commit `30ab3dd5fbb90ed832a592a0a63424ab858a94a0` (2026-10-21). https://github.com/sthubbar/goldbach-lean/blob/30ab3dd5fbb90ed832a592a0a63424ab858a94a0/entries/renyi1948/LeanLab/PNTPort/DirichletZF/SiegelSigns.lean

[ingham-1940] A. E. Ingham. On the estimation of N(σ, T). The Quarterly Journal of Mathematics (Oxford Series), 11 (1940), 291–292 (pages as in zbMATH, Zbl 0025.02704; the Crossref record of the DOI has 201–202). DOI 10.1093/qmath/os-11.1.201.

[landrun] Armin Ranjbar. landrun (runs a Linux process in an unprivileged sandbox using Landlock). GitHub repository zouuup/landrun, commit `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (2026-07-23). https://github.com/zouuup/landrun

[lean-4-35] Lean FRO. Lean 4.35.0 release notes, section "Checking Projects with lake check and lake comparator". Released 2026-10-12. https://lean-lang.org/doc/reference/latest/releases/v4.35.0/

[lean4] Leonardo de Moura and Sebastian Ullrich. The Lean 4 Theorem Prover and Programming Language. In: Automated Deduction – CADE 28, Springer, 2021, pp. 625–635. DOI 10.1007/978-3-030-79876-5_37.

[lean4export] Lean FRO. lean4export (plain-text export of Lean 4 declarations). GitHub repository leanprover/lean4export, commits `076e8e57707e813375e8f9da8bf989799ace9680` (2026-09-14) and `9fb131bb100eb32ccf6836f14e4f8328d13b6792` (2026-08-03). https://github.com/leanprover/lean4export

[levinson-montgomery-1974] Norman Levinson and H. L. Montgomery. Zeros of the derivatives of the Riemann zeta-function. Acta Mathematica, 133 (1974), 49–65. DOI 10.1007/BF02392141.

[lewko-density-32] Mark Lewko. A zero-density estimate with exponent 3(1−σ)/(2σ) for the Riemann zeta function. Palomar registry, entry PALOMAR-2026-10-09-000005 (registered 2026-10-09). https://data.palomar-registry.org/entries/PALOMAR-2026-10-09-000005-v1.json

[lewko-density-34] Mark Lewko. The density hypothesis for σ > 3/4. Palomar registry, entry PALOMAR-2026-10-07-000009 (registered 2026-10-07). https://data.palomar-registry.org/entries/PALOMAR-2026-10-07-000009-v1.json

[lewko-density-3917] Mark Lewko. Zero-density estimates from an improved large-values bound. Palomar registry, entry PALOMAR-2026-10-11-000010 (registered 2026-10-11). https://data.palomar-registry.org/entries/PALOMAR-2026-10-11-000010-v1.json

[lewko-density-improved] Mark Lewko. Improved zero-density estimates for the Riemann zeta function. Palomar registry, entry PALOMAR-2026-10-21-000008 (registered 2026-10-21). https://data.palomar-registry.org/entries/PALOMAR-2026-10-21-000008-v1.json

[littlewood-1924] J. E. Littlewood. On the zeros of the Riemann zeta-function. Proceedings of the Cambridge Philosophical Society, 22 (1924), no. 3, 295–318. DOI 10.1017/S0305004100014225.

[liu-2026] Baiying Liu. Improved zero-free half-planes for the quasi-Riemann hypothesis. arXiv:2610.12234 [math.NT], v2 (12 October 2026).

[mathlib] The mathlib Community. The Lean Mathematical Library. In: Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020), ACM, 2020, pp. 367–381. DOI 10.1145/3372885.3373824.

[montgomery-1973] H. L. Montgomery. The pair correlation of zeros of the zeta function. In: Analytic Number Theory (St. Louis, Mo., 1972), Proceedings of Symposia in Pure Mathematics 24, American Mathematical Society, 1973, pp. 181–193. DOI 10.1090/pspum/024/9944.

[montgomery-vaughan-1974] H. L. Montgomery and R. C. Vaughan. Hilbert's inequality. Journal of the London Mathematical Society (2), 8 (1974), 73–82. DOI 10.1112/jlms/s2-8.1.73.

[nanoda] ammkrn. nanoda_lib (an external type checker for Lean 4 export files). GitHub repository ammkrn/nanoda_lib; the record pins the fork robsimmons/nanoda_lib at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`. https://github.com/ammkrn/nanoda_lib

[odlyzko-1987] A. M. Odlyzko. On the distribution of spacings between zeros of the zeta function. Mathematics of Computation, 48 (1987), no. 177, 273–308. DOI 10.1090/S0025-5718-1987-0866115-0.

[openai-math] OpenAI. openai/math (mathematical manuscripts and Lean proof artifacts). GitHub repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (2026-10-06). https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a

[openai-qrh] OpenAI. The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8. OpenAI Math Release preprint, 30 September 2026; file `preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf` in [openai-math]. https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf

[palomar] Palomar Registry. A public registry of Lean-verified results. https://palomar-registry.org/

[platt-trudgian-2021] Dave Platt and Tim Trudgian. The Riemann hypothesis is true up to 3·10¹². Bulletin of the London Mathematical Society, 53 (2021), no. 3, 792–797. DOI 10.1112/blms.12460.

[pnt-plus] Alex Kontorovich and Terence Tao (organizers). Prime Number Theorem and More (PrimeNumberTheoremAnd), collaborative Lean project, launched 2024-01-09. https://github.com/AlexKontorovich/PrimeNumberTheoremAnd

[selberg-1946] Atle Selberg. Contributions to the theory of the Riemann zeta-function. Arch. Math. Naturvid., 48 (1946), no. 5, 89–155.

[speiser-1934] Andreas Speiser. Geometrisches zur Riemannschen Zetafunktion. Mathematische Annalen, 110 (1934), 514–521. DOI 10.1007/BF01448042.

[tao-trudgian-yang] Terence Tao, Tim Trudgian and Andrew Yang. New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach. arXiv:2501.16779 (28 January 2025). Companion database, zero-density chapter: https://teorth.github.io/expdb/blueprint/zero-density-chapter.html

[titchmarsh] E. C. Titchmarsh. The Theory of the Riemann Zeta-function. Second edition, revised by D. R. Heath-Brown. Oxford: Clarendon Press, 1986. x + 412 pp.

[von-mangoldt-1905] H. von Mangoldt. Zur Verteilung der Nullstellen der Riemannschen Funktion ξ(t). Mathematische Annalen, 60 (1905), 1–19. DOI 10.1007/BF01447494.
