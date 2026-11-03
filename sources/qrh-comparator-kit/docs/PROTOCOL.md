# The protocol: what is checked, what a PASS is worth, and why each step exists

## The claim under test

OpenAI's repository `github.com/openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`
(titled "Initial commit", dated 2026-10-06, and still the head of the repository when this kit
was written), contains a Lean 4 file that states

```lean
theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

and 2,924 further files that are said to prove it. `riemannZeta` is Mathlib's function. In words:
the Riemann zeta function has no zero with real part greater than 7/8.

OpenAI's own catalogue of these formalizations, `lean/formalization.yaml`, carries
`review: status: unchecked`. The repository ships a Comparator configuration for this theorem
and a three-line instruction for running it. This kit runs it, with the precautions Comparator's
documentation asks for and some it does not.

## How Comparator decides

Comparator is the Lean FRO's judge for exactly this situation: someone hands you a statement
you can read and a proof you cannot. It needs two modules. The *challenge* states the theorem
with the proof left out. The *solution* states it again with a proof. Here the challenge is
`ComparatorChallenges/QuasiRiemannHypothesis.lean` (nine lines, importing only Mathlib) and the
solution is `OAI.NumberTheory.DirichletL.Nonvanishing`. Comparator then does five things:

1. builds the challenge inside a sandbox;
2. exports the challenge statement and every definition it refers to;
3. builds the solution inside the sandbox (the long step: 2,943 files);
4. exports the solution's theorem with everything it depends on, then checks that the two
   statements are identical, definition by definition, and that the proof uses no axiom outside
   the permitted list (`propext`, `Quot.sound`, `Classical.choice`: Lean's three standard ones);
5. replays the exported proof, all of it, through the Lean kernel.

It prints `Your solution is okay!` and exits 0 only if all of that succeeds.

## What a PASS certifies

- The theorem proved is the theorem stated in the challenge file, including the meaning of
  every symbol in it.
- The proof rests on the three standard axioms and nothing else. No `sorry`, no extra axiom, no
  trust in compiled code.
- Lean's kernel accepted every step of the proof and of everything the proof uses.

## What a PASS does not certify

- **That the Lean statement says what the paper says.** No tool checks that. The statement is
  short enough to read, and it says what the headline says.
- **Anything about the Riemann Hypothesis.** The theorem excludes zeros with real part above
  7/8. Zeros with real part between 1/2 and 7/8 are exactly as possible as before.
- **Independence from Lean itself.** One kernel checked the proof: Lean's own. A second,
  independent kernel (nanoda) exists and Comparator can call it; this kit does not, and neither
  does OpenAI's configuration. That would be the natural next hardening step.

## What the result trusts

| Trusted | Why it has to be, and what the kit does about it |
|---|---|
| Lean's kernel, and the Lean release it ships in | The kernel is the judge. The kit checks seven files of the installed toolchain against checksums of the official v4.34.1 release. |
| Comparator and lean4export | They do the comparing and the exporting. Built from pinned commits; their own regression suite is part of the controls. |
| Mathlib's definitions | The statement is about Mathlib's `riemannZeta`. Mathlib is at commit `d13f23b7`; the kit checks that its source is unmodified, before and after the run. |
| Mathlib's prebuilt cache | By default the compiled Mathlib comes from Mathlib's own server (`lake exe cache get`), as OpenAI's instructions and Comparator's README both allow. A tampered cache could change what `riemannZeta` means. `05_deps.sh --mathlib-from-source` removes this assumption by compiling Mathlib inside the sandbox, at the cost of some hours. |
| The challenge file and OpenAI's lakefile | Comparator's model treats both as yours. Both were read when the kit was written and are pinned by sha256. The lakefile is 335 lines: dependency pins, and code that applies OpenAI's compatibility patches to 23 dependencies. |
| The dependencies' build configuration | Lake runs each package's configuration file. Of the 42 packages, 32 use declarative TOML; the 10 Lean ones contain no `run_cmd` and one `post_update` hook (Mathlib's cache download, which the kit switches off). The set is pinned by digest and re-checked after the run. |
| landrun, Landlock, systemd, the Linux kernel | They are the sandbox. Before the real run, and again in the same boot at launch, the kit proves by behaviour that the sandbox denies a forbidden write and that the socket restriction holds; one control makes a proof file attempt forbidden writes while Comparator itself compiles it. |
| Go and its module proxy | Only to build landrun. The `go` command verifies the Go release and landrun's modules against Go's public checksum database. |
| The machine and its operator | A receipt is a record, not a cryptographic proof. Anyone with the same kit can repeat the run. |

## How Comparator's stated assumptions are met

Comparator's README lists six. In order:

1. *Challenge imports and lakefile are yours or trustworthy.* See the table above.
2. *The solution was never compiled outside the sandbox.* The tree is fetched fresh; phase 5
   and phase 6 both check that no build output of the challenge, the solution, or the two
   third-party libraries exists before the run. The proof is compiled only by Comparator, and
   only a cold run can end in PASS.
3. *landrun and lean4export are available.* Built in phase 2 at pinned commits.
4. *landrun works and is not exploited.* Phase 3 tests it by behaviour. An exploit cannot be
   ruled out by testing; the scan below found nothing in the proof's files that could attempt
   one.
5. *The kernel is correct.* Assumed.
6. *Not run as a privileged user.* Every phase after phase 0 runs as an account with no sudo
   rights. Every Comparator launch, the controls included, happens inside a systemd unit with
   `RestrictAddressFamilies=~AF_UNIX`, as the README asks.

## Precautions beyond the README

- **A static landrun.** Comparator runs under `lake env`, which puts every package's build
  directory on the library search path, and those directories are writable from inside the
  sandbox. A sandbox launcher that needed the dynamic loader could be handed a planted library
  on its second use. The kit builds landrun without cgo and refuses to go on unless the binary
  is static.
- **`SystemCallArchitectures=native`** on the unit, which systemd's manual recommends alongside
  the socket restriction so that it cannot be bypassed through the 32-bit system-call interface.
- **Nothing interprets the build tree afterwards.** Once the proof has been compiled, the kit
  runs neither `git` nor `lake` on anything under `.lake`: it compares sha256 checksums recorded
  in phase 5. The bridge step loads compiled files only inside a sandbox.
- **The kit is read-only on the droplet** (owned by root, under `/opt`), and the receipt is
  INVALID if any kit file differs from the shipped manifest.
- **The run vouches for itself.** The job that runs Comparator records, from inside its own
  unit, that it could not create an AF_UNIX socket, and that an attempt of a given kind (cold or
  warm) began. The receipt requires both records. A Comparator command started by hand, outside
  the launcher, cannot end in PASS.

Three launch details differ from the README's one-line command without changing what it does:
the run is a detached systemd unit rather than a terminal session; the unit has
`OOMPolicy=continue`, so that if the kernel kills one process for lack of memory, the job script
survives to record the exit code; and the unit's stack limit is 1 GiB instead of the usual
8 MiB. The kernel replay follows the proof's dependencies recursively, and a long enough chain
of them would otherwise abort the run at its very end, after hours of building. A run at
Mathlib's scale behaved identically with both limits.

## What was read and measured when the kit was written (2026-10-07)

- The proof's import closure: 2,924 project files, 486,490 lines, all in
  `lean/OAI/NumberTheory/DirichletL`, about 25,000 declarations. Outside the project it imports
  248 Mathlib modules, one Lean core module, 4 files of PrimeNumberTheoremAnd and 15 of
  rellich-kondrachov (both with OpenAI's patches applied).
- A plain-text scan of those 2,943 files found no occurrence, not even in a comment, of `sorry`,
  `axiom`, `native_decide`, `set_option`, `unsafe`, `implemented_by`, `extern`, `macro`, `elab`,
  `syntax`, `run_cmd`, `run_tac`, `by_elab`, `simproc`, `IO.`, `open Lean`, or any command
  beginning with `#`. The only way the files extend Lean's syntax is `local notation` (2,884
  uses), which abbreviates by pattern and cannot run a program. So nothing in them defines a
  tactic or runs code of its own while being compiled; what runs is Lean's and Mathlib's. A
  scan is not a proof of anything. It is the reason to expect no surprises, and Comparator is
  the check.
- `lake update` reproduced OpenAI's dependency manifest byte for byte, every time it was run
  (several independent clones).
- The files import one another in a chain 404 levels deep, and 253 of those levels hold one or
  two files. That shape, not the size, is what makes the build long: see the time estimate in
  `README.md`.
- Of Mathlib and its companion libraries, the proof's imports reach 4,101 modules out of 8,908.
- 29 of the proof's files, those that need only the part of Mathlib built on the test machine,
  were compiled there with the pinned Lean and Mathlib: no errors.
- Comparator, through this kit's launcher and sandbox, accepted a theorem of Mathlib's own (the
  functional equation of zeta) after exporting and replaying the 53,000 declarations it rests
  on. This is the largest complete run the kit has done.
- Every one of those facts is re-checked on the droplet against `PINS.env` (phases 4 and 5).
  If OpenAI changes the repository, the kit keeps checking the pinned commit and says so.

Not read: the mathematics. Nobody involved in writing this kit has checked the argument.

## The controls

Phase 3 runs 21 small projects through exactly the launcher the real run uses and requires
6 accepts and 15 rejects, each with the text that shows why:

- five written for this kit: a correct proof; the same name with a different statement
  ("theorem statement do not match"); a proof from an extra axiom and a proof by `sorry` (both
  "Illegal axiom detected"); and a correct proof whose file tries, while Comparator compiles
  it, to write next to the challenge and outside the project, which must fail while a write
  inside `.lake` succeeds;
- the sixteen projects of Comparator's own regression suite that do not need the nanoda kernel:
  four accepts and twelve rejects. Four rejects come from the statement and definition
  comparison, four from the axiom check, one from the kernel ("Lean default kernel rejects the
  solution"), and three end with lean4export aborting on a file that lacks one of the kernel's
  built-in constants. That last kind is a rejection by a blunt instrument: it shows that such
  files do not get through, not that a subtler check caught them. The expected text for each
  project is in `controls/upstream_expected.tsv`.

## The one built-in deviation

Comparator and lean4export publish a release per Lean version, and there is none for Lean
4.34.1, the version OpenAI's project uses. The kit builds their v4.34.0 release with the 4.34.1
toolchain (lean4export must be built by the same Lean that wrote the files it reads).
Comparator's source at that tag is identical to its newest one (v4.35.0-rc4) apart from the
toolchain pin and the dependency manifest. The evidence that this combination behaves is the
controls above, run with exactly these binaries.

## Re-runs: only a cold run certifies

A **cold** run starts from a tree in which nothing has been compiled. That is the situation
Comparator's assumption 2 describes, and only a cold run can end in PASS.

If an attempt ends without a decision, typically because the machine ran out of memory in step
4 or 5 after hours of building, the way to go again is `scripts/reset_tree.sh "why"`, which
deletes everything compiled and downloaded inside the checkout (earlier logs are kept and
listed in the receipt), then phase 5, then phase 6. That costs the whole build again. It is
the price of a result with no asterisk.

A **warm** run (`06_run_comparator.sh --warm`) skips the rebuilding: it goes again in the tree
as the failed attempt left it. It is a diagnostic: a quick way to learn whether more memory or
a larger stack gets the run through. If Comparator accepts in a warm run the verdict is
PROVISIONAL, not PASS, because of what a warm run leaves open. During the earlier attempt the
proof's files were compiled inside the sandbox, which may write anywhere under `.lake`. A
hostile proof could have used that to prepare the ground for the next run: a doctored compiled
challenge, altered compiled dependencies, a planted program or library in a directory that
`lake env` puts on the search paths, or changes to a dependency's build configuration, all of
which the next run would pick up outside the sandbox. The kit closes none of these for warm
runs; it only labels the result. The scan gives no reason to think OpenAI's files do any of
this. But "no reason to think so" is exactly what a certification is supposed to replace.

A decided case is never run again: after a rejection, or after an accept in a cold run, the kit
refuses a new attempt and refuses to reset the tree. An accept in a warm run is not a decision
in this sense, which is why the cold run that follows it can still end in PASS.

## The bridge step

Phase 8 is not a Comparator run. It compiles two files of Joey's with OpenAI's Lean toolchain,
each inside a landrun sandbox, in a systemd unit with the restrictions of a Comparator run (the
phase checks that it is in such a unit and refuses to run otherwise). `MNF_Bridge78.lean`
proves consequences of the 7/8 theorem with that theorem as an explicit hypothesis and imports
only Mathlib. `MNF_Bridge78_Unconditional.lean` imports OpenAI's proof and removes the
hypothesis. The phase then requires a `#print axioms` report with nothing beyond the three
standard axioms for every audited theorem, and records whether the statements Lean prints are
the ones recorded when the kit was written. See `bridge/README.md`.

Its result is exactly as strong as the PASS it stands on, and worth nothing without one. An
ordinary compile believes the compiled files it imports; it does not re-check them. When the
kit was tested, a compiled file that merely claimed OpenAI's theorem, with no proof behind it,
was enough to make this phase report success. Catching that is Comparator's job (its kernel
replay, and the control that feeds it such a file), which is why phase 8 refuses to run unless
the recorded verdict is PASS.

## Options

- `05_deps.sh --mathlib-from-source`: no cache; Mathlib is compiled in the sandbox.
- `06_run_comparator.sh --stack SIZE`: a stack limit other than 1 GiB, for a "deep recursion" or
  stack-overflow failure in the kernel replay.
- `06_run_comparator.sh --warm`: the diagnostic re-run described above.
- `06_run_comparator.sh --dirichlet`: after an accept, also try OpenAI's statement for Dirichlet
  L-functions, of which the zeta statement is a special case. Always warm, so PROVISIONAL at
  best.
