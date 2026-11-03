# QRH zeta23 add-on — an independent Comparator run of Anthropic's `zeta23`

An add-on to the QRH Comparator kit. It repeats, on Joey's laptop and under the kit's own
launcher, the check Anthropic reports for its public Lean formalization of Alpöge–Furman,
"More than two thirds of the zeta zeros are simple and on the critical line"
(arXiv:2608.13637): github.com/anthropics/formal-math, directory `zeta23/`, pinned by commit
and by the sha256 of its nine trusted files. The result is a receipt in the same spirit as
`RECEIPT.md` for OpenAI's 7/8 theorem: what was checked, what the checker answered, and what
that answer is and is not worth.

It does not touch the main kit's work (`~/qrh-work`) or the MNF add-ons' runs; everything
happens under `~/qrh-zeta23-work`. It does not change the MNF library and proves nothing new:
Stage B of the plan is this receipt first, and the restatement of zeta23's theorems over
MNF's definitions only after it.

## What the run checks

Comparator builds `Challenge` (the 17 statements with `sorry` proofs, Mathlib only, with the
counting definitions of `ChallengeDeps.lean` inlined) and `Solution` (the same statements
proved by the `Zeta23` library, about 316 files and 100,000 lines, compiled from source inside
the sandbox), exports both with lean4export, checks that every statement and every constant it
mentions agree, that the proofs use only `propext`, `Quot.sound`, `Classical.choice`, and
replays the solution in Lean's kernel and, when NanoDa is available, in the NanoDa kernel.

The 17 statements: `two_thirds_on_critical_line` (and `_cumulative`),
`two_thirds_simple_on_critical_line` (and `_cumulative`), `five_sixths_distinct` (and
`_cumulative`), the Montgomery–Taylor refinements (`montgomery_taylor_on_critical_line`,
`montgomery_taylor_simple_on_critical_line_mult` and `_cumulative`,
`montgomery_taylor_distinct_mult` and `_cumulative`), and the six Dirichlet analogues
(`dirichlet_*`). The receipt prints the whole of `Challenge.lean`.

## The second run: the MNF library on the checked tree (step B2)

After the receipt, `scripts/z23_mnf.sh` puts Joey's `MNF.RH` library on top of the same
checkout and has Comparator judge it as a second run, label `zeta23-mnf`:

- `MNF/RH/Core.lean`, `Gap.lean`, `Hypotheses.lean`: byte-identical to the MNF add-on v2 (ACCEPTED
  on OpenAI's tree on 2026-10-28; pinned here by sha256). They compile unchanged at zeta23's pin.
- `MNF/RH/Counting.lean` [BOOKKEEPING]: zeta23's counting vocabulary (`zerosIn`, `Ncount`,
  `Ndist`, `N0star`, `N0simple`, `cMT`) spelled exactly as zeta23 spells it but over MNF's
  `is_nontrivial_zero` and `zeta_order`; finiteness of the zeros in a window (from Mathlib's
  `IsCompact.inter_riemannZetaZeros_finite`), the inequalities between the counts, and two
  restatements: Mathlib's `RiemannHypothesis` ⟺ on every window the distinct on-line count equals
  the distinct count; `AllZerosSimple` ⟺ on every window the count with multiplicity equals the
  distinct count. Mathlib only.
- `MNF/RH/Zeta23Restated.lean` [RESTATEMENT | zeta23]: zeta23's Theorems A, B, C and the five
  Theorem-D bounds for ζ, stated over MNF's definitions and proved by delegation to zeta23's
  `Solution` theorems (the kernel checks that MNF's definitions unfold to zeta23's), plus two
  rewrites through `Counting.lean` (Theorem B with `ζ' ≠ 0` in place of multiplicity one; Theorem
  C next to the trivial bound `Ndist ≤ Ncount`). The six Dirichlet statements are not restated:
  MNF has no Dirichlet vocabulary.
- The challenge: five Mathlib-only modules mirroring the sources module by module (see the MNF
  add-on v2's README for why), `MNFChallenges/Restated.json` with 62 theorem names (the 36
  Mathlib-only statements of the MNF library, 13 from `Counting.lean`, 13 from
  `Zeta23Restated.lean`), no definition holes, NanoDa enabled. `scripts/z23_gen_challenge.py`
  generates it inside the checkout; `MNF_AuditB2.lean` is the audit file.

What this run can and cannot say: it establishes that zeta23's Theorems A–D hold verbatim over
MNF's definitions, and that the two counting equivalences are kernel-checked restatements. It
discharges none of `SpectralGapHyp`, `AllZerosSimple`, `MultiplicityBoundOne`,
`DerivativeNonvanishing`: a proportion of zeros is not a statement about every zero. Nothing in
it uses the 7/8 theorem, and the two must never be put together as one result. The run is warm
with respect to the Zeta23 library by design (its oleans come from the accepted first run,
exactly as the MNF add-on reused OpenAI's tree); the MNF layer and the challenge are cold.

The three files and the receipt-style report (`MNF_ZETA23.md`, `qrh-zeta23-mnf-receipt.tar.gz`)
were authored and reviewed on 2026-10-28: three independent reviewers (vacuity, faithfulness and
format, overclaim) found no vacuous statement; every count threads the finiteness lemma; the
definitions match zeta23's character for character up to the two renamed constants.

## Pins (PINS-zeta23.env)

- anthropics/formal-math at `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (main on 2026-10-27; the
  zeta23 files last changed at `2bafb8c8`, 2026-08-28). Trusted files by sha256: `Challenge.lean`,
  `ChallengeDeps.lean`, `comparator.json`, `comparator-xiprime.json`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `Challenge/XiPrime.lean`, `ChallengeDeps/XiPrime.lean`.
- Lean `leanprover/lean4:v4.33.0-rc2` (seven toolchain binaries pinned by sha256), Mathlib
  `51e6992efd06126df61a496bebf8f49482a4e129` (the project's manifest).
- Comparator `v4.33.0-rc2` (`75c730e9`) and the lean4export its manifest pins (`9fb131bb`, also
  the `v4.33.0-rc2` tag), built with their own toolchain; landrun `811cfff5`, the main kit's
  static binary reused by copy and checked by hash (`63a60219…`); NanoDa `68d5ca9d` (the
  revision zeta23's own script pins), built only if `cargo` is installed.

## The second kernel

`comparator.json` asks for NanoDa (`enable_nanoda: true`). Comparator aborts if the kernel it
is asked for is absent, so when `cargo` is not installed `z23_prepare.sh` writes
`comparator-leankernel.json`, the same configuration with `enable_nanoda` set to `false`, hands
Comparator that file, and records a deviation; the receipt then says "Kernels: Lean's kernel".
To get both kernels, install Rust before running (as yourself: `sudo apt install cargo`), and
the script builds NanoDa and uses the pinned configuration unchanged.

## What the add-on does

1. `scripts/z23_prepare.sh` — manifest check; toolchain; landrun by copy and hash; Comparator and
   lean4export built; NanoDa if possible; the pinned checkout with its nine trusted files
   checked; Mathlib's prebuilt cache; the compiled dependencies recorded by hash; a cold-tree
   check; the sandbox probes; then one cold run through `run_comparator.sh` under the label
   `zeta23-main`. Returns after the launch (20–60 minutes of downloads and builds first).
2. `scripts/z23_status.sh [--wait N]` — where the run is (expect 20–60 minutes in all).
3. `scripts/z23_report.sh` — re-checks trusted files, tools and dependencies by hash, runs the
   project's own `scripts/PrintAxioms.lean` with plain `lean` in the sandbox, and writes
   `~/qrh-zeta23-work/receipt/RECEIPT-zeta23.md`, `receipt.json` and
   `~/qrh-zeta23-work/qrh-zeta23-receipt.tar.gz` (copy in `/tmp`). Last line `VERDICT=...`.

PASS requires: Comparator exit 0 with its acceptance line; run type cold; the restricted systemd
unit with AF_UNIX denied; sandbox probes passed in the same boot as the job; trusted files, tools
and compiled dependencies unchanged after the run; all pins matched; NanoDa's acceptance line
when NanoDa was enabled; every one of the 17 statements with an axiom report within the three.

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-zeta23-addon.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-zeta23-addon.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-zeta23-addon.tar.gz && cd qrh-zeta23-addon
tmux new -s zeta23
scripts/z23_prepare.sh          # 20–60 min, then the run starts detached
scripts/z23_status.sh --wait 540   # repeat until STATE=finished (hours)
scripts/z23_report.sh
```

Or give Claude Code the prompt *Read CLAUDE.md and carry out the add-on protocol.* Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-zeta23-work/qrh-zeta23-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-zeta23-receipt.tar.gz
```

## What was tested before this reached you

A dry run of the same scripts on Joey's own account on 2026-10-28 (a separate work directory,
the same pins, the same launcher, a static landrun rebuilt there, Lean's kernel only because
cargo was not installed): every check passed, the sandbox and socket probes passed, and
Comparator accepted the 17 statements in a cold run of 18 min 54 s wall clock (challenge
built and exported in about four minutes; the Zeta23 library in about twelve; largest process
7.0 GiB). Its receipt, logs and facts are next to the add-on in `qrh-zeta23-addon-dryrun/`.
It is not the receipt: the work directory, user and session differ, and two findings of that
run were folded back into the scripts afterwards (Lake rewrites three of its 16-byte `.hash`
sidecar files among the dependencies during a build, so the dependency snapshot now leaves
`.hash` files out, as it already left `.trace` out; and the report lists any modified path).

NanoDa: after cargo was installed, nanoda_bin (commit 68d5ca9d) was built on Joey's account and
the rc2 Comparator was run with `enable_nanoda: true` on its own smallest passing test project
(`tests/projects/simple_match`), with nanoda_bin found on PATH exactly as the kit's launcher
provides it: `Nanoda kernel accepts the solution`, then `Your solution is okay!`. A second dry run
of zeta23 with both kernels followed (see the dry-run folder).

The main kit's phase 3 controls (6 accepted, 15 rejected) were run with Comparator v4.34.0 on
Lean v4.34.1, not with the rc2 checker this add-on builds; the rc2 checker is the release
matching the project's toolchain, with the same compare and axiom logic (its Main.lean differs
in the NanoDa plumbing and in not printing a separate kernel-acceptance line).
