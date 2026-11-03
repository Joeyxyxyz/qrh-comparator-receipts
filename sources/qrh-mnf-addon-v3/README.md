# QRH MNF add-on v3 — the consolidated `MNF.RH` library, Comparator-checked

Version 3 (2026-10-29) of the add-on: v1 (40 theorems) and v2 (43, definition bodies compared)
were ACCEPTED on 2026-10-28 (receipts `qrh-mnf-receipt.tar.gz`, `qrh-mnf-v2-receipt.tar.gz`).
v3 adds the frontier package (`Reduction.lean`, `Schrodinger.lean` with the Sturm–Liouville
theorem), the counting vocabulary (`Counting.lean`) and the conditional gap-density theorem
(`GapDensity.lean`): 87 theorems, 41 definitions. `Core.lean`, `Gap.lean` and `Hypotheses.lean`
are byte-identical to v2. See "What changed in v3" below.

An add-on to the QRH Comparator kit. After the kit has verified OpenAI's 7/8 zero-free-region
theorem (PASS in `RECEIPT.md`), this add-on compiles Joey's consolidated Lean library on top of
the verified tree and has Comparator judge it as a second, separate run.

## What is in the library

`MNF/RH/Core.lean` — unconditional, Mathlib only: the nontrivial zeros, their multiplicity
(`zeta_order`), simple ⟺ ζ' ≠ 0, the functional-equation symmetry ρ ↦ 1 − ρ for zeros, for ζ'
at zeros and for multiplicities, and the exact relation between Mathlib's `RiemannHypothesis`
and "every nontrivial zero has Re = 1/2".

`MNF/RH/Gap.lean` — the MNF spectral-gap hypothesis `SpectralGapProperty S Δ`: RH ⟺ gap at any
Δ ≥ 1/2 (no hypothesis), RH ⟺ gap at any Δ > θ − 1/2 given a zero-free region Re > θ, why no
smaller Δ can work, and the hackathon items made exact (sign gate, `nullify`, dilation
covariance).

`MNF/RH/Hypotheses.lean` — every assumption the corpus ever took as an `axiom`, as a named
`Prop` used only as an explicit argument (Speiser's theorem, the simple-zeros conjecture, the
gap at a given Δ, output83's extra assumption), with the conditional theorems that use them;
and (v2) `spectralGapHyp_iff_zeroFree_strip`: the gap hypothesis at `Δ` is exactly a zero-free
strip `1/2 < Re s < 1/2 + Δ`, plus the boundary case at `Δ = 3/8` under a 7/8 region.

`MNF/RH/Unconditional.lean` — the θ = 7/8 instances with the zero-free region discharged from
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`; (v2) also `spectralGapHyp_three_eighths_iff`:
a gap at exactly `3/8` ⟺ every nontrivial zero has real part `1/2`, `1/8` or `7/8` (not RH:
the 7/8 theorem does not exclude zeros on `Re s = 7/8`).

`MNF/RH/Counting.lean` [BOOKKEEPING] — zeta23's window-counting vocabulary (`zerosIn`, `Ncount`,
`Ndist`, `N0star`, `N0simple`, `cMT`) over MNF's own `is_nontrivial_zero` and `zeta_order`, spelled
as zeta23 spells it; finiteness of the zeros in a window (Mathlib); the inequalities between the
counts; and two restatements: Mathlib's `RiemannHypothesis` ⟺ on every window the distinct on-line
count equals the distinct count, and `AllZerosSimple` ⟺ on every window the count with multiplicity
equals the distinct count. (Byte-identical to the file judged on the zeta23 tree the same day.)

`MNF/RH/Reduction.lean` [PROVED] — each corpus "attack" as an ↔: the gap at Δ IS a zero-free band
`1/2 < Re ρ < 1/2 + Δ` (`gap_iff_zeroFreeBand`; one side suffices, `gap_of_right_side`;
`rh_of_band_of_zeroFree`); `MultipleZeroKillsGap` and `FischerForward` ARE "RH ⟹ all zeros
simple" (`multipleZeroKillsGap_iff`, `fischerForward_iff`); the Hilbert–Pólya step needs no operator
(`rh_of_realSpectrumRealization`); a `GapMechanism` is the same thing as the band (`gap_of_mechanism`,
`mechanism_of_gap`, `gapMechanism_iff`); the τ-line probe identities are definitional.

`SturmLiouville/SimpleEigenvalues.lean` [PROVED] — Joey's consolidated corpus file (Aristotle,
2026-03-03; consolidated 2026-10-27): for a continuous confining potential `V`, any two `L²`
eigenfunctions of `−u'' + V u = λ u` on ℝ are proportional (`sturm_liouville_simple_eigenvalues`).
Ported to this pin on 2026-10-28 with fourteen mechanical changes inside proofs (API renames,
deprecated tactics, one import); no definition and no statement changed.

`MNF/RH/Schrodinger.lean` [PROVED, hypotheses explicit] — Hilbert–Pólya through a confining
Schrödinger operator: `IsSchrodingerRealization V level eigenfunction` (a `Prop` on the data) and
`SchrodingerRealization` (its ∃); a realization gives RH (`rh_of_realization`), every level of a
realization is a simple eigenvalue by the Sturm–Liouville theorem (`eigenvalue_simple_of_realization`),
and the step to simple zeros of ζ is a `MultiplicityDictionary` that is exactly the simple-zeros
conjecture (`multiplicityDictionary_iff`). The former `structure` was replaced by the predicate plus
its ∃ so the challenge can mirror it.

`MNF/RH/GapDensity.lean` [CONDITIONAL] — the one place the gap does work that is not a
restatement: `N0` (on-line count with multiplicity), `NOff` (zeros at distance ≥ δ), the exact
split `Ncount = N0 + NOff Δ` under a gap at Δ > 0, and `on_line_density_one_of_gap`: given two
[LITERATURE] Props stated as explicit hypotheses, `BohrLandau` (zeros at fixed distance from the
line are O(T); 1914) and `NcountSuperlinear` (from Riemann–von Mangoldt), a gap at any Δ > 0 forces
density one of the zeros onto the line. No Lean library supplies either Prop as of 2026-10-28.

`MNFChallenges/*.lean` + `RH.json` — the Comparator challenge: nine Mathlib-only modules mirroring
the sources module by module (eight under the `MNF.RH` namespace and one in the root namespace for
the Sturm–Liouville file, with its own preamble), carrying the 41 definitions and the 87 theorem
statements with every proof `sorry`, generated from the sources by `scripts/gen_challenge.py`. In v2 the config's `definition_names` is empty, so Comparator compares
every definition by name, type and body (in v1 the 17 definitions were listed as holes, which
Comparator compares by name, type and universe levels only). For the bodies to be identical
constant for constant, the challenge mirrors the sources module by module (same Mathlib imports,
same `open`s, same order): Lean abstracts the proof terms inside a definition (for instance the
`Nat.AtLeastTwo` instance inside the real numeral `1/2`) into auxiliary lemmas and reuses one
already made in the same module, so a single-file challenge gives `LeftCriticalStrip` the
auxiliary lemma of `ShiftedZeroSpectrum` and Comparator rejects the pair; the local pre-check
found exactly that. `DEPOSIT_MAP.md` says what each result means for the corpus.

No file contains `axiom` or `sorry` except the challenge (`sorry` only). The expected axiom
report for every theorem is `[propext, Classical.choice, Quot.sound]`.

## What the add-on does

1. `scripts/mnf_prepare.sh` — checks the add-on against `MANIFEST.sha256` and the main kit's
   verdict (must be PASS), copies the verified tree to `~/qrh-work/mnf-tree`, adds `MNF/`,
   `MNFChallenges/`, `MNF_Audit.lean`, appends two `lean_lib` lines to the copy's
   `lakefile.lean`, and starts Comparator on `MNFChallenges/RH.json` through the kit's own
   launcher (`run_comparator.sh`: systemd user unit, AF_UNIX sockets denied, 1 GB stack, landrun
   sandbox for the build and export steps), under the label `mnf-library-v3`. The original tree,
   the main receipt and the earlier add-on runs (`~/qrh-work/mnf`, `mnf-v2`) are not touched; v3's
   logs and facts live under `~/qrh-work/mnf-v3`.
2. `scripts/mnf_status.sh [--wait N]` — where the run is.
3. `scripts/mnf_report.sh` — audits the compiled library (plain `lean`, sandboxed, on
   `MNF_Audit.lean`: `#print axioms` and `#check` for all 87 theorems) and writes
   `~/qrh-work/mnf-v3/MNF_LIBRARY.md` and `~/qrh-work/qrh-mnf-v3-receipt.tar.gz`. Its last line is
   `MNF_LIBRARY=ACCEPTED`, `=REJECTED` or `=INCOMPLETE`.

ACCEPTED requires: Comparator exit 0 with its acceptance line; the job launched with AF_UNIX
denied; the audit compile clean (no error, no `sorry`); exactly one axiom report per theorem,
each within the permitted three; and (v2) no definition holes in the config.

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-mnf-addon-v3.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-mnf-addon-v3.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-mnf-addon-v3.tar.gz && cd qrh-mnf-addon-v3
tmux new -s mnf
~/.local/bin/claude
```

Prompt: *Read CLAUDE.md and carry out the add-on protocol.* Expect 15–60 minutes. Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-work/qrh-mnf-v3-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-mnf-v3-receipt.tar.gz
```

## What changed in v3

- Five files added: `Counting.lean`, `Reduction.lean`, `Schrodinger.lean`, `GapDensity.lean` and
  `SturmLiouville/SimpleEigenvalues.lean` (a third `lean_lib`). 43 → 87 theorems, 17 → 41
  definitions; `Unconditional.lean` now imports `Schrodinger` and `GapDensity` and adds
  `rh_of_band_seven_eighths`, the 7/8 instance of `rh_of_band_of_zeroFree`.
- The two `structure`s of the frontier package (`GapMechanism`, `SchrodingerRealization`) became
  `Prop`-valued definitions with an ∃, so that Comparator compares their bodies like every other
  definition; `gapMechanism_iff` records the equivalence with the band.
- The challenge generator mirrors a root-namespace module with its own preamble (the
  Sturm–Liouville file) and keeps the order of definitions; label `mnf-library-v3`, work directory
  `~/qrh-work/mnf-v3`, bundle `qrh-mnf-v3-receipt.tar.gz`.
- Before shipping, the 79 Mathlib-only statements were built at the pin on Joey's own account and
  judged by the locally built Comparator d03acab with this configuration; the eight `Unconditional`
  statements cannot be pre-checked outside OpenAI's tree.

## What changed in v2

- Three theorems: `spectralGapHyp_iff_zeroFree_strip` and `spectralGapHyp_three_eighths_iff_of`
  (Hypotheses.lean, Mathlib only) and `spectralGapHyp_three_eighths_iff` (Unconditional.lean).
  40 → 43 theorems; the 17 definitions are unchanged.
- The challenge config lists no definition holes (`definition_names: []`), so definition bodies
  are compared; the challenge is four modules mirroring the sources (see above) instead of one
  file with `import Mathlib`.
- `mnf_report.sh` refuses ACCEPTED if the config lists holes.
- Label `mnf-library-v2`, work directory `~/qrh-work/mnf-v2`, bundle `qrh-mnf-v2-receipt.tar.gz`:
  the v1 run's files are left exactly as they were.
- `CHECKSUMS.sha256` and `scripts/verify_receipts.sh` (run from your own account, where the
  bundles are): re-derive every hash the deposit cites and re-read both verdicts.
- `DEPOSIT_MAP.md` §8 records the external results read for this work (Anthropic's zeta23) with
  pins and hashes, and says they were read, not run here.
- Before shipping, the three Mathlib-only files and the 36 Mathlib-only statements were built at
  the same pin (Lean v4.34.1, Mathlib d13f23b7) on Joey's own account and judged by a locally
  built Comparator d03acab (lean4export 076e8e5, landrun 811cfff) with the new config, outside
  the kit's systemd unit; that pre-check is not the receipt. The seven Unconditional statements
  cannot be pre-checked outside OpenAI's tree.

## Pins

Same as the kit: Lean v4.34.1, Mathlib d13f23b7, openai/math adc7f124, Comparator d03acab
(v4.34.0 source, built with 4.34.1), lean4export 076e8e5, landrun 811cfff. The library also
compiles unchanged at the corpus pin (Lean v4.24.0, Mathlib f897ebcf), except
`Unconditional.lean`, which needs OpenAI's tree.
