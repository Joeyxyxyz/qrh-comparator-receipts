# QRH MNF add-on v2 — the consolidated `MNF.RH` library, Comparator-checked

Version 2 (2026-10-28) of the add-on whose first run was ACCEPTED on 2026-10-28 (receipt
`qrh-mnf-receipt.tar.gz`). What changed is listed under "What changed in v2" below; the library's
`Core.lean` and `Gap.lean` are byte-identical to v1.

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

`MNFChallenges/{Core,Gap,Hypotheses,RH}.lean` + `RH.json` — the Comparator challenge: the same 17
definitions and the 43 theorem statements with every proof `sorry`, generated from the sources by
`scripts/gen_challenge.py`. In v2 the config's `definition_names` is empty, so Comparator compares
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
   sandbox for the build and export steps), under the label `mnf-library-v2`. The original tree,
   the main receipt and the v1 add-on's `~/qrh-work/mnf` are not touched; v2's logs and facts live
   under `~/qrh-work/mnf-v2`.
2. `scripts/mnf_status.sh [--wait N]` — where the run is.
3. `scripts/mnf_report.sh` — audits the compiled library (plain `lean`, sandboxed, on
   `MNF_Audit.lean`: `#print axioms` and `#check` for all 43 theorems) and writes
   `~/qrh-work/mnf-v2/MNF_LIBRARY.md` and `~/qrh-work/qrh-mnf-v2-receipt.tar.gz`. Its last line is
   `MNF_LIBRARY=ACCEPTED`, `=REJECTED` or `=INCOMPLETE`.

ACCEPTED requires: Comparator exit 0 with its acceptance line; the job launched with AF_UNIX
denied; the audit compile clean (no error, no `sorry`); exactly one axiom report per theorem,
each within the permitted three; and (v2) no definition holes in the config.

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-mnf-addon-v2.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-mnf-addon-v2.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-mnf-addon-v2.tar.gz && cd qrh-mnf-addon-v2
tmux new -s mnf
~/.local/bin/claude
```

Prompt: *Read CLAUDE.md and carry out the add-on protocol.* Expect 15–60 minutes. Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-work/qrh-mnf-v2-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-mnf-v2-receipt.tar.gz
```

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
