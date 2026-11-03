# QRH MNF add-on — the consolidated `MNF.RH` library, Comparator-checked

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
gap at a given Δ, output83's extra assumption), with the conditional theorems that use them.

`MNF/RH/Unconditional.lean` — the θ = 7/8 instances with the zero-free region discharged from
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`.

`MNFChallenges/RH.lean` + `RH.json` — the Comparator challenge: the same 17 definitions and the
40 theorem statements with every proof `sorry`, generated from the sources by
`scripts/gen_challenge.py`. `DEPOSIT_MAP.md` says what each result means for the corpus.

No file contains `axiom` or `sorry` except the challenge (`sorry` only). The expected axiom
report for every theorem is `[propext, Classical.choice, Quot.sound]`.

## What the add-on does

1. `scripts/mnf_prepare.sh` — checks the add-on against `MANIFEST.sha256` and the main kit's
   verdict (must be PASS), copies the verified tree to `~/qrh-work/mnf-tree`, adds `MNF/`,
   `MNFChallenges/`, `MNF_Audit.lean`, appends two `lean_lib` lines to the copy's
   `lakefile.lean`, and starts Comparator on `MNFChallenges/RH.json` through the kit's own
   launcher (`run_comparator.sh`: systemd user unit, AF_UNIX sockets denied, 1 GB stack, landrun
   sandbox for the build and export steps). The original tree and the main receipt are not
   touched; the add-on's logs and facts live under `~/qrh-work/mnf`.
2. `scripts/mnf_status.sh [--wait N]` — where the run is.
3. `scripts/mnf_report.sh` — audits the compiled library (plain `lean`, sandboxed, on
   `MNF_Audit.lean`: `#print axioms` and `#check` for all 40 theorems) and writes
   `~/qrh-work/mnf/MNF_LIBRARY.md` and `~/qrh-work/qrh-mnf-receipt.tar.gz`. Its last line is
   `MNF_LIBRARY=ACCEPTED`, `=REJECTED` or `=INCOMPLETE`.

ACCEPTED requires: Comparator exit 0 with its acceptance line; the job launched with AF_UNIX
denied; the audit compile clean (no error, no `sorry`); exactly one axiom report per theorem,
each within the permitted three.

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-mnf-addon.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-mnf-addon.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-mnf-addon.tar.gz && cd qrh-mnf-addon
tmux new -s mnf
~/.local/bin/claude
```

Prompt: *Read CLAUDE.md and carry out the add-on protocol.* Expect 15–60 minutes. Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-work/qrh-mnf-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-mnf-receipt.tar.gz
```

## Pins

Same as the kit: Lean v4.34.1, Mathlib d13f23b7, openai/math adc7f124, Comparator d03acab
(v4.34.0 source, built with 4.34.1), lean4export 076e8e5, landrun 811cfff. The library also
compiles unchanged at the corpus pin (Lean v4.24.0, Mathlib f897ebcf), except
`Unconditional.lean`, which needs OpenAI's tree.
