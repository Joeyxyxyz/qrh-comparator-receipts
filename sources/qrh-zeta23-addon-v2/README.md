# QRH zeta23 add-on v2 — step B3: the density layer, judged on the checked zeta23 tree

Joey Messina, 2026-11-03. One more Comparator run on top of the zeta23 checkout that the zeta23
add-on checked (`zeta23-main`, PASS, 2026-10-28) and on which step B2 judged the MNF.RH layer
(`zeta23-mnf`, ACCEPTED, 2026-10-29). Same kit, same launcher (systemd user unit with AF_UNIX
denied, landrun for the build and export steps), same pins (`PINS-zeta23.env`: Lean v4.33.0-rc2,
Mathlib `51e6992e`, Comparator v4.33.0-rc2 `75c730e9`, lean4export `9fb131bb`, NanoDa).

## What the run judges (124 theorems, no definition holes, both kernels)

| module | what | register |
|---|---|---|
| `MNF/RH/GapDensity.lean` (4) | add-on v3's file (docstrings revised after an adversarial review; statements and proofs unchanged): `N0`, `NOff`, the window split under a gap, and `on_line_density_one_of_gap` | [CONDITIONAL] |
| `MNF/RH/Density.lean` (19) | `NcountSuperlinear` is a theorem (delegated to zeta23's Riemann–von Mangoldt formula); off-line zeros ≤ (1/3 + ε)·N(0,T) (zeta23's Theorem B restated); `NNear`, the near/off split at every δ, `NNear_eq_N0_of_gap`; `ReservoirDensityOne` from Bohr–Landau alone, `OnLineDensityOne` from Bohr–Landau + a gap; Bohr–Landau reduced by reflection to its right-half form | [RESTATEMENT \| zeta23], [BOOKKEEPING], [CONDITIONAL] |
| `MNF/RH/Strip.lean` (19) | the band around the line under N, E and injection; what distinguishes the true zero | [BOOKKEEPING] |
| `MNF/Extension/InjectionEjection.lean` (56) | the injection/ejection algebra of the MNF2 package (ACCEPTED at the OpenAI pin on 2026-11-03), rebuilt here | [PROVED, operator algebra] |
| `Zeta23/BL/DPMV.lean` (12), `DPMVexp.lean` (9) | a Dirichlet-polynomial mean-value inequality, two forms, Mathlib-only | [PROVED] |
| `Zeta23/BL/JensenDisc.lean` (5) | Jensen-disc inequalities: zero count × log(R/r) ≤ circle average of log‖f‖ − log‖f(c)‖; the circle average of log‖f‖ ≤ ½ log of the circle average of ‖f‖² | [PROVED] |

Also in the tree, needed by the above and NOT in the claim set: `Zeta23/Superlinear.lean`,
`Zeta23/OffLine.lean`, `Zeta23/MNFBridge.lean` (sorry-free), and `Zeta23/BohrLandau.lean`, which
carries two `sorry` lemmas (`meanSquare_strip`, `rightHalfBound_of_meanSquare`): the analytic
inputs of Bohr–Landau, named, not proved. No claimed theorem depends on them (the audit prints
every claimed theorem's axioms). The five MNF.RH files of step B2 are reused byte-identical.

What the run cannot say: nothing here proves Bohr–Landau, nothing proves, weakens or replaces
`SpectralGapHyp` (RH for Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2), `OnLineDensityOne`
follows from RH and is not known to imply it, and nothing uses the 7/8 theorem. The run is warm
with respect to the Zeta23 library (its oleans come from the accepted first run) and, in a tree
where step B2 ran, for B2's five files; it is cold for every module this add-on introduces,
which `z23_density.sh` checks.

## The challenge

`scripts/z23_gen_density_challenge.py` writes `MNFChallengesD/*.lean`: each source module mirrored
as itself with the non-Mathlib imports replaced by the mirror imports (or dropped) and every
theorem's proof replaced by `sorry`; definitions, namespaces, opens and set_options verbatim
(module-for-module, so that Lean's per-module auxiliary lemmas inside definitions agree; see the
MNF add-on v2's README). The challenge is `MNFChallengesD.All`, the solution `MNF.RH.DensityAll`;
`MNF_AuditDensity.lean` is the audit file. On the author's account the same configuration was
accepted by Comparator with both kernels on 2026-11-03 (warm pre-check, outside the launcher).

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-zeta23-addon-v2.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-zeta23-addon-v2.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-zeta23-addon-v2.tar.gz && cd qrh-zeta23-addon-v2
scripts/z23_density.sh                  # returns in a minute or two; the run is detached
scripts/z23_density_status.sh --wait 540   # repeat until STATE=finished (10–30 min)
scripts/z23_density_report.sh
```

Or give Claude Code the prompt *Read CLAUDE.md and carry out the add-on protocol.* Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-zeta23-work/qrh-zeta23-density-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-zeta23-density-receipt.tar.gz
```

## Provenance

The Lean files of 2026-11-03 (Density, Strip, the BL lemmas, the ports of GapDensity and of the
injection/ejection algebra) were written with Claude Code under Joey's direction; the four
`Zeta23/*.lean` files were supplied by Joey the same day; every theorem is kernel-checked and the
prose was corrected after an adversarial review (`notes/density-field-2026-11-03/plan/REVIEW_2026-11-03.md`
on the drive). Apache-2.0 for Joey's files; zeta23 and Mathlib keep their licenses.
