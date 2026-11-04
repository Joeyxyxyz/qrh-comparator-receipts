# QRH zeta23 add-on v4 — step B3, third run: the density layer with Bohr–Landau for every δ > 0

Joey Messina, 2026-11-03. One more Comparator run on top of the zeta23 checkout that the zeta23
add-on checked (`zeta23-main`, PASS, 2026-10-28) and on which step B2 judged the MNF.RH layer
(`zeta23-mnf`, ACCEPTED, 2026-10-29), and on which add-on v2 judged the density layer
(`zeta23-density`, ACCEPTED, 2026-11-03, 124 theorems). Add-on v3 re-judged that layer with Bohr–Landau
for δ > 1/6 (`zeta23-density-v3`, ACCEPTED, 2026-11-03, 270 theorems). This add-on re-judges all of
it together with the closure of Bohr–Landau for every δ > 0, label `zeta23-density-v4`. Same kit, same launcher (systemd user unit with AF_UNIX
denied, landrun for the build and export steps), same pins (`PINS-zeta23.env`: Lean v4.33.0-rc2,
Mathlib `51e6992e`, Comparator v4.33.0-rc2 `75c730e9`, lean4export `9fb131bb`, NanoDa).

## What the run judges (334 theorems, no definition holes, both kernels)

| module | what | register |
|---|---|---|
| `MNF/RH/GapDensity.lean` (4) | add-on v3's file (docstrings revised after an adversarial review; statements and proofs unchanged): `N0`, `NOff`, the window split under a gap, and `on_line_density_one_of_gap` | [CONDITIONAL] |
| `MNF/RH/Density.lean` (19) | `NcountSuperlinear` is a theorem (delegated to zeta23's Riemann–von Mangoldt formula); off-line zeros ≤ (1/3 + ε)·N(0,T) (zeta23's Theorem B restated); `NNear`, the near/off split at every δ, `NNear_eq_N0_of_gap`; `ReservoirDensityOne` from Bohr–Landau alone, `OnLineDensityOne` from Bohr–Landau + a gap; Bohr–Landau reduced by reflection to its right-half form | [RESTATEMENT \| zeta23], [BOOKKEEPING], [CONDITIONAL] |
| `MNF/RH/Strip.lean` (19) | the band around the line under N, E and injection; what distinguishes the true zero | [BOOKKEEPING] |
| `MNF/Extension/InjectionEjection.lean` (56) | the injection/ejection algebra of the MNF2 package (ACCEPTED at the OpenAI pin on 2026-11-03), rebuilt here | [PROVED, operator algebra] |
| `Zeta23/BL/DPMV.lean` (12), `DPMVexp.lean` (9) | a Dirichlet-polynomial mean-value inequality, two forms, Mathlib-only | [PROVED] |
| `Zeta23/BL/JensenDisc.lean` (5) | Jensen-disc inequalities: zero count × log(R/r) ≤ circle average of log‖f‖ − log‖f(c)‖; the circle average of log‖f‖ ≤ ½ log of the circle average of ‖f‖² | [PROVED] |
| `Zeta23/BL/BohrLandauPartial.lean` (139) | the uniform mean square ∫₁ᵀ‖ζ(σ+it)‖² ≤ C(σ₁)·T for σ ≥ σ₁, 2/3 ≤ σ₁ < 1, explicit constant (`M3.meanSquareUnif_explicit`); the instances 2/3 ≤ σ ≤ 1 of the sorried `meanSquare_strip` (`M45.meanSquare_strip_of`; σ = 1 vacuous, see its docstring); Jensen on discs centred 2 + it averaged in t (`rightHalf_of_meanSquareUnif`); **`rightHalf_gt_sixth` and `bohrLandau_gt_sixth`: for every δ > 1/6 the nontrivial zeros with 0 < Im ρ ≤ T and \|Re ρ − 1/2\| ≥ δ, with multiplicity, number ≤ C_δ·T for T ≥ 2** | [PROVED, this tree] |
| `Zeta23/BL/BohrLandauClosure.lean` (64) | the smooth first-derivative test (Titchmarsh 4.2/4.3 for twice-differentiable phases); the Fourier series of B₂({u}); Euler–Maclaurin for ζ from the tree's `Zeta0EqZeta`; the tail integrated by parts; one Fourier mode of the tail and the sharpened tail O(N^{−σ}); the approximate formula ζ = S_N + N^{1−s}/(s−1) + O(N^{−σ}) for N ≥ t (Titchmarsh 4.11, x = N); the uniform mean square ∫₁ᵀ‖ζ(σ+it)‖² ≤ C·T for every σ₁ > 1/2; **`Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau`** (for every δ > 0 the nontrivial zeros with 0 < Im ρ ≤ T and \|Re ρ − 1/2\| ≥ δ, with multiplicity, number ≤ C_δ·T for T ≥ 2); sorry-free versions `meanSquare_strip'`, `rightHalfBound_of_meanSquare'` of the two sorried statements of `Zeta23/BohrLandau.lean`; `MNF.RH.reservoirDensityOne_unconditional` and **`MNF.RH.onLineDensityOne_of_gap_only`** (a gap at any Δ > 0 gives density one on the line with no other hypothesis; for Δ ≥ 1/2 the gap is RH) | [PROVED, this tree] |
| `MNF/RH/DensityPartial.lean` (7) | the same in MNF vocabulary; for every δ > 1/6 density one within δ of the line with no hypothesis; a gap at any Δ > 1/6 gives density one on the line with no other hypothesis | [PROVED, this tree], [CONDITIONAL] |

Also in the tree, needed by the above and NOT in the claim set: `Zeta23/Superlinear.lean`,
`Zeta23/OffLine.lean`, `Zeta23/MNFBridge.lean` (sorry-free), and `Zeta23/BohrLandau.lean`, which
carries two `sorry` lemmas (`meanSquare_strip`, `rightHalfBound_of_meanSquare`): the analytic
inputs of Bohr–Landau as first named; both statements are now proved in `BohrLandauClosure.lean`
(`meanSquare_strip'`, `rightHalfBound_of_meanSquare'`); the original file is kept unchanged with
its sorries so that the receipts of v2 and v3 remain reproducible, and nothing claimed depends on them. No claimed theorem depends on them (the audit prints
every claimed theorem's axioms). The five MNF.RH files of step B2 are reused byte-identical.

What the run cannot say: Bohr–Landau is classical (1914); this is its formalization, not new
mathematics. Nothing here proves, weakens or replaces `SpectralGapHyp`; nothing proves, weakens or replaces
`SpectralGapHyp` (RH for Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2), `OnLineDensityOne`
follows from RH and is not known to imply it, and nothing uses the 7/8 theorem. The run is warm
with respect to the Zeta23 library (its oleans come from the accepted first run) and, in a tree
where step B2 ran, for B2's five files; it is cold for every module v4 introduces (`BohrLandauClosure` and its mirror), which
`z23_density.sh` checks; v2's and v3's modules may already be compiled, which it records.

## The challenge

`scripts/z23_gen_density_challenge.py` writes `MNFChallengesD/*.lean`: each source module mirrored
as itself with the non-Mathlib imports replaced by the mirror imports (or dropped) and every
theorem's proof replaced by `sorry`; definitions, namespaces, opens and set_options verbatim
(module-for-module, so that Lean's per-module auxiliary lemmas inside definitions agree; see the
MNF add-on v2's README). The challenge is `MNFChallengesD.All`, the solution `MNF.RH.DensityAll`;
`MNF_AuditDensity.lean` is the audit file. On the author's account the same configuration was
accepted by Comparator with both kernels on 2026-11-03 (warm pre-check, outside the launcher;
334 theorems, 81 definitions).

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-zeta23-addon-v4.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-zeta23-addon-v4.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-zeta23-addon-v4.tar.gz && cd qrh-zeta23-addon-v4
scripts/z23_density.sh                  # returns in a minute or two; the run is detached
scripts/z23_density_status.sh --wait 540   # repeat until STATE=finished (10–30 min)
scripts/z23_density_report.sh
```

Or give Claude Code the prompt *Read CLAUDE.md and carry out the add-on protocol.* Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-zeta23-work/qrh-zeta23-density-v4-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-zeta23-density-v4-receipt.tar.gz
```

## Provenance

The Lean files of 2026-11-03 (Density, Strip, DensityPartial, the BL lemmas, BohrLandauPartial and
BohrLandauClosure — the last two written by workflow agents from a dependency plan, merged, and
prose-reviewed — the ports of GapDensity and of the
injection/ejection algebra) were written with Claude Code under Joey's direction; the four
`Zeta23/*.lean` files were supplied by Joey the same day; every theorem is kernel-checked and the
prose was corrected after an adversarial review (`notes/density-field-2026-11-03/plan/REVIEW_2026-11-03.md`
on the drive). Apache-2.0 for Joey's files; zeta23 and Mathlib keep their licenses.
