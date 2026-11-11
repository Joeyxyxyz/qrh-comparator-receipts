# QRH zeta23 add-on v6 — step B3, fifth run: the density layer with the strip cube

Joey Messina, 2026-11-04. One more Comparator run on top of the zeta23 checkout that the zeta23
add-on checked (`zeta23-main`, PASS, 2026-10-28), on which step B2 judged the MNF.RH layer
(`zeta23-mnf`, ACCEPTED, 2026-10-29), and on which add-ons v2, v3 and v4 judged the density layer
(`zeta23-density`, 124 theorems, 2026-11-03; `zeta23-density-v3`, 270 theorems, Bohr–Landau for
δ > 1/6, 2026-11-03; `zeta23-density-v4`, 334 theorems, Bohr–Landau for every δ > 0, 2026-11-04;
`zeta23-density-v5`, 480 theorems, the reservoir mass and a zero-density estimate with a power
saving, 2026-11-04). This add-on re-judges all of it together with one new file, `MNF/RH/Cube.lean`,
label `zeta23-density-v6`. Same kit,
same launcher (systemd user unit with AF_UNIX denied, landrun for the build and export steps),
same pins (`PINS-zeta23.env`: Lean v4.33.0-rc2, Mathlib `51e6992e`, Comparator v4.33.0-rc2
`75c730e9`, lean4export `9fb131bb`, NanoDa).

## What the run judges (534 theorems, no definition holes, both kernels)

| module | what | register |
|---|---|---|
| `MNF/RH/GapDensity.lean` (4) | add-on v3's file (docstrings revised after an adversarial review; statements and proofs unchanged): `N0`, `NOff`, the window split under a gap, and `on_line_density_one_of_gap` | [CONDITIONAL] |
| `MNF/RH/Density.lean` (19) | `NcountSuperlinear` is a theorem (delegated to zeta23's Riemann–von Mangoldt formula); off-line zeros ≤ (1/3 + ε)·N(0,T) (zeta23's Theorem B restated); `NNear`, the near/off split at every δ, `NNear_eq_N0_of_gap`; `ReservoirDensityOne` from Bohr–Landau alone, `OnLineDensityOne` from Bohr–Landau + a gap; Bohr–Landau reduced by reflection to its right-half form | [RESTATEMENT \| zeta23], [BOOKKEEPING], [CONDITIONAL] |
| `MNF/RH/Strip.lean` (19) | the band around the line under N, E and injection; what distinguishes the true zero | [BOOKKEEPING] |
| `MNF/Extension/InjectionEjection.lean` (56) | the injection/ejection algebra of the MNF2 package (ACCEPTED at the OpenAI pin on 2026-11-03), rebuilt here | [PROVED, operator algebra] |
| `Zeta23/BL/DPMV.lean` (12), `DPMVexp.lean` (9) | a Dirichlet-polynomial mean-value inequality, two forms, Mathlib-only | [PROVED] |
| `Zeta23/BL/JensenDisc.lean` (5) | Jensen-disc inequalities: zero count × log(R/r) ≤ circle average of log‖f‖ − log‖f(c)‖; the circle average of log‖f‖ ≤ ½ log of the circle average of ‖f‖² | [PROVED] |
| `Zeta23/BL/BohrLandauPartial.lean` (139) | the uniform mean square ∫₁ᵀ‖ζ(σ+it)‖² ≤ C(σ₁)·T for σ ≥ σ₁, 2/3 ≤ σ₁ < 1, explicit constant; Jensen on discs centred 2 + it averaged in t; `rightHalf_gt_sixth`, `bohrLandau_gt_sixth` (Bohr–Landau for δ > 1/6) | [PROVED, this tree] |
| `Zeta23/BL/BohrLandauClosure.lean` (64) | the smooth first-derivative test; the Fourier series of B₂({u}); Euler–Maclaurin for ζ from the tree's `Zeta0EqZeta`; the sharpened tail O(N^{−σ}); the approximate formula ζ = S_N + N^{1−s}/(s−1) + O(N^{−σ}) for N ≥ t (Titchmarsh 4.11, x = N); the uniform mean square for every σ₁ > 1/2; **`Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau`** (for every δ > 0 the nontrivial zeros with 0 < Im ρ ≤ T and \|Re ρ − 1/2\| ≥ δ, with multiplicity, number ≤ C_δ·T for T ≥ 2); `MNF.RH.reservoirDensityOne_unconditional`, **`MNF.RH.onLineDensityOne_of_gap_only`** | [PROVED, this tree] |
| `MNF/RH/DensityPartial.lean` (7) | the same in MNF vocabulary; for every δ > 1/6 density one within δ of the line with no hypothesis; a gap at any Δ > 1/6 gives density one on the line with no other hypothesis | [PROVED, this tree], [CONDITIONAL] |
| `MNF/RH/ReservoirMass.lean` (38) | the reservoir mass Σ m(ρ)·\|Re ρ − 1/2\| over 0 < Im ρ ≤ T (`reservoirMass`): the layer-cake identity `reservoirMass T = ∫₀^{1/2} NOff δ 0 T dδ`; an explicit Bohr–Landau constant `NOff δ 0 T ≤ (A·δ^{−5/2} + B)·T` for 0 < δ ≤ 1/2, T ≥ 2 (`Zeta23.BL.bohrLandau_explicit`); **`reservoirMass T ≤ A·T·(log T)^{3/5}`** for large T (`reservoirMass_le_rpow`), hence `reservoirMass T ≤ A·(log T)^{−2/5}·N(0,T)` and **`reservoirMass T / N(0,T) → 0`** (`meanDisplacement_tendsto_zero`); the signed sum Σ m(ρ)(Re ρ − 1/2) is 0 (`signedReservoir_eq_zero`). Classically weaker than Littlewood (1924) and Selberg (1946) | [PROVED, this tree] |
| `Zeta23/Density/StripDensity.lean` (108) | a zero-density estimate with a power saving, Carlson's method in single-window form: **`Zeta23.Density.density_single_window`** — for 1/2 < σ₁ and σ₁ − 1/2 < δ ≤ 1/2 there is C with `NRight δ T ≤ C·T^{1 − (2σ₁−1)²/(2σ₁)}·(1 + log T)³` for all T ≥ 2 (at σ₁ = 3/4: O(T^{5/6}(log T)³)); the mollifier M_X = Σ_{n≤X} μ(n) n^{−s}, the product polynomial S_N·M_X and the divisor bound Σ_{m≤Y} d_X(m)² ≤ Y(1 + log X)³, Jensen discs with the majorant ½ log(ε² + ‖f‖²), the window mean square of ζ·M_X; weaker than Carlson's exponent 4σ₁(1 − σ₁), which is not proved | [PROVED, this tree] |
| **`MNF/RH/Cube.lean` (54, new)** | the strip seen through three coordinates of an ordered pair of zeros (the two shifted real parts and the ordinate difference): the zones line / punctured band / reservoir, the mirror ρ ↦ 1 − ρ̄, degenerate zeros (multiple, or sharing an ordinate with another zero). **Projection degeneracy**: an off-line zero is degenerate through its mirror (`degenerate_of_not_onLine`); "no degenerate zero" is exactly "RH and all zeros simple" (`noDegenerate_iff`); **the gap as ordinate injectivity**: `SpectralGapHyp Δ` ⟺ no two distinct zeros within Δ of the line share an ordinate (`spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros`) ⟺ the band's coincident mass vanishes in every window (`spectralGapHyp_iff_bandCoincidentMass`); the marginals of the pair measure (N·NOff, N·reservoirMass, the double layer cake `pairSum_fst_abs_eq_integral`); the atom at ordinate difference 0 (`coincidentMass_eq`, `offLine_sq_le_offDiagonalCoincidentMass`, eventually ≤ (5/9 + ε)·N² by the one-third theorem); **ζ has no real zero in (0, 1)** (`riemannZeta_ofReal_ne_zero_of_mem_Ioo`, `nontrivial_zero_im_ne_zero`), from the tree's one-term Euler–Maclaurin representation. The equivalences relocate RH, simplicity and the gap; they prove none of them | [BOOKKEEPING], [PROVED, this tree] |

Also in the tree, needed by the above and NOT in the claim set: `Zeta23/Superlinear.lean`,
`Zeta23/OffLine.lean`, `Zeta23/MNFBridge.lean` (sorry-free), and `Zeta23/BohrLandau.lean`, which
carries two `sorry` lemmas (`meanSquare_strip`, `rightHalfBound_of_meanSquare`): the analytic
inputs of Bohr–Landau as first named; both statements are proved in `BohrLandauClosure.lean`
(`meanSquare_strip'`, `rightHalfBound_of_meanSquare'`); the original file is kept unchanged with
its sorries so that the receipts of v2 and v3 remain reproducible. No claimed theorem depends on
them (the audit prints every claimed theorem's axioms). The five MNF.RH files of step B2 are
reused byte-identical. The 27 declarations of `ReservoirMass.lean` whose statements mention
zeta23-internal names (`Zeta23.Ncount`, `ell1`, `reflect`, the `Classical.choose` constants) or
a finiteness proof as a term are not in the claim set either; the existential statements that
follow them in the file are. Two `aux_` lemmas of `Cube.lean` (statements naming `Zeta23.reflect`
or a finiteness proof term) are likewise outside the claim set.

What the run cannot say: Bohr–Landau is classical (1914), Carlson's zero-density theorem is
classical (1920) and the absence of real zeros of ζ in (0, 1) is elementary; these are
formalizations with weaker constants and a weaker exponent, not new mathematics. The cube's
equivalences restate RH, the simplicity of the zeros and the gap as statements about ordinate
coincidences; each side is as open as the other, and the cubic small-distance law of the zeros is
the GUE prediction (Montgomery), not a theorem. Nothing here proves, weakens or replaces `SpectralGapHyp` (RH for Δ ≥ 1/2, an open
zero-free strip for 0 < Δ < 1/2); a zero-density estimate is a count and not a zero-free region,
it excludes no individual zero; `OnLineDensityOne` follows from RH and is not known to imply it;
a vanishing mean displacement is consistent with infinitely many zeros off the line; and nothing
uses the 7/8 theorem. The run is warm with respect to the Zeta23 library (its oleans come from the
accepted first run) and, in a tree where step B2 ran, for B2's five files; it is cold for every
module v6 introduces (`Cube` and its mirror), which `z23_density.sh` checks; the modules of
v2–v5 may already be compiled, which it records.

## The challenge

`scripts/z23_gen_density_challenge.py` writes `MNFChallengesD/*.lean`: each source module mirrored
as itself with the non-Mathlib imports replaced by the mirror imports (or dropped) and every
theorem's proof replaced by `sorry`; definitions, namespaces, opens and set_options verbatim
(module-for-module, so that Lean's per-module auxiliary lemmas inside definitions agree; see the
MNF add-on v2's README). The challenge is `MNFChallengesD.All`, the solution `MNF.RH.DensityAll`;
`MNF_AuditDensity.lean` is the audit file. On the author's account the same configuration was
accepted by Comparator with both kernels on 2026-11-04 (warm pre-check, outside the launcher;
534 theorems, 110 definitions).

## Running it (on the laptop that ran the kit)

As yourself:

```sh
sudo cp ~/Downloads/qrh-zeta23-addon-v6.tar.gz /home/qrh/ && sudo chown qrh /home/qrh/qrh-zeta23-addon-v6.tar.gz
sudo machinectl shell qrh@
```

As `qrh`:

```sh
cd ~ && tar -xzf qrh-zeta23-addon-v6.tar.gz && cd qrh-zeta23-addon-v6
scripts/z23_density.sh                  # returns in a minute or two; the run is detached
scripts/z23_density_status.sh --wait 540   # repeat until STATE=finished (10–40 min)
scripts/z23_density_report.sh
```

Or give Claude Code the prompt *Read CLAUDE.md and carry out the add-on protocol.* Afterwards,
copy the bundle to your own account:

```sh
sudo cp /home/qrh/qrh-zeta23-work/qrh-zeta23-density-v6-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-zeta23-density-v6-receipt.tar.gz
```

## Provenance

The Lean files of 2026-11-03/04 (Density, Strip, DensityPartial, the BL lemmas, BohrLandauPartial,
BohrLandauClosure, ReservoirMass, StripDensity and Cube — the last five written by workflow agents
from dependency plans, merged, and prose-reviewed — the ports of GapDensity and of the
injection/ejection algebra) were written with Claude Code under Joey's direction; the four
`Zeta23/*.lean` files were supplied by Joey; every theorem is kernel-checked and the prose was
corrected after adversarial reviews (`notes/density-field-2026-11-03/` on the drive). Apache-2.0
for Joey's files; zeta23 and Mathlib keep their licenses.
