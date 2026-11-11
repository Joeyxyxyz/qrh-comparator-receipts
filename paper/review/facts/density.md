# Fact sheet: the Lean layer judged in runs 7 to 11 on the zeta23 tree (density.md)

Compiled 2026-11-10 from the files named below. Every entry carries its evidence as a file path and an exact quote (whitespace collapsed); Lean statements are copied by script from the receipt of run 11 and are their own quotes. Nothing in this sheet proves, or is evidence for, the Riemann hypothesis, the simplicity of the zeros, or a zero-free strip next to the critical line.

## 0. Paths, conventions, and how the statements were copied

Path abbreviations used in every evidence line:

| abbreviation | path |
|---|---|
| `REPO` | `/home/joeyxyxyz/repos/qrh-comparator-receipts` |
| `V6` | `REPO/sources/qrh-zeta23-addon-v6` (the complete layer: 23 Lean files under `MNF/` and `Zeta23/`) |
| `NOTES` | `REPO/notes/density-field-2026-11-03` |
| `WORK` | the paper work area (`.../scratchpad/paper`) |
| `R7`, `R8`, `R9`, `R10`, `R11` | `WORK/extracted/qrh-zeta23-density-receipt/density`, `.../qrh-zeta23-density-v3-receipt/density-v3`, `.../qrh-zeta23-density-v4-receipt/density-v4`, `.../qrh-zeta23-density-v5-receipt/density-v5`, `.../qrh-zeta23-density-v6-receipt/density-v6` (each holds `MNF_DENSITY.md`, `audit.out`, `check.out`, `density_sha256.txt`) |

Run numbering (evidence: `REPO/README.md`: "7. **The density field** (`zeta23-density`, add-on v2)"; `REPO/README.md`: "11. **The strip cube** (`zeta23-density-v6`, add-on v6)"): run 7 = add-on v2, run 8 = add-on v3, run 9 = add-on v4, run 10 = add-on v5, run 11 = add-on v6. Do not confuse the add-on version with the run number.

How the Lean statements below were obtained. Each density report has a block "What was proved" introduced by `R11/MNF_DENSITY.md`: "As printed by Lean (`#check`), from the audit compile:". The audit file runs `#check @name` for every claimed theorem (`V6/scripts/z23_gen_density_challenge.py`: "audit += [f"#print axioms {n}" for n in all_claimed] + [""] + [f"#check @{n}" for n in all_claimed]"). Lean prints a theorem that has implicit binders with a leading `@`, and the report generator keeps only lines that start with the bare name (`V6/scripts/z23_density_check.py`: "starts = tuple(n + " " for n in wanted) + tuple(n + ":" for n in wanted)"). Consequence, counted for this sheet with a script: the "What was proved" block of `R11/MNF_DENSITY.md` contains 255 of the 534 statements; the other 279 are printed, with the leading `@`, in `R11/audit.out` of the same bundle; the axiom table of the report has all 534 rows. For runs 7 to 10 the block holds 106 of 124, 144 of 270, 171 of 334 and 218 of 480 statements (same script). Each statement below says which of the two files it was copied from. Among the principal results, the following are NOT in the report block and were copied from `R11/audit.out`: `BLClosure.zeta_approx_sharp`, `BLClosure.meanSquareUnif_all`, `MNF.RH.onLineDensityOne_of_gap_only`, `Zeta23.Density.fz_sub_one_eq`, `Zeta23.Density.meanSquare_fz_window`, `Zeta23.Density.count_le_meanSquare_fz`, `Zeta23.Density.density_single_window`, `MNF.RH.degenerate_of_not_onLine`, `MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo`.

Reading Lean's printed form: `↑` is a coercion (natural number to real, real to complex); `∑ᶠ` is Mathlib's finite sum over a set; `∫ (t : ℝ) in a..b, f t` is the interval integral; `x ^ (3 / 5)` with a real base and a real exponent is the real power function (in the source the exponents are written `((3:ℝ)/5)` and `(-(2:ℝ)/5)`: `V6/MNF/RH/ReservoirMass.lean`: "reservoirMass T ≤ A * T * (Real.log T) ^ ((3:ℝ)/5)").

## 1. The five runs

All five are Comparator runs on the zeta23 checkout that run 2 checked, with the same pins (`V6/README.md`: "same pins (`PINS-zeta23.env`: Lean v4.33.0-rc2, Mathlib `51e6992e`, Comparator v4.33.0-rc2 `75c730e9`, lean4export `9fb131bb`, NanoDa)"). Each report says what was compared: `R11/MNF_DENSITY.md`: "Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice; Lean's kernel and NanoDa replayed the solution." Each run re-judges the whole layer so far (`REPO/DEPOSIT_MAP.md`: "Each run re-judges everything of the previous one plus the new modules; run 11 is the complete layer.").

| run | label | add-on | job start (UTC) | job end (UTC) | exit | theorems | definitions | result | modules first judged in this run |
|---|---|---|---|---|---|---|---|---|---|
| 7 | `zeta23-density` | v2 | 2026-11-03T21:05:57Z | 2026-11-03T21:13:50Z | 0 | 124 | 66 | ACCEPTED | `MNF/RH/GapDensity`, `MNF/RH/Density`, `MNF/RH/Strip`, `MNF/Extension/InjectionEjection`, `Zeta23/BL/DPMV`, `Zeta23/BL/DPMVexp`, `Zeta23/BL/JensenDisc` |
| 8 | `zeta23-density-v3` | v3 | 2026-11-03T22:03:08Z | 2026-11-03T22:09:37Z | 0 | 270 | 76 | ACCEPTED | `Zeta23/BL/BohrLandauPartial`, `MNF/RH/DensityPartial` |
| 9 | `zeta23-density-v4` | v4 | 2026-11-04T00:52:20Z | 2026-11-04T00:58:43Z | 0 | 334 | 81 | ACCEPTED | `Zeta23/BL/BohrLandauClosure` |
| 10 | `zeta23-density-v5` | v5 | 2026-11-04T14:38:23Z | 2026-11-04T14:45:29Z | 0 | 480 | 98 | ACCEPTED | `MNF/RH/ReservoirMass`, `Zeta23/Density/StripDensity` |
| 11 | `zeta23-density-v6` | v6 | 2026-11-11T00:02:37Z | 2026-11-11T00:17:52Z | 0 | 534 | 110 | ACCEPTED | `MNF/RH/Cube` |

Evidence, one line per run:

- Run 7: `R7/MNF_DENSITY.md`: "Comparator job `zeta23-density`: exit 0, started 2026-11-03T21:05:57Z, ended 2026-11-03T21:13:50Z"; `R7/MNF_DENSITY.md`: "124 theorems named in the challenge config; 66 definitions in the challenge, all compared by name, type and body (definition_names is empty)"; `R7/check.out`: "MNF_DENSITY=ACCEPTED".
- Run 8: `R8/MNF_DENSITY.md`: "Comparator job `zeta23-density-v3`: exit 0, started 2026-11-03T22:03:08Z, ended 2026-11-03T22:09:37Z"; `R8/MNF_DENSITY.md`: "270 theorems named in the challenge config; 76 definitions in the challenge"; `R8/check.out`: "MNF_DENSITY=ACCEPTED".
- Run 9: `R9/MNF_DENSITY.md`: "Comparator job `zeta23-density-v4`: exit 0, started 2026-11-04T00:52:20Z, ended 2026-11-04T00:58:43Z"; `R9/MNF_DENSITY.md`: "334 theorems named in the challenge config; 81 definitions in the challenge"; `R9/check.out`: "MNF_DENSITY=ACCEPTED".
- Run 10: `R10/MNF_DENSITY.md`: "Comparator job `zeta23-density-v5`: exit 0, started 2026-11-04T14:38:23Z, ended 2026-11-04T14:45:29Z"; `R10/MNF_DENSITY.md`: "480 theorems named in the challenge config; 98 definitions in the challenge"; `R10/check.out`: "MNF_DENSITY=ACCEPTED".
- Run 11: `R11/MNF_DENSITY.md`: "Comparator job `zeta23-density-v6`: exit 0, started 2026-11-11T00:02:37Z, ended 2026-11-11T00:17:52Z"; `R11/MNF_DENSITY.md`: "534 theorems named in the challenge config; 110 definitions in the challenge, all compared by name, type and body (definition_names is empty)"; `R11/check.out`: "MNF_DENSITY=ACCEPTED"; both kernels: `R11/MNF_DENSITY.md`: "Nanoda kernel accepts the solution", `R11/MNF_DENSITY.md`: "Lean default kernel accepts the solution".
- Modules new to each run: `R8/MNF_DENSITY.md`: "compiled earlier in this tree (v2 run): MNF/RH/GapDensity MNF/RH/Density MNF/RH/Strip MNF/Extension/InjectionEjection Zeta23/Superlinear Zeta23/OffLine Zeta23/BohrLandau Zeta23/BL/DPMV Zeta23/BL/DPMVexp Zeta23/BL/JensenDisc; cold for every module v3 introduces" and `R11/MNF_DENSITY.md`: "compiled earlier in this tree (v2-v5 runs): MNF/RH/GapDensity MNF/RH/Density MNF/RH/Strip MNF/RH/DensityPartial MNF/Extension/InjectionEjection Zeta23/Superlinear Zeta23/OffLine Zeta23/BohrLandau Zeta23/BL/DPMV Zeta23/BL/DPMVexp Zeta23/BL/JensenDisc Zeta23/BL/BohrLandauPartial Zeta23/BL/BohrLandauClosure MNF/RH/ReservoirMass Zeta23/Density/StripDensity; cold for every module v6 introduces". The per-run increments match the per-module claim counts of section 2 (124; +139 +7 = 270; +64 = 334; +38 +108 = 480; +54 = 534).
- The layer files did not change between add-ons: computed for this sheet, each of the 17 layer files has the same sha256 in every add-on v2 to v6 that contains it (for example `MNF/RH/Density.lean` `f7c3828d…` in all five; `Zeta23/BL/BohrLandauPartial.lean` `04a4f8d4…` in v3 to v6), and the values agree with the "Hashes" section of `R11/MNF_DENSITY.md` (`R11/MNF_DENSITY.md`: "ca885439db1221a162d57fdf483c778b5766e140f4ccae76f665fc211a1537dd MNF/RH/Cube.lean").
- What "definitions" counts: the report generator counts `def` lines of the challenge sources (`V6/scripts/z23_density_check.py`: "defs = re.findall(r"^(?:noncomputable )?def (\S+)", challenge_src, re.M)"). Recounted for this sheet in the v6 sources: the 18 mirrored modules contain 110 `def` declarations and one `abbrev` (`V6/MNF/Extension/InjectionEjection.lean`: "abbrev Rep := List ℝ").
- The challenge configuration of run 11 (copy in the notes, sha256 `278ccfbd…` equal to the receipt's listing: `R11/MNF_DENSITY.md`: "278ccfbd7c508f10536aa1080b1e4675c7e91a23c26d98fcf2d082fdc2da7f5a MNFChallengesD/Density.json"): 534 `theorem_names`, `definition_names` empty, `permitted_axioms` propext, Quot.sound, Classical.choice, `enable_nanoda` true, challenge module `MNFChallengesD.All`, solution module `MNF.RH.DensityAll` (read from `NOTES/zeta23-tree/MNFChallengesD/Density.json`; generator: `V6/scripts/z23_gen_density_challenge.py`: "cfg = {"challenge_module": CHALLENGE_MODULE, "solution_module": SOLUTION_MODULE, "theorem_names": all_claimed, "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}").
- Axioms: all 534 axiom reports of run 11 list exactly `propext`, `Classical.choice`, `Quot.sound` (parsed by script from `R11/audit.out`; 533 reports are on one line and one, for `AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq`, is wrapped over three lines; first line: `R11/audit.out`: "'MNF.RH.N0_le_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]"); no line of any of the five `audit.out` files contains `sorryAx`.
- Warm and cold: each run is warm for the zeta23 library and for earlier layer modules and cold only for the modules it introduces (`R11/MNF_DENSITY.md`: "warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled"). The README of the add-on says the same (`V6/README.md`: "it is cold for every module v6 introduces (`Cube` and its mirror), which `z23_density.sh` checks; the modules of v2–v5 may already be compiled, which it records").

How the challenge is built (needed to say what "compared" means): a mirror of each source module with every proof replaced by `sorry` and Mathlib-only imports (`V6/scripts/z23_gen_density_challenge.py`: "A mirror is the source module itself with (a) every non-Mathlib import replaced by the import of the corresponding mirror module or dropped, and (b) every theorem's proof replaced by `sorry`."). Thirteen modules are claimed (`V6/scripts/z23_gen_density_challenge.py`: "CLAIMED = ["MNF.RH.GapDensity", "MNF.RH.Density", "MNF.RH.Strip", "MNF.Extension.InjectionEjection","); five more are mirrored for their definitions and statements but not claimed in these runs (`MNF.RH.Core`, `Gap`, `Hypotheses`, `Counting`, judged in run 6, and `Zeta23.BohrLandau`); `Zeta23/Superlinear.lean`, `Zeta23/OffLine.lean`, `Zeta23/MNFBridge.lean` and `MNF/RH/Zeta23Restated.lean` are not mirrored.

## 2. Sizes

Counted for this sheet from the files under `V6` (lines = `wc -l`; "theorems" = top-level `theorem` or `lemma` declarations; "defs" = `def`/`abbrev`; "claimed" = declarations whose fully qualified name has an axiom line in `R11/audit.out`). The claimed counts agree with the add-on's own table (`V6/README.md`: "## What the run judges (534 theorems, no definition holes, both kernels)" and the per-module figures there: `GapDensity.lean` (4), `Density.lean` (19), `Strip.lean` (19), `InjectionEjection.lean` (56), `DPMV.lean` (12), `DPMVexp.lean` (9), `JensenDisc.lean` (5), `BohrLandauPartial.lean` (139), `BohrLandauClosure.lean` (64), `DensityPartial.lean` (7), `ReservoirMass.lean` (38), `StripDensity.lean` (108), `Cube.lean` (54, new)).

| module (file under `V6`) | lines | theorems | defs | claimed | first run | content in one line |
|---|---|---|---|---|---|---|
| `MNF/RH/GapDensity.lean` | 173 | 4 | 4 | 4 | 7 | `N0`, `NOff`, `BohrLandau`, `NcountSuperlinear`; the split under a gap; the conditional density theorem with two hypotheses |
| `MNF/RH/Density.lean` | 297 | 19 | 7 | 19 | 7 | `NcountSuperlinear` and the one-third bound by delegation; the two density notions; reduction of Bohr-Landau to the right half |
| `MNF/RH/Strip.lean` | 245 | 19 | 1 | 19 | 7 | the band around the line in the author's operator vocabulary; no analytic content |
| `MNF/Extension/InjectionEjection.lean` | 956 | 69 | 31 | 56 | 7 | the author's threshold, ejection and injection operators on real numbers and lists; no zeta content |
| `Zeta23/BL/DPMV.lean` | 155 | 12 | 1 | 12 | 7 | Dirichlet-polynomial mean value, direct expansion; Mathlib only |
| `Zeta23/BL/DPMVexp.lean` | 157 | 9 | 0 | 9 | 7 | the same in the exponential form; Mathlib only |
| `Zeta23/BL/JensenDisc.lean` | 166 | 5 | 0 | 5 | 7 | two Jensen-disc inequalities; Mathlib only |
| `Zeta23/BL/BohrLandauPartial.lean` | 2190 | 139 | 6 | 139 | 8 | mean square for $\sigma\ge 2/3$; Jensen discs averaged in $t$; Bohr-Landau for $\delta>1/6$ |
| `MNF/RH/DensityPartial.lean` | 131 | 7 | 0 | 7 | 8 | the $\delta>1/6$ results over the `MNF.RH` names |
| `Zeta23/BL/BohrLandauClosure.lean` | 1290 | 64 | 5 | 64 | 9 | first-derivative test, Fourier series of $B_2$, Euler-Maclaurin, sharp approximate formula, mean square for every $\sigma_1>1/2$, Bohr-Landau for every $\delta>0$ |
| `MNF/RH/ReservoirMass.lean` | 1192 | 65 | 4 | 38 | 10 | the displacement sum, layer cake, explicit Bohr-Landau constant, the $T(\log T)^{3/5}$ bound |
| `Zeta23/Density/StripDensity.lean` | 3146 | 108 | 13 | 108 | 10 | the zero-density estimate with a power saving |
| `MNF/RH/Cube.lean` | 934 | 56 | 12 | 54 | 11 | zones, mirror, degenerate zeros, the pair sum, the two equivalences, no real zero in $(0,1)$ |
| total, 13 claimed modules | 11032 | 576 | 84 | 534 | | |
| `MNF/RH/DensityAll.lean` | 11 | 0 | 0 | 0 | 7 | the top module (imports only) |
| `MNF/RH/Core.lean`, `Gap.lean`, `Hypotheses.lean`, `Counting.lean`, `Zeta23Restated.lean` | 383, 237, 203, 212, 191 | 30, 19, 10, 13, 13 | 7, 5, 5, 6, 0 | 0 | (run 6) | the five files of step B2, reused; not in the claim set of runs 7 to 11 |
| `Zeta23/Superlinear.lean`, `OffLine.lean`, `BohrLandau.lean`, `MNFBridge.lean` | 74, 62, 117, 46 | 4, 4, 9, 7 | 1, 2, 4, 0 | 0 | 7 (in the tree, not claimed) | supplied files; see section 6 |
| total, all 23 Lean files | 12568 | | | 534 | | |

Other size statements found in the record, with the differences noted:

- `BohrLandauPartial.lean`: `NOTES/plan/BOHR_LANDAU_PARTIAL.md`: "2172 lines, 145 declarations, no `sorry`". The installed file has 2190 lines and 139 theorems plus 6 definitions (145 declarations); the line count in the note predates the prose review.
- `BohrLandauClosure.lean`: `NOTES/plan/BOHR_LANDAU_CLOSURE.md`: "64 theorems, no `sorry`".
- `ReservoirMass.lean`: `NOTES/DENSITY_LEDGER.md`: "source `zeta23-tree/MNF/RH/ReservoirMass.lean`, 65 declarations, standard axioms" (65 theorems and lemmas; 38 claimed).
- `StripDensity.lean`: `NOTES/DENSITY_LEDGER.md`: "`zeta23-tree/Zeta23/Density/StripDensity.lean`, 108 declarations, standard axioms".
- `Cube.lean`: `NOTES/DENSITY_LEDGER.md`: "56 declarations, 54 claimed, standard axioms".
- `InjectionEjection.lean`: `V6/MNF/Extension/InjectionEjection.lean`: "all 31 definitions, and every one of its 18 attempted proofs closed as written. Its 38 `sorry` proofs were then filled by Claude Code (eight prover agents, statements untouched, 13 helper lemmas named aux_*)" (56 theorems + 13 `aux_` lemmas = 69).

## 3. Definitions the statements use, and the notation map

Notation of the paper: nontrivial zeros $\rho=\beta+i\gamma$, $0<\beta<1$, multiplicity $m(\rho)$.

| paper | Lean | definition (source) |
|---|---|---|
| nontrivial zero | `MNF.RH.is_nontrivial_zero ρ` | $\zeta(\rho)=0$ and $0<\operatorname{Re}\rho<1$ |
| $m(\rho)$ | `MNF.RH.zeta_order ρ` | the order of vanishing of $\zeta$ at $\rho$ as a natural number |
| zeros with $T_1<\gamma\le T_2$ | `MNF.RH.zerosIn T₁ T₂` | a set of complex numbers; finite (`zerosIn_finite`) |
| $N(T)$ | `MNF.RH.Ncount 0 T` | $\sum_{0<\gamma\le T} m(\rho)$ |
| $N_0(T)$ | `MNF.RH.N0 0 T` | zeros with $\beta=1/2$, $0<\gamma\le T$, with multiplicity |
| $N_{\mathrm{off}}(\delta,T)$ | `MNF.RH.NOff δ 0 T` | zeros with $\lvert\beta-1/2\rvert\ge\delta$, $0<\gamma\le T$, with multiplicity |
| zeros off the line | `MNF.RH.NOffLine 0 T` | zeros with $\beta\ne 1/2$, $0<\gamma\le T$, with multiplicity |
| $N(\sigma,T)$, $\sigma=1/2+\delta$ | `MNF.RH.NRight δ T`, `Zeta23.BL.NRight δ T` | zeros with $\beta-1/2\ge\delta$, $0<\gamma\le T$, with multiplicity (two definitions with the same body) |
| left-half count | `MNF.RH.NLeft δ T` | zeros with $1/2-\beta\ge\delta$ |
| zeros within $\delta$ of the line | `MNF.RH.NNear δ 0 T` | zeros with $\lvert\beta-1/2\rvert<\delta$ |

The window is $0<\gamma\le T$ (positive ordinates only), and every count is with multiplicity.

```lean
def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
```

Source of the text: `V6/MNF/RH/Core.lean`, line 52.

```lean
noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat
```

Source of the text: `V6/MNF/RH/Core.lean`, line 58.

```lean
def ShiftedZeroSpectrum : Set ℝ := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}

def AllZerosSimple : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ = 1
```

Source of the text: `V6/MNF/RH/Core.lean`, lines 61 to 63.

```lean
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
```

Source of the text: `V6/MNF/RH/Counting.lean`, line 52.

```lean
noncomputable def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ
```

Source of the text: `V6/MNF/RH/Counting.lean`, line 57.

```lean
noncomputable def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/GapDensity.lean`, line 64.

```lean
noncomputable def NOff (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/GapDensity.lean`, line 68.

```lean
noncomputable def NNear (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | |ρ.re - 1 / 2| < δ}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/Density.lean`, line 68.

```lean
noncomputable def NOffLine (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re ≠ 1 / 2}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/Density.lean`, line 72.

```lean
noncomputable def NRight (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | δ ≤ ρ.re - 1 / 2}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/Density.lean`, line 76.

```lean
noncomputable def NLeft (δ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn 0 T ∩ {ρ | δ ≤ 1 / 2 - ρ.re}, zeta_order ρ
```

Source of the text: `V6/MNF/RH/Density.lean`, line 80.

The named propositions (each is a `Prop`; none is asserted by its definition):

```lean
def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T
```

Source of the text: `V6/MNF/RH/GapDensity.lean`, line 73.

Plain form of `BohrLandau`: for every $\delta>0$ there is $C$ such that $N_{\mathrm{off}}(\delta,T)\le C\,T$ for all $T\ge 2$.

```lean
def NcountSuperlinear : Prop := ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ T ≥ T₀, c * T ≤ (Ncount 0 T : ℝ)
```

Source of the text: `V6/MNF/RH/GapDensity.lean`, line 80.

Plain form of `NcountSuperlinear`: for every $c>0$ there is $T_0$ with $N(T)\ge cT$ for all $T\ge T_0$.

```lean
def RightHalfBound : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NRight δ T : ℝ) ≤ C * T
```

Source of the text: `V6/MNF/RH/Density.lean`, line 83.

```lean
def ReservoirDensityOne : Prop :=
  ∀ δ > 0, ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (NOff δ 0 T : ℝ) ≤ ε * Ncount 0 T
```

Source of the text: `V6/MNF/RH/Density.lean`, lines 207 to 208.

Plain form of `ReservoirDensityOne`: for every $\delta>0$ and $\varepsilon>0$ there is $T_0$ (depending on both) with $N_{\mathrm{off}}(\delta,T)\le\varepsilon N(T)$ for all $T\ge T_0$.

```lean
def OnLineDensityOne : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 - ε) * (Ncount 0 T : ℝ) ≤ N0 0 T
```

Source of the text: `V6/MNF/RH/Density.lean`, lines 211 to 212.

Plain form of `OnLineDensityOne`: for every $\varepsilon>0$ there is $T_0$ with $(1-\varepsilon)N(T)\le N_0(T)$ for all $T\ge T_0$.

The author's gap hypothesis:

```lean
def SpectralGapProperty (S : Set ℝ) (Δ : ℝ) : Prop := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ
```

Source of the text: `V6/MNF/RH/Gap.lean`, line 34.

```lean
def SpectralGapHyp (Δ : ℝ) : Prop := SpectralGapProperty ShiftedZeroSpectrum Δ
```

Source of the text: `V6/MNF/RH/Hypotheses.lean`, line 47.

Plain form of `SpectralGapHyp Δ` (the author's "spectral gap hypothesis" at threshold $\Delta$): every nontrivial zero has $\beta=1/2$ or $\lvert\beta-1/2\rvert\ge\Delta$. In standard terms it is a zero-free strip: `V6/MNF/RH/Hypotheses.lean`: "SpectralGapHyp Δ ↔ ∀ s : ℂ, 1/2 < s.re → s.re < 1/2 + Δ → riemannZeta s ≠ 0" (theorem `spectralGapHyp_iff_zeroFree_strip`, a file of step B2, not in the claim set of runs 7 to 11). For $\Delta\ge 1/2$ it is the Riemann hypothesis: `V6/MNF/RH/Gap.lean`: "theorem riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1/2 ≤ Δ) : RiemannHypothesis ↔ SpectralGapProperty ShiftedZeroSpectrum Δ". For $0<\Delta<1/2$ it is open; the record says so in these words: `V6/README.md`: "Nothing here proves, weakens or replaces `SpectralGapHyp` (RH for Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2)".

The author's threshold operator ("nullification"):

```lean
noncomputable def nullify (Δ x : ℝ) : ℝ := if Δ ≤ |x| then x else 0
```

Source of the text: `V6/MNF/RH/Gap.lean`, line 181.

## 4. Principal results

Each entry: Lean name, module, the statement as Lean printed it in the receipt of run 11, a plain statement, the first run that carried it (the first of the five `audit.out` files in which the name has a standard-axiom line; checked by script), and remarks. All statements are unconditional unless a hypothesis is written in the statement.

### 4.1 `MNF.RH.ncountSuperlinear` (module `MNF/RH/Density.lean`; first run 7)

```lean
MNF.RH.ncountSuperlinear : MNF.RH.NcountSuperlinear
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 26 (Lean's `#check` output).

Plain statement: for every $c>0$ there is $T_0$ such that $N(T)\ge cT$ for all $T\ge T_0$; equivalently $N(T)/T\to\infty$.

Remarks. A restatement by delegation, not a new proof: `V6/MNF/RH/Density.lean`: "theorem ncountSuperlinear : NcountSuperlinear := Zeta23.ncountSuperlinear". `Zeta23.ncountSuperlinear` is in the supplied file `Zeta23/Superlinear.lean` and is derived from zeta23's Riemann-von Mangoldt formula: `V6/Zeta23/Superlinear.lean`: "obtain ⟨C, T₀, hR⟩ := riemannVonMangoldt_zeta.main". Only the main term is used (`V6/MNF/RH/Density.lean`: "only the main term is used, and it gives N(T,2T) ≥ cT for every c eventually"). Register tag in the record: `[RESTATEMENT | zeta23]`.

### 4.2 `MNF.RH.offLine_le_one_third` (module `MNF/RH/Density.lean`; first run 7)

```lean
MNF.RH.offLine_le_one_third : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ↑(MNF.RH.NOffLine 0 T) ≤ (1 / 3 + ε) * ↑(MNF.RH.Ncount 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 27 (Lean's `#check` output).

Plain statement: for every $\varepsilon>0$ there is $T_0$ such that, for all $T\ge T_0$, the number of nontrivial zeros with $\beta\ne 1/2$ and $0<\gamma\le T$, counted with multiplicity, is at most $(1/3+\varepsilon)N(T)$.

Remarks. This is Theorem B of zeta23 (Anthropic's formalization of the Alpoge-Furman theorem, receipted in run 2) read as an upper bound, by delegation: `V6/MNF/RH/Density.lean`: "[RESTATEMENT | zeta23] Theorem B (two thirds simple and on the line, with multiplicity on the left) read as an off-line bound"; the delegate is in the supplied file `Zeta23/OffLine.lean`: `V6/Zeta23/OffLine.lean`: "obtain ⟨T₀, h⟩ := thmB₀_mult_cumulative ε hε". It is not a result of this work. Companion in the same module, `MNF.RH.NOff_le_one_third` (same bound for $N_{\mathrm{off}}(\delta,T)$, $\delta>0$).

### 4.3 `MNF.RH.reservoirDensityOne_of_bohrLandau` and `MNF.RH.onLineDensityOne_of_gap` (module `MNF/RH/Density.lean`; first run 7)

```lean
MNF.RH.reservoirDensityOne_of_bohrLandau : MNF.RH.BohrLandau → MNF.RH.ReservoirDensityOne
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 28 (Lean's `#check` output).

Plain statement: if for every $\delta>0$ there is $C$ with $N_{\mathrm{off}}(\delta,T)\le CT$ for all $T\ge 2$ (the proposition `BohrLandau`), then for every $\delta>0$ and $\varepsilon>0$ there is $T_0$ with $N_{\mathrm{off}}(\delta,T)\le\varepsilon N(T)$ for all $T\ge T_0$.

```lean
MNF.RH.onLineDensityOne_of_gap : MNF.RH.BohrLandau →
  ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 42 (Lean's `#check` output).

Plain statement: if `BohrLandau` holds and, for some $\Delta>0$, every nontrivial zero has $\beta=1/2$ or $\lvert\beta-1/2\rvert\ge\Delta$ (`SpectralGapHyp Δ`), then for every $\varepsilon>0$ there is $T_0$ with $N_0(T)\ge(1-\varepsilon)N(T)$ for all $T\ge T_0$.

Remarks. In run 7 both are conditional on `BohrLandau`, which was then not proved on the tree (`R7/MNF_DENSITY.md`: "Bohr–Landau itself is NOT proved"). The gap is used once: `V6/MNF/RH/Density.lean`: "In this file the gap is used once, through `NNear_eq_N0_of_gap`: under a gap at Δ the Δ-reservoir is empty, so the δ = Δ instance of `ReservoirDensityOne` is `OnLineDensityOne`". The implication itself is folklore, in the record's words: `V6/MNF/RH/GapDensity.lean`: ""zero-free strip next to the line plus Bohr–Landau gives density one" is a folklore implication, not new mathematics". On the strength of the conclusion: `V6/MNF/RH/Density.lean`: "`OnLineDensityOne` is implied by RH and is not known to imply it". The older form with two hypotheses, `MNF.RH.on_line_density_one_of_gap` (`MNF/RH/GapDensity.lean`), is also in the claim set from run 7; its statements and proofs are those of add-on v3 of the MNF library (`V6/MNF/RH/GapDensity.lean`: "the statements and proofs are add-on v3's, unchanged"), which was run 5, on OpenAI's tree (`REPO/README.md`: "5. **MNF.RH on OpenAI's tree, v3**: 87 theorems, 41 definitions, ACCEPTED, 2026-10-29.").

### 4.4 The Dirichlet-polynomial mean value (modules `Zeta23/BL/DPMV.lean`, `Zeta23/BL/DPMVexp.lean`; first run 7)

```lean
DPMV.dirichlet_mean_value : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  0 < T →
    ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * ↑n ^ (-↑t * Complex.I)‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (↑n / ↑m)|)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 227 (Lean's `#check` output).

```lean
DPMV2.dirichlet_mean_value : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  0 < T →
    ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-↑t * Complex.I * ↑(Real.log ↑n))‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
        ∑ m ∈ Finset.Icc 1 N,
          ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log ↑n - Real.log ↑m|)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 259 (Lean's `#check` output).

Plain statement (both forms): for every sequence $a:\mathbb N\to\mathbb C$, every $N\in\mathbb N$ and every real $T>0$,
$$\int_0^T\Bigl\lvert\sum_{n=1}^N a_n n^{-it}\Bigr\rvert^2dt\ \le\ T\sum_{n=1}^N\lvert a_n\rvert^2+\sum_{\substack{1\le m,n\le N\\ m\ne n}}\lvert a_m\rvert\lvert a_n\rvert\,\frac{2}{\lvert\log(n/m)\rvert}.$$
The second form writes $n^{-it}$ as $\exp(-it\log n)$ and the denominator as $\lvert\log n-\log m\rvert$.

Remarks. Mathlib only (`V6/Zeta23/BL/DPMV.lean`: "# Dirichlet-polynomial mean value (route 1: direct expansion)"; the file's only import is Mathlib). This is the elementary form with the off-diagonal bounded term by term; the Montgomery-Vaughan form used later in the mean square of zeta is a different theorem, `M1.dirichlet_meanSquare_le` in `BohrLandauPartial.lean` (section 5a), which takes the integral expansion from this file (`V6/Zeta23/BL/BohrLandauPartial.lean`: "have h2 := congrArg Complex.re (DPMV.integral_normSq_sum a N T)").

### 4.5 The Jensen-disc inequalities (module `Zeta23/BL/JensenDisc.lean`; first run 7)

```lean
sum_divisor_mul_log_le : ∀ (c : ℂ) (r R : ℝ) (f : ℂ → ℂ),
  0 < r →
    r < R →
      AnalyticOnNhd ℂ f (Metric.closedBall c R) →
        f c ≠ 0 →
          (∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor f (Metric.closedBall c r)) u)) * Real.log (R / r) ≤
            Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 265 (Lean's `#check` output).

Plain statement: let $c\in\mathbb C$, $0<r<R$, and let $f$ be analytic on a neighbourhood of the closed disc $\lvert z-c\rvert\le R$ with $f(c)\ne 0$. Let $n(r)$ be the number of zeros of $f$ in the closed disc $\lvert z-c\rvert\le r$, with multiplicity (the sum of the divisor of $f$ on that disc). Then
$$n(r)\,\log\frac Rr\ \le\ \frac1{2\pi}\int_0^{2\pi}\log\lvert f(c+Re^{i\theta})\rvert\,d\theta-\log\lvert f(c)\rvert.$$

```lean
AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq : ∀ (c : ℂ) (R : ℝ),
  0 < R →
    ∀ (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall c R) →
        f c ≠ 0 →
          Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤
            1 / 2 * Real.log (Real.circleAverage (fun z => ‖f z‖ ^ 2) c R)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 294 (Lean's `#check` output).

Plain statement: for $R>0$ and $f$ analytic on a neighbourhood of the closed disc $\lvert z-c\rvert\le R$ with $f(c)\ne0$, the circle average of $\log\lvert f\rvert$ on $\lvert z-c\rvert=R$ is at most $\tfrac12\log$ of the circle average of $\lvert f\rvert^2$.

Remarks. Both follow from Mathlib's Jensen formula (`V6/Zeta23/BL/JensenDisc.lean`: "have jensen := h₁f'.circleAverage_log_norm hR.ne' h₂f") and the concavity of the logarithm. The module has five theorems (the two above, two measure-theoretic variants, and `AnalyticOnNhd.ae_circleMap_ne_zero`).

### 4.6 `Zeta23.BL.bohrLandau_gt_sixth` (module `Zeta23/BL/BohrLandauPartial.lean`; first run 8)

```lean
Zeta23.BL.bohrLandau_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ C * T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 387 (Lean's `#check` output).

Plain statement: for every $\delta>1/6$ there is $C$ such that $N_{\mathrm{off}}(\delta,T)\le CT$ for all $T\ge2$.

Remarks. The same statement over the `MNF.RH` names is `MNF.RH.bohrLandau_gt_sixth` (`MNF/RH/DensityPartial.lean`, first run 8), by delegation. The restriction $\delta>1/6$ belongs to the route, not to the theorem of Bohr and Landau: `V6/MNF/RH/DensityPartial.lean`: "a limitation of this route, not a theorem about ζ (classically the mean square is O(T) for every σ > 1/2)". The mean square it rests on, with its explicit constant:

```lean
@Zeta23.BL.M3.meanSquareUnif_explicit : ∀ {σ₁ : ℝ},
  2 / 3 ≤ σ₁ →
    σ₁ < 1 →
      ∀ {σ : ℝ},
        σ₁ ≤ σ →
          ∀ {T : ℝ},
            1 ≤ T →
              ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2 ≤
                (4 * (1 + 1 / (2 * σ₁ - 1)) + 208 * (1 + 4 / (2 - 2 * σ₁)) + 17 + 4 * (1 + 1 / σ₁) ^ 2) * T
```

Source of the text: `R11/audit.out`, line 1090 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: for $2/3\le\sigma_1<1$, every $\sigma\ge\sigma_1$ and every $T\ge1$, $\int_1^T\lvert\zeta(\sigma+it)\rvert^2dt\le C(\sigma_1)T$ with $C(\sigma_1)=4\bigl(1+\tfrac1{2\sigma_1-1}\bigr)+208\bigl(1+\tfrac4{2-2\sigma_1}\bigr)+17+4\bigl(1+\tfrac1{\sigma_1}\bigr)^2$.

### 4.7 `BLClosure.zeta_approx_sharp` (module `Zeta23/BL/BohrLandauClosure.lean`; first run 9)

```lean
@BLClosure.zeta_approx_sharp : ∀ {σ₀ : ℝ},
  0 < σ₀ →
    ∃ C,
      ∀ (σ t : ℝ),
        σ₀ ≤ σ →
          σ ≤ 2 →
            0 ≤ t →
              ∀ (N : ℕ),
                1 ≤ N →
                  t ≤ ↑N →
                    ↑σ + ↑t * Complex.I ≠ 1 →
                      ‖riemannZeta (↑σ + ↑t * Complex.I) - BLClosure.S N (↑σ + ↑t * Complex.I) -
                            ↑N ^ (1 - (↑σ + ↑t * Complex.I)) / (↑σ + ↑t * Complex.I - 1)‖ ≤
                        C * ↑N ^ (-σ)
```

Source of the text: `R11/audit.out`, line 1621 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: for every $\sigma_0>0$ there is $C=C(\sigma_0)$ such that for all real $\sigma,t$ with $\sigma_0\le\sigma\le2$ and $t\ge0$, every integer $N\ge1$ with $t\le N$, and $s=\sigma+it\ne1$,
$$\Bigl\lvert\zeta(s)-\sum_{n=1}^N n^{-s}-\frac{N^{1-s}}{s-1}\Bigr\rvert\le C\,N^{-\sigma}.$$
Here `BLClosure.S N s` is $\sum_{n=1}^N n^{-s}$ (`V6/Zeta23/BL/BohrLandauClosure.lean`: "noncomputable def S (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)").

Remarks. The shape of Titchmarsh's Theorem 4.11 on a narrower range, as the source says: `V6/Zeta23/BL/BohrLandauClosure.lean`: "proved here only on the narrower range x = N an integer, 0 ≤ t ≤ N, σ₀ ≤ σ ≤ 2 (4.11 allows all σ ≥ σ₀ > 0 and |t| ≤ 2πx/C, C > 1)". The constant in the proof is $C_0+1/2$ with $C_0=12\cdot\frac4{\pi^3}\sum_{\nu\ge1}\nu^{-3}+\frac14$ the constant of `tail_sharp` (`V6/Zeta23/BL/BohrLandauClosure.lean`: "refine ⟨12 * (4 / π ^ 3 * ∑' ν : ℕ, 1 / ((ν : ℝ) + 1) ^ 3) + 1 / 4, ?_⟩"; `V6/Zeta23/BL/BohrLandauClosure.lean`: "refine ⟨C₀ + 1 / 2, ?_⟩"); the statement is existential.

### 4.8 `BLClosure.meanSquareUnif_all` (module `Zeta23/BL/BohrLandauClosure.lean`; first run 9)

```lean
@BLClosure.meanSquareUnif_all : ∀ {σ₁ : ℝ},
  1 / 2 < σ₁ →
    ∃ C, ∀ (σ : ℝ), σ₁ ≤ σ → ∀ (T : ℝ), 2 ≤ T → ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2 ≤ C * T
```

Source of the text: `R11/audit.out`, line 1683 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: for every $\sigma_1>1/2$ there is $C$ such that $\int_1^T\lvert\zeta(\sigma+it)\rvert^2dt\le CT$ for all $\sigma\ge\sigma_1$ and all $T\ge2$.

Remarks. An upper bound only: `V6/Zeta23/BL/BohrLandauClosure.lean`: "This is the O(T) upper bound of the Hardy–Littlewood mean-value theorem (Titchmarsh §7.2); the asymptotic `∼ ζ(2σ) T` is not proved here." The lower limit of integration is 1, not 0.

### 4.9 `Zeta23.BL.bohrLandau_full` (module `Zeta23/BL/BohrLandauClosure.lean`; first run 9)

```lean
Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 429 (Lean's `#check` output).

Plain statement (unfolding `MNF.RH.BohrLandau`): for every $\delta>0$ there is $C_\delta$ such that the number of nontrivial zeros with $\lvert\beta-1/2\rvert\ge\delta$ and $0<\gamma\le T$, counted with multiplicity, is at most $C_\delta T$ for all $T\ge2$.

Remarks. This is the theorem of Bohr and Landau (1914), formalized; the record's words: `REPO/DEPOSIT_MAP.md`: "Bohr–Landau 1914, formalized; not new mathematics". The right-half form is `Zeta23.BL.rightHalf_all` / `Zeta23.BL.rightHalfBound`; the statement is existential in $C_\delta$ (an explicit form is 4.11).

### 4.10 `MNF.RH.onLineDensityOne_of_gap_only` and `MNF.RH.reservoirDensityOne_unconditional` (module `Zeta23/BL/BohrLandauClosure.lean`, namespace `MNF.RH`; first run 9)

```lean
MNF.RH.reservoirDensityOne_unconditional : MNF.RH.ReservoirDensityOne
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 431 (Lean's `#check` output).

Plain statement: for every $\delta>0$ and $\varepsilon>0$ there is $T_0$ such that $N_{\mathrm{off}}(\delta,T)\le\varepsilon N(T)$ for all $T\ge T_0$. No hypothesis.

```lean
@MNF.RH.onLineDensityOne_of_gap_only : ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
```

Source of the text: `R11/audit.out`, line 1696 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: if for some $\Delta>0$ every nontrivial zero has $\beta=1/2$ or $\lvert\beta-1/2\rvert\ge\Delta$, then for every $\varepsilon>0$ there is $T_0$ with $N_0(T)\ge(1-\varepsilon)N(T)$ for all $T\ge T_0$.

Remarks. Conditional on the gap hypothesis, which is not weakened: `V6/Zeta23/BL/BohrLandauClosure.lean`: "The gap hypothesis is not weakened: for `Δ ≥ 1/2` `SpectralGapHyp Δ` is RH (`riemannHypothesis_iff_gap_half`), and for `0 < Δ < 1/2` it is an unknown zero-free strip of width `Δ` beside the line"; and `V6/Zeta23/BL/BohrLandauClosure.lean`: "nothing here is progress on RH or on the gap". Both are one-line corollaries of 4.3 and 4.9 (`V6/Zeta23/BL/BohrLandauClosure.lean`: "onLineDensityOne_of_gap Zeta23.BL.bohrLandau_full hΔ hgap").

### 4.11 `Zeta23.BL.bohrLandau_explicit` (module `MNF/RH/ReservoirMass.lean`, namespace `Zeta23.BL`; first run 10)

```lean
Zeta23.BL.bohrLandau_explicit : ∃ A B,
  0 ≤ A ∧ 0 ≤ B ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 → ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ (A * δ ^ (-(5 / 2)) + B) * T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 446 (Lean's `#check` output).

Plain statement: there are constants $A,B\ge0$ such that $N_{\mathrm{off}}(\delta,T)\le(A\,\delta^{-5/2}+B)\,T$ for all $0<\delta\le1/2$ and all $T\ge2$.

Remarks. In the proof $A=2A_0$ and $B=N(4)$ (`V6/MNF/RH/ReservoirMass.lean`: "refine ⟨2 * A₀, (MNF.RH.Ncount 0 4 : ℝ), by linarith [A₀_nonneg], Nat.cast_nonneg _, ?_⟩") with $A_0=54+\tfrac{27}2B_{\mathrm{ms}}+12\log3$, $B_{\mathrm{ms}}=951+4C_G^2$ (`V6/MNF/RH/ReservoirMass.lean`: "noncomputable def A₀ : ℝ := 54 + 27 / 2 * meanSquareB + 12 * Real.log 3"; `V6/MNF/RH/ReservoirMass.lean`: "noncomputable def meanSquareB : ℝ := 951 + 4 * CG ^ 2"), where $C_G$ is the constant of 4.7 at $\sigma_0=1/2$, taken by choice and not a numeral (`V6/MNF/RH/ReservoirMass.lean`: "the one ingredient that is not a numeral"). The Lean statement only asserts existence. The statements that name $A_0$, $C_G$ are outside the claim set (section 6).

Three existential companions in the same module are in the claim set (first run 10) and carry the inputs of the displacement bound:

```lean
Zeta23.BL.meanSquare_explicit_small : ∃ B,
  0 ≤ B ∧
    ∀ (σ₁ : ℝ),
      1 / 2 < σ₁ →
        σ₁ ≤ 3 / 4 →
          ∀ (σ : ℝ),
            σ₁ ≤ σ →
              ∀ (T : ℝ), 2 ≤ T → ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2 ≤ (4 / (2 * σ₁ - 1) + B) * T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 434 (Lean's `#check` output).

Plain statement: there is $B\ge0$ such that for every $\sigma_1$ with $1/2<\sigma_1\le3/4$, every $\sigma\ge\sigma_1$ and every $T\ge2$, $\int_1^T\lvert\zeta(\sigma+it)\rvert^2dt\le\bigl(\tfrac4{2\sigma_1-1}+B\bigr)T$. One constant $B$ serves all $\sigma_1$; the dependence on $\sigma_1$ is the explicit term $4/(2\sigma_1-1)$.

```lean
Zeta23.MNF_Ncount_le_mul_log : ∃ C T₀, 2 ≤ T₀ ∧ ∀ (T : ℝ), T₀ ≤ T → ↑(MNF.RH.Ncount 0 T) ≤ C * T * Real.log T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 448 (Lean's `#check` output).

```lean
Zeta23.MNF_mul_log_le_Ncount : ∃ c, 0 < c ∧ ∃ T₀, 2 ≤ T₀ ∧ ∀ (T : ℝ), T₀ ≤ T → c * T * Real.log T ≤ ↑(MNF.RH.Ncount 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 449 (Lean's `#check` output).

Plain statements: there are $C$ and $T_0\ge2$ with $N(T)\le C\,T\log T$ for all $T\ge T_0$; there are $c>0$ and $T_0\ge2$ with $N(T)\ge c\,T\log T$ for all $T\ge T_0$. Both are derived from the tree's Riemann-von Mangoldt statement (5c, step 4) and are not results of this work beyond the derivation.

### 4.12 The displacement sum (module `MNF/RH/ReservoirMass.lean`; first run 10)

Definition (the author's "reservoir mass"; in standard words the total displacement of the zeros from the critical line, with multiplicity):

```lean
noncomputable def reservoirMass (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) * |ρ.re - 1 / 2|
```

Source of the text: `V6/MNF/RH/ReservoirMass.lean`, lines 675 to 676.

Paper notation proposed for this sheet: $D(T)=\sum_{0<\gamma\le T}m(\rho)\,\lvert\beta-1/2\rvert$.

```lean
MNF.RH.reservoirMass_eq_integral : ∀ (T : ℝ), MNF.RH.reservoirMass T = ∫ (δ : ℝ) in 0..1 / 2, ↑(MNF.RH.NOff δ 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 456 (Lean's `#check` output).

Plain statement (`reservoirMass_eq_integral`, layer cake): for every real $T$, $D(T)=\int_0^{1/2}N_{\mathrm{off}}(\delta,T)\,d\delta$.

```lean
MNF.RH.reservoirMass_le_rpow : ∃ A T₀, ∀ (T : ℝ), T₀ ≤ T → MNF.RH.reservoirMass T ≤ A * T * Real.log T ^ (3 / 5)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 487 (Lean's `#check` output).

Plain statement (`reservoirMass_le_rpow`): there are $A$ and $T_0$ such that $D(T)\le A\,T\,(\log T)^{3/5}$ for all $T\ge T_0$.

```lean
MNF.RH.reservoirMass_le_Ncount_mul : ∃ A T₀,
  ∀ (T : ℝ), T₀ ≤ T → MNF.RH.reservoirMass T ≤ A * Real.log T ^ (-2 / 5) * ↑(MNF.RH.Ncount 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 488 (Lean's `#check` output).

Plain statement (`reservoirMass_le_Ncount_mul`): there are $A$ and $T_0$ such that $D(T)\le A\,(\log T)^{-2/5}\,N(T)$ for all $T\ge T_0$.

```lean
MNF.RH.meanDisplacement_tendsto_zero : Filter.Tendsto (fun T => MNF.RH.reservoirMass T / ↑(MNF.RH.Ncount 0 T))
  Filter.atTop (nhds 0)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 490 (Lean's `#check` output).

Plain statement (`meanDisplacement_tendsto_zero`): $D(T)/N(T)\to0$ as $T\to\infty$.

```lean
MNF.RH.signedReservoir_eq_zero : ∀ (T : ℝ),
  ∑ᶠ (ρ : ℂ) (_ : ρ ∈ MNF.RH.zerosIn 0 T), ↑(MNF.RH.zeta_order ρ) * (ρ.re - 1 / 2) = 0
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 469 (Lean's `#check` output).

Plain statement (`signedReservoir_eq_zero`): for every real $T$, $\sum_{0<\gamma\le T}m(\rho)\,(\beta-1/2)=0$.

Remarks. Classical context, in the source's words: `V6/MNF/RH/ReservoirMass.lean`: "The bound T (log T)^{3/5} is far weaker than what is classically known for the same sum: Littlewood (1924) proved Σ_{0<Im ρ≤T} |Re ρ − 1/2| = O(T log log T), and Selberg (1946) proved it is O(T)". The gain over the trivial bound is only a factor $(\log T)^{-2/5}$: the trivial bound is `reservoirMass_le_half_Ncount`, $D(T)\le\tfrac12N(T)$ (`V6/MNF/RH/ReservoirMass.lean`: "the gain over the trivial bound here is the factor (log T)^{−2/5}, nothing more"). The result is compatible with zeros off the line: `V6/MNF/RH/ReservoirMass.lean`: "a vanishing mean distance is consistent with infinitely many zeros off the line". The signed identity is the functional-equation symmetry and nothing more (`V6/MNF/RH/ReservoirMass.lean`: "it is the functional-equation symmetry and nothing more"). Also claimed in the module: `reservoirMass_nonneg`, `reservoirMass_le_half_Ncount`, `reservoirMass_le_split`, `reservoirMass_le_eps_Ncount`, `reservoirMass_eq_two_right` ($D(T)$ is twice the right-half signed sum).

### 4.13 The zero-density estimate (module `Zeta23/Density/StripDensity.lean`; first run 10)

Definitions of the module (verbatim):

```lean
/-- Möbius mollifier `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`. -/
noncomputable def Mx (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Icc 1 X, ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s)
/-- the mollified zeta `f = ζ · M_X`. -/
noncomputable def fz (X : ℕ) (s : ℂ) : ℂ := riemannZeta s * Mx X s
/-- coefficient of `m^{-s}` in `S N · M_X`. -/
def cm (N X m : ℕ) : ℤ := ∑ d ∈ m.divisors.filter (· ≤ X), if m / d ≤ N then μ d else 0
/-- number of divisors of `m` that are `≤ X`. -/
def dX (X m : ℕ) : ℕ := (m.divisors.filter (· ≤ X)).card
/-- ε-majorant of `log ‖f‖` (replaces the tree's `Lz`, whose `1 +` kills every saving). -/
noncomputable def Leps (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ := (1 / 2) * Real.log (ε ^ 2 + ‖f z‖ ^ 2)
/-- zeros with `σ ≤ Re ρ`, `T₁ < Im ρ ≤ T₂`, with multiplicity (window form of `NRight`). -/
noncomputable def NSigma (σ T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ MNF.RH.zerosIn T₁ T₂ ∩ {ρ | σ ≤ ρ.re}, zeta_order ρ
```

Source of the text: `V6/Zeta23/Density/StripDensity.lean`, lines 77 to 89.

In paper notation: $M_X(s)=\sum_{n\le X}\mu(n)n^{-s}$ (the mollifier), $f_X=\zeta M_X$, $c_m=c_m(N,X)=\sum_{d\mid m,\ d\le X,\ m/d\le N}\mu(d)$, $d_X(m)=\#\{d\mid m:\ d\le X\}$, $L_\varepsilon(f)(z)=\tfrac12\log(\varepsilon^2+\lvert f(z)\rvert^2)$.

```lean
Zeta23.Density.sum_dX_sq_le : ∀ (X Y : ℕ),
  ∑ m ∈ Finset.Icc 1 Y, ↑(Zeta23.Density.dX X m) ^ 2 ≤ ↑Y * (1 + Real.log ↑X) ^ 3
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 507 (Lean's `#check` output).

Plain statement (`sum_dX_sq_le`): for all natural numbers $X,Y$, $\sum_{m=1}^Y d_X(m)^2\le Y\,(1+\log X)^3$. The logarithm is in $X$, not $Y$.

```lean
@Zeta23.Density.fz_sub_one_eq : ∀ {X : ℕ},
  1 ≤ X →
    ∀ {s : ℂ},
      1 < s.re →
        Zeta23.Density.fz X s - 1 =
          -(riemannZeta s * ∑' (n : ℕ), if X < n then ↑(ArithmeticFunction.moebius n) * ↑n ^ (-s) else 0)
```

Source of the text: `R11/audit.out`, line 1776 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement (`fz_sub_one_eq`): for $X\ge1$ and $\operatorname{Re}s>1$, $\zeta(s)M_X(s)-1=-\zeta(s)\sum_{n>X}\mu(n)n^{-s}$. (The hypothesis $X\ge1$ is not used: `V6/Zeta23/Density/StripDensity.lean`: "The hypothesis `hX` is kept for the statement shape; the identity does not use it.")

```lean
@Zeta23.Density.meanSquare_fz_window : ∀ {σ₁ σ : ℝ},
  1 / 2 < σ₁ →
    σ₁ < 1 →
      σ₁ ≤ σ →
        ∀ {N X : ℕ},
          1 ≤ X →
            X ≤ N →
              ∀ {a ℓ : ℝ},
                1 ≤ a →
                  0 ≤ ℓ →
                    ∀ {C_G : ℝ},
                      0 ≤ C_G →
                        (∀ t ∈ Set.Icc a (a + ℓ),
                            ‖riemannZeta (↑σ + ↑t * Complex.I) - BLClosure.S N (↑σ + ↑t * Complex.I) -
                                  ↑N ^ (1 - (↑σ + ↑t * Complex.I)) / (↑σ + ↑t * Complex.I - 1)‖ ≤
                              C_G * ↑N ^ (-σ)) →
                          ∀ {η : ℝ},
                            0 < η →
                              ∫ (t : ℝ) in a..a + ℓ, ‖Zeta23.Density.fz X (↑σ + ↑t * Complex.I)‖ ^ 2 ≤
                                (1 + η) *
                                    (ℓ * (1 + (2 + 1 / (2 * σ₁ - 1)) * (1 + Real.log ↑X) ^ 3 * ↑X ^ (1 - 2 * σ₁)) +
                                      26 * (2 + 2 / (2 - 2 * σ₁)) * (1 + Real.log ↑X) ^ 3 * ↑(N * X) ^ (2 - 2 * σ₁)) +
                                  (1 + 1 / η) *
                                    (2 * (1 + ↑X ^ (1 - σ₁) / (1 - σ₁)) ^ 2 *
                                      (↑N ^ (2 - 2 * σ₁) / a + C_G ^ 2 * ↑N ^ (-2 * σ₁) * ℓ))
```

Source of the text: `R11/audit.out`, line 1910 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement (`meanSquare_fz_window`): let $1/2<\sigma_1<1$, $\sigma\ge\sigma_1$, integers $1\le X\le N$, reals $a\ge1$, $\ell\ge0$, $C_G\ge0$, and suppose that for every $t\in[a,a+\ell]$, with $s=\sigma+it$, $\lvert\zeta(s)-\sum_{n\le N}n^{-s}-N^{1-s}/(s-1)\rvert\le C_GN^{-\sigma}$. Then for every $\eta>0$,
$$\int_a^{a+\ell}\lvert f_X(\sigma+it)\rvert^2dt\le(1+\eta)\Bigl(\ell\bigl(1+(2+\tfrac1{2\sigma_1-1})(1+\log X)^3X^{1-2\sigma_1}\bigr)+26(2+\tfrac2{2-2\sigma_1})(1+\log X)^3(NX)^{2-2\sigma_1}\Bigr)+(1+\tfrac1\eta)\cdot2\Bigl(1+\tfrac{X^{1-\sigma_1}}{1-\sigma_1}\Bigr)^2\Bigl(\tfrac{N^{2-2\sigma_1}}a+C_G^2N^{-2\sigma_1}\ell\Bigr).$$

```lean
@Zeta23.Density.count_le_meanSquare_fz : ∀ {σ₁ δ : ℝ},
  1 / 2 < σ₁ →
    σ₁ - 1 / 2 < δ →
      δ ≤ 1 / 2 →
        ∀ {X : ℕ},
          4 ≤ X →
            ∀ {ε : ℝ},
              0 < ε →
                ∀ {T : ℝ},
                  4 ≤ T →
                    ∀ {E : ℝ},
                      0 ≤ E →
                        (∀ (σ : ℝ),
                            σ₁ ≤ σ →
                              σ ≤ 2 →
                                ∀ (a : ℝ),
                                  3 / 2 ≤ a →
                                    a ≤ 9 / 2 →
                                      ∫ (t : ℝ) in a..a + T, ‖Zeta23.Density.fz X (↑σ + ↑t * Complex.I)‖ ^ 2 ≤
                                        T * (1 + E)) →
                          2 * Zeta23.BL.hwin σ₁ δ * Real.log (Zeta23.BL.Rout σ₁ / Zeta23.BL.rin σ₁ δ) *
                              (↑(Zeta23.BL.NRight δ T) - ↑(Zeta23.BL.NRight δ 4)) ≤
                            T * (1 / 2 * (ε ^ 2 + E) + Real.pi ^ 2 / ↑X)
```

Source of the text: `R11/audit.out`, line 2243 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement (`count_le_meanSquare_fz`): let $1/2<\sigma_1$, $\sigma_1-1/2<\delta\le1/2$, an integer $X\ge4$, $\varepsilon>0$, $T\ge4$, $E\ge0$, and suppose that for all $\sigma\in[\sigma_1,2]$ and all $a\in[3/2,9/2]$, $\int_a^{a+T}\lvert f_X(\sigma+it)\rvert^2dt\le T(1+E)$. Then
$$2\,h\,\log\frac{R}{r}\,\bigl(N(\tfrac12+\delta,T)-N(\tfrac12+\delta,4)\bigr)\le T\Bigl(\tfrac12(\varepsilon^2+E)+\frac{\pi^2}X\Bigr),$$
with $R=2-\sigma_1$ (`Rout`), $r=\tfrac12\bigl(R+\tfrac32-\delta\bigr)$ (`rin`), $h=\tfrac12\sqrt{r^2-(\tfrac32-\delta)^2}$ (`hwin`).

```lean
noncomputable def Rout (σ₁ : ℝ) : ℝ := 2 - σ₁
noncomputable def rin (σ₁ δ : ℝ) : ℝ := (Rout σ₁ + (3 / 2 - δ)) / 2
noncomputable def hwin (σ₁ δ : ℝ) : ℝ := Real.sqrt (rin σ₁ δ ^ 2 - (3 / 2 - δ) ^ 2) / 2
```

Source of the text: `V6/Zeta23/BL/BohrLandauPartial.lean`, lines 1238 to 1240.

```lean
@Zeta23.Density.density_single_window : ∀ {σ₁ δ : ℝ},
  1 / 2 < σ₁ →
    σ₁ - 1 / 2 < δ →
      δ ≤ 1 / 2 →
        ∃ C,
          ∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T ^ (1 - (2 * σ₁ - 1) ^ 2 / (2 * σ₁)) * (1 + Real.log T) ^ 3
```

Source of the text: `R11/audit.out`, line 2436 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement (`density_single_window`): for all real $\sigma_1,\delta$ with $1/2<\sigma_1$ and $\sigma_1-1/2<\delta\le1/2$ there is $C$ (depending on $\sigma_1$ and $\delta$) such that for all $T\ge2$
$$N(\tfrac12+\delta,T)\ \le\ C\,T^{\,1-\frac{(2\sigma_1-1)^2}{2\sigma_1}}\,(1+\log T)^3 .$$
Equivalently: for $1/2<\sigma_1<\sigma\le1$, $N(\sigma,T)\le C(\sigma_1,\sigma)\,T^{1-(2\sigma_1-1)^2/(2\sigma_1)}(1+\log T)^3$ for $T\ge2$. The hypotheses force $\sigma_1<1$. At $\sigma_1=3/4$ the exponent is $5/6$ (checked in the source: `V6/Zeta23/Density/StripDensity.lean`: "example : 1 - (2 * (3 / 4 : ℝ) - 1) ^ 2 / (2 * (3 / 4)) = 5 / 6 := by norm_num").

Remarks. A count, not a zero-free region: `V6/Zeta23/Density/StripDensity.lean`: "the result is a *count* of zeros off the line, strictly weaker than any zero-free strip, and not known to imply anything about one"; `V6/Zeta23/Density/StripDensity.lean`: "it is not evidence for the Riemann hypothesis". Weaker than Carlson: `V6/Zeta23/Density/StripDensity.lean`: "THE METHOD is Carlson's (1920), with a weaker exponent than Carlson's `4σ₁(1 − σ₁)`". The saving that the strict hypothesis allows: `V6/Zeta23/Density/StripDensity.lean`: "every saving below `4δ²/(1 + 2δ)` is attained and that value itself is not". The count is right-half only; the two-sided form over `NOff` (planned as `offLine_density`) is not in the module (`NOTES/DENSITY_LEDGER.md`: "by reflection the same holds on the left" is a remark of the ledger, not a claimed theorem).

### 4.14 The cube module: definitions (module `MNF/RH/Cube.lean`; first run 11)

```lean
/-- The mirror ρ ↦ 1 − ρ̄ of the functional-equation symmetry: the same imaginary part, the real
part reflected in 1/2.  (The same body as zeta23's `reflect`.) -/
def mirror (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- The critical line, Re ρ = 1/2. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- The open band of half-width Δ around the line, the line itself removed:
0 < |Re ρ − 1/2| < Δ. -/
def InBand (Δ : ℝ) (ρ : ℂ) : Prop := 0 < |ρ.re - 1 / 2| ∧ |ρ.re - 1 / 2| < Δ

/-- The reservoir at threshold Δ (this file's word for the points at distance ≥ Δ from the
line, see the header): |Re ρ − 1/2| ≥ Δ. -/
def InReservoir (Δ : ℝ) (ρ : ℂ) : Prop := Δ ≤ |ρ.re - 1 / 2|

/-- The nontrivial zeros within distance < Δ of the line (the line included). -/
def bandZeros (Δ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ |ρ.re - 1 / 2| < Δ}

/-- A nontrivial zero is degenerate if it is a multiple zero or shares its ordinate with another
nontrivial zero. -/
def Degenerate (ρ : ℂ) : Prop :=
  2 ≤ zeta_order ρ ∨ ∃ ρ' : ℂ, is_nontrivial_zero ρ' ∧ ρ' ≠ ρ ∧ ρ'.im = ρ.im

/-- No two distinct points of `S` share an imaginary part. -/
def OrdinatesInjectiveOn (S : Set ℂ) : Prop := ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ.im = ρ'.im → ρ = ρ'

/-- The pair measure of the window (0, T] applied to a test function: the sum over ordered pairs
of nontrivial zeros `(ρ, ρ')` with `0 < Im ≤ T`, weighted by both multiplicities, of
`f (Re ρ − 1/2) (Re ρ' − 1/2) (Im ρ − Im ρ')`. -/
noncomputable def pairSum (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, ∑ᶠ ρ' ∈ zerosIn 0 T,
    (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ) * f (ρ.re - 1 / 2) (ρ'.re - 1 / 2) (ρ.im - ρ'.im)

/-- The coincident mass: the pair measure of the pairs with equal ordinates (the atom at s = 0). -/
noncomputable def coincidentMass (T : ℝ) : ℝ := pairSum T (fun _ _ s => if s = 0 then 1 else 0)

/-- The diagonal mass Σ m(ρ)². -/
noncomputable def diagonalMass (T : ℝ) : ℝ := ∑ᶠ ρ ∈ zerosIn 0 T, (zeta_order ρ : ℝ) ^ 2

/-- The off-diagonal coincident mass: ordered pairs of distinct zeros with equal ordinates. -/
noncomputable def offDiagonalCoincidentMass (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T, ∑ᶠ ρ' ∈ zerosIn 0 T ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im},
    (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ)

/-- The band's coincident mass: ordered pairs of distinct zeros, both within distance < Δ of the
line, with equal ordinates. -/
noncomputable def bandCoincidentMass (Δ T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn 0 T ∩ bandZeros Δ,
    ∑ᶠ ρ' ∈ zerosIn 0 T ∩ bandZeros Δ ∩ {ρ' | ρ' ≠ ρ ∧ ρ'.im = ρ.im},
      (zeta_order ρ : ℝ) * (zeta_order ρ' : ℝ)
```

Source of the text: `V6/MNF/RH/Cube.lean`, lines 101 to 150.

In standard words: `mirror` is $\rho\mapsto1-\bar\rho$ (reflection in the critical line, same ordinate); `OnLine`: $\beta=1/2$; `InBand Δ`: $0<\lvert\beta-1/2\rvert<\Delta$; `InReservoir Δ`: $\lvert\beta-1/2\rvert\ge\Delta$; `bandZeros Δ`: the nontrivial zeros with $\lvert\beta-1/2\rvert<\Delta$ (the line included); `Degenerate ρ`: $m(\rho)\ge2$, or there is a nontrivial zero $\rho'\ne\rho$ with the same ordinate; `OrdinatesInjectiveOn S`: no two distinct points of $S$ have the same imaginary part; `pairSum T f` $=\sum_{\rho}\sum_{\rho'}m(\rho)m(\rho')\,f(\beta-\tfrac12,\beta'-\tfrac12,\gamma-\gamma')$ over ordered pairs of nontrivial zeros with $0<\gamma,\gamma'\le T$; `coincidentMass T`: the pair sum of the indicator of $\gamma=\gamma'$; `diagonalMass T` $=\sum m(\rho)^2$; `offDiagonalCoincidentMass T`: the sum of $m(\rho)m(\rho')$ over ordered pairs of distinct zeros with equal ordinates; `bandCoincidentMass Δ T`: the same with both zeros in `bandZeros Δ`. The words "cube", "reservoir" and "degenerate" are the author's (`V6/MNF/RH/Cube.lean`: "none of them is standard terminology").

### 4.15 `degenerate_of_not_onLine` and `noDegenerate_iff` (module `MNF/RH/Cube.lean`; first run 11)

```lean
@MNF.RH.degenerate_of_not_onLine : ∀ {ρ : ℂ}, MNF.RH.is_nontrivial_zero ρ → ¬MNF.RH.OnLine ρ → MNF.RH.Degenerate ρ
```

Source of the text: `R11/audit.out`, line 2457 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: a nontrivial zero with $\beta\ne1/2$ is degenerate (its partner is $1-\bar\rho$, a different zero with the same ordinate).

```lean
MNF.RH.noDegenerate_iff : (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ¬MNF.RH.Degenerate ρ) ↔
  (∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → MNF.RH.OnLine ρ) ∧ MNF.RH.AllZerosSimple
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 538 (Lean's `#check` output).

Plain statement: "no nontrivial zero is degenerate" holds if and only if "every nontrivial zero has $\beta=1/2$ and every nontrivial zero is simple" (`AllZerosSimple`: `V6/MNF/RH/Core.lean`: "def AllZerosSimple : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ = 1").

Remarks. An equivalence between two open statements; the left side is a restatement of "RH and all zeros simple". The statement writes RH in the strip form "every nontrivial zero has real part $1/2$"; that this is Mathlib's `RiemannHypothesis` is a theorem of step B2, not of this run (`V6/MNF/RH/Core.lean`: "theorem riemannHypothesis_iff_strip : RiemannHypothesis ↔ ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re = 1/2"). The record: `REPO/DEPOSIT_MAP.md`: "Relocates RH together with the simplicity conjecture; proves neither". The proof uses only the reflection symmetry of the zeros (with multiplicity) and elementary logic.

### 4.16 The three forms of the gap hypothesis (module `MNF/RH/Cube.lean`; first run 11)

```lean
MNF.RH.spectralGapHyp_iff_not_inBand : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ¬MNF.RH.InBand Δ ρ
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 540 (Lean's `#check` output).

```lean
MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ MNF.RH.OrdinatesInjectiveOn (MNF.RH.bandZeros Δ)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 542 (Lean's `#check` output).

```lean
MNF.RH.spectralGapHyp_iff_bandCoincidentMass : ∀ (Δ : ℝ),
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (T : ℝ), MNF.RH.bandCoincidentMass Δ T = 0
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 547 (Lean's `#check` output).

Plain statements, for every real $\Delta$ (no sign condition in the statements): (i) the gap hypothesis at $\Delta$ holds if and only if no nontrivial zero has $0<\lvert\beta-1/2\rvert<\Delta$; (ii) if and only if no two distinct nontrivial zeros with $\lvert\beta-1/2\rvert<\Delta$ have the same ordinate; (iii) if and only if for every real $T$ the sum of $m(\rho)m(\rho')$ over ordered pairs of distinct zeros with $0<\gamma=\gamma'\le T$ and both within distance $<\Delta$ of the line is $0$.

Remarks. Each is an equivalence with the open hypothesis: `V6/MNF/RH/Cube.lean`: "An equivalence, not a proof of either side: it relocates `SpectralGapHyp Δ`, which stays as open as before." (i) is the definition unfolded. (iii) needs that no nontrivial zero is real (4.17), because the sums only see windows $0<\gamma\le T$; negative ordinates are handled by complex conjugation (Mathlib's `riemannZeta_conj`).

### 4.17 No real zero in $(0,1)$ (module `MNF/RH/Cube.lean`; first run 11)

```lean
@MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo : ∀ {σ : ℝ}, 0 < σ → σ < 1 → riemannZeta ↑σ ≠ 0
```

Source of the text: `R11/audit.out`, line 2477 (Lean's `#check @` output; this statement has implicit binders, is printed with a leading `@`, and is therefore absent from the "What was proved" block of `R11/MNF_DENSITY.md`; it is in that report's axiom table).

Plain statement: for every real $\sigma$ with $0<\sigma<1$, $\zeta(\sigma)\ne0$.

```lean
MNF.RH.nontrivial_zero_im_ne_zero : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.im ≠ 0
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 546 (Lean's `#check` output).

Plain statement: every nontrivial zero has nonzero imaginary part.

Remarks. Classical and elementary: `REPO/DEPOSIT_MAP.md`: "Classical and elementary; a zero-free statement about the real segment only, not about the interior of the strip". What the record says about its availability at the pin: `V6/MNF/RH/Cube.lean`: "That classical fact was not on the tree, and we found no form of it in Mathlib at this pin (which has `riemannZeta_ne_zero_of_one_le_re` only); it is proved here." This is a statement about one pinned Mathlib commit and one tree, not about the Lean literature at large.

### 4.18 The pair sum and its marginals (module `MNF/RH/Cube.lean`; first run 11)

```lean
MNF.RH.pairSum_const : ∀ (T : ℝ), (MNF.RH.pairSum T fun x x_1 x_2 => 1) = ↑(MNF.RH.Ncount 0 T) ^ 2
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 553 (Lean's `#check` output).

```lean
MNF.RH.pairSum_fst : ∀ (T : ℝ) (g : ℝ → ℝ),
  (MNF.RH.pairSum T fun a x x_1 => g a) =
    ↑(MNF.RH.Ncount 0 T) * ∑ᶠ (ρ : ℂ) (_ : ρ ∈ MNF.RH.zerosIn 0 T), ↑(MNF.RH.zeta_order ρ) * g (ρ.re - 1 / 2)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 554 (Lean's `#check` output).

```lean
MNF.RH.pairSum_snd : ∀ (T : ℝ) (g : ℝ → ℝ),
  (MNF.RH.pairSum T fun x b x_1 => g b) =
    ↑(MNF.RH.Ncount 0 T) * ∑ᶠ (ρ : ℂ) (_ : ρ ∈ MNF.RH.zerosIn 0 T), ↑(MNF.RH.zeta_order ρ) * g (ρ.re - 1 / 2)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 557 (Lean's `#check` output).

```lean
MNF.RH.pairSum_fst_indicator : ∀ (T δ : ℝ),
  (MNF.RH.pairSum T fun a x x_1 => if δ ≤ |a| then 1 else 0) = ↑(MNF.RH.Ncount 0 T) * ↑(MNF.RH.NOff δ 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 560 (Lean's `#check` output).

```lean
MNF.RH.pairSum_fst_abs : ∀ (T : ℝ),
  (MNF.RH.pairSum T fun a x x_1 => |a|) = ↑(MNF.RH.Ncount 0 T) * MNF.RH.reservoirMass T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 562 (Lean's `#check` output).

```lean
MNF.RH.pairSum_fst_abs_eq_integral : ∀ (T : ℝ),
  (MNF.RH.pairSum T fun a x x_1 => |a|) = ↑(MNF.RH.Ncount 0 T) * ∫ (δ : ℝ) in 0..1 / 2, ↑(MNF.RH.NOff δ 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 564 (Lean's `#check` output).

```lean
MNF.RH.pairSum_swap : ∀ (T : ℝ) (f : ℝ → ℝ → ℝ → ℝ), MNF.RH.pairSum T f = MNF.RH.pairSum T fun a b s => f b a (-s)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 566 (Lean's `#check` output).

Plain statements, for every real $T$: the pair sum of the constant $1$ is $N(T)^2$; for $g:\mathbb R\to\mathbb R$ the pair sum of $g$ of the first (or second) shifted real part is $N(T)\sum_{0<\gamma\le T}m(\rho)g(\beta-\tfrac12)$; with $g=\mathbf 1[\lvert a\rvert\ge\delta]$ this is $N(T)\,N_{\mathrm{off}}(\delta,T)$; with $g=\lvert a\rvert$ it is $N(T)\,D(T)=N(T)\int_0^{1/2}N_{\mathrm{off}}(\delta,T)\,d\delta$; exchanging the two zeros replaces $f(a,b,s)$ by $f(b,a,-s)$. All are rearrangements of finite sums. Also claimed: `pairSum_nonneg`, `pairSum_mono`, `diagonalMass_nonneg`, `diagonalMass_le_sq_Ncount` ($\sum m(\rho)^2\le N(T)^2$), `Ncount_le_diagonalMass` ($N(T)\le\sum m(\rho)^2$), `Ncount_eq_N0_add_NOffLine`.

### 4.19 The coincident mass (module `MNF/RH/Cube.lean`; first run 11)

```lean
MNF.RH.coincidentMass_eq : ∀ (T : ℝ),
  MNF.RH.coincidentMass T = MNF.RH.diagonalMass T + MNF.RH.offDiagonalCoincidentMass T
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 573 (Lean's `#check` output).

Plain statement: for every real $T$, the sum of $m(\rho)m(\rho')$ over ordered pairs with $0<\gamma=\gamma'\le T$ equals $\sum_{0<\gamma\le T}m(\rho)^2$ plus the same sum restricted to $\rho'\ne\rho$.

```lean
MNF.RH.offDiagonalCoincidentMass_le : ∀ (T : ℝ),
  MNF.RH.offDiagonalCoincidentMass T ≤
    ↑(MNF.RH.NOffLine 0 T) * ↑(MNF.RH.Ncount 0 T) + ↑(MNF.RH.N0 0 T) * ↑(MNF.RH.NOffLine 0 T)
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 579 (Lean's `#check` output).

Plain statement: for every real $T$, with $O(T)$ the sum of $m(\rho)m(\rho')$ over ordered pairs of distinct zeros with $0<\gamma=\gamma'\le T$, and $N_{\ne}(T)$ the count of zeros with $\beta\ne1/2$: $O(T)\le N_{\ne}(T)\,N(T)+N_0(T)\,N_{\ne}(T)$.

```lean
MNF.RH.offDiagonalCoincidentMass_le_five_ninths : ∀ ε > 0,
  ∃ T₀, ∀ T ≥ T₀, MNF.RH.offDiagonalCoincidentMass T ≤ (5 / 9 + ε) * ↑(MNF.RH.Ncount 0 T) ^ 2
```

Source of the text: `R11/MNF_DENSITY.md`, block "What was proved", line 590 (Lean's `#check` output).

Plain statement: for every $\varepsilon>0$ there is $T_0$ such that $O(T)\le(5/9+\varepsilon)\,N(T)^2$ for all $T\ge T_0$.

Remarks. The eventual bound uses the one-third theorem of 4.2 (zeta23's) and the identity $N=N_0+N_{\ne}$; the arithmetic is $\tfrac13\cdot1+\tfrac23\cdot\tfrac13=\tfrac59$ (`V6/MNF/RH/Cube.lean`: "Read termwise the same arithmetic is `(1/3)·1 + (2/3)·(1/3) = 5/9`"). Companions claimed in the module: `offLine_sq_le_offDiagonalCoincidentMass` ($\sum_{\beta\ne1/2}m(\rho)^2\le O(T)$), `offDiagonalCoincidentMass_le_two_mul` ($O(T)\le2N_{\ne}(T)N(T)$), `offDiagonalCoincidentMass_le_two_thirds`, `offDiagonalCoincidentMass_eq_zero_of_onLine`, `onLine_of_offDiagonalCoincidentMass_eq_zero` (positive ordinates only), `bandCoincidentMass_le_offDiagonalCoincidentMass`. None of these says anything about pair correlation: `V6/MNF/RH/Cube.lean`: "it is NOT a theorem, nothing here proves or assumes it" (of the cubic small-distance law).

## 5. Proof architecture

What follows describes the Lean proofs as they stand in `V6`, with the plans cited where they explain a choice. "The tree" means the zeta23 checkout (Anthropic's `formal-math/zeta23`, receipted in run 2); a name said to be "the tree's" is a theorem of that library, used and not re-proved here.

### 5a. Bohr-Landau as formalized

Route. Jensen's formula on discs, not Littlewood's lemma: `NOTES/plan/BOHR_LANDAU_PLAN.md`: "**Route B (Jensen on discs centred `2 + t*I`, averaged in `t`), not route A (Littlewood).** Littlewood's lemma is in neither Mathlib nor the tree". The proof has two independent halves, a mean square of $\zeta$ and a zero count from Jensen's formula (`NOTES/plan/BOHR_LANDAU_PLAN.md`: "Two independent halves: **M** (mean square; analysis of Dirichlet polynomials) and **J** (Jensen/covering; complex analysis + measure theory)."), and was reached in two steps: $\delta>1/6$ in run 8, every $\delta>0$ in run 9.

Step 1, the reflection to the left half (supplied file `Zeta23/BohrLandau.lean`, sorry-free part; restated in the claim set in `MNF/RH/Density.lean`). For $\delta>0$, $N_{\mathrm{off}}(\delta,T)$ is the sum of the right-half and left-half counts (`NOff_eq_right_add_left`); the map $\rho\mapsto1-\bar\rho$ (zeta23's `reflect`) preserves the ordinate and the multiplicity and exchanges the halves, so the two counts are equal (`NLeft_eq_NRight`); hence a right-half bound with constant $C$ gives `BohrLandau` with constant $2C$ (`bohrLandau_of_right`). Evidence: `V6/Zeta23/BohrLandau.lean`: "reduction to the right half: ρ ↦ 1 − ρ̄ (zeta23's `reflect`) preserves Im, multiplicity."; `V6/Zeta23/BohrLandau.lean`: "exact (zetaZeroConfig.mult_reflect ρ hz).symm"; `V6/Zeta23/BohrLandau.lean`: "refine ⟨2 * C, fun T hT => ?_⟩". The claimed restatements delegate: `V6/MNF/RH/Density.lean`: "theorem bohrLandau_of_right (h : RightHalfBound) : BohrLandau := Zeta23.BL.bohrLandau_of_right h".

Step 2, the zero count from Jensen's formula (`Zeta23/BL/BohrLandauPartial.lean`, blocks J023, J45, J67, J89). Fix $1/2<\sigma_1<1$ and $\sigma_1-1/2<\delta\le1/2$.

- Geometry. Discs centred $2+it$, $t\ge3$, outer radius $R=2-\sigma_1$, inner radius $r=\tfrac12(R+\tfrac32-\delta)$, half-window $h=\tfrac12\sqrt{r^2-(\tfrac32-\delta)^2}$ (definitions quoted in 4.13). `geom_facts`: $0<r<R<\tfrac32$, $0<h\le1$, and every $\rho$ with $\tfrac12+\delta\le\beta<1$ lies in the closed inner disc centred $2+it$ whenever $\lvert t-\gamma\rvert\le h$. The outer disc lies in $\operatorname{Re}s\ge\sigma_1$ and does not contain the pole. Evidence: `V6/Zeta23/BL/BohrLandauPartial.lean`: "0 < rin σ₁ δ ∧ rin σ₁ δ < Rout σ₁ ∧ Rout σ₁ < 3 / 2 ∧ 0 < hwin σ₁ δ ∧ hwin σ₁ δ ≤ 1 ∧ ∀ ρ : ℂ, 1 / 2 + δ ≤ ρ.re → ρ.re < 1 → ∀ t : ℝ, |t - ρ.im| ≤ hwin σ₁ δ → ρ ∈ closedBall (2 + t * I) (rin σ₁ δ)".
- Jensen at one $t$. The disc inequality of 4.5 applied to $\zeta$ (`count_disc_le`), with the centre value controlled by the tree's lower bound $\lvert\zeta(2+it)\rvert\ge1/3$: `V6/Zeta23/BL/BohrLandauPartial.lean`: "`-log ‖ζ(2 + t I)‖ ≤ log 3`, from `zeta_lower_bound_two`". The zeros of $\zeta$ counted by `zeta_order` are dominated by the divisor of $\zeta$ on the disc (`finset_sum_zeta_order_le_finsum_divisor`).
- The majorant. $\log\lvert\zeta\rvert\le L(z):=\tfrac12\log(1+\lvert\zeta(z)\rvert^2)$, continuous and nonnegative (`V6/Zeta23/BL/BohrLandauPartial.lean`: "noncomputable def Lz (z : ℂ) : ℝ := (1 / 2) * Real.log (1 + ‖riemannZeta z‖ ^ 2)").
- Averaging in $t$ (`count_le_integral`). Each zero with $\beta\ge\tfrac12+\delta$, $4<\gamma\le T$ lies in the inner disc for all $t$ in a window of length $2h$ inside $[3,T+3]$; integrating the per-$t$ inequality over $t\in[3,T+3]$ gives $2h\log(R/r)\,(N(\tfrac12+\delta,T)-N(\tfrac12+\delta,4))\le\int_3^{T+3}(\text{circle average of }L\text{ at }2+it,\text{ radius }R)\,dt+T\log3$. Evidence: `V6/Zeta23/BL/BohrLandauPartial.lean`: "2 * hwin σ₁ δ * Real.log (Rout σ₁ / rin σ₁ δ) * ((NRight δ T : ℝ) - NRight δ 4) ≤ ∫ t in (3:ℝ)..(T + 3), (circleAverage Lz (2 + t * I) (Rout σ₁) + Real.log 3)".
- Fubini and the mean square (`integral_circleAverage_Lz_eq_swap`, `integral_Lz_circle_le`). The $t$-integral of the circle averages is the $\theta$-average of integrals along vertical segments $\operatorname{Re}s=2+R\cos\theta\in[\sigma_1,2+R]$; on each, $L\le\tfrac12\lvert\zeta\rvert^2$ and the uniform mean-square hypothesis gives $\le\tfrac12C(T+5)$. Evidence: `V6/Zeta23/BL/BohrLandauPartial.lean`: "the integral of `Lz` is an integral along the vertical segment `Re s = 2 + Rout σ₁ cos θ` (which lies in `[σ₁, 2 + Rout σ₁]`), enlarged to `u ∈ [1, T + 5]`, and bounded via `Lz ≤ (1/2)‖ζ‖²` by the uniform mean square `hMS`".
- Assembly (`count_le_meanSquare'`, `rightHalf_of_meanSquareUnif`). With $K=2h\log(R/r)$: $K\,(N(\tfrac12+\delta,T)-N(\tfrac12+\delta,4))\le\tfrac12C(T+5)+T\log3$ for $T\ge4$; for $2\le T<4$ monotonicity; for $\delta\ge1/2$ the count is $0$. Result: for $1/2<\sigma_1<1$, a uniform mean square on $\operatorname{Re}s\ge\sigma_1$ gives $N(\tfrac12+\delta,T)\le C'T$ for every $\delta>\sigma_1-1/2$. The constant in the proof: `V6/Zeta23/BL/BohrLandauPartial.lean`: "`C = NRight δ 4 / 2 + ((9/8) max C₀ 0 + log 3) / K`, `C₀` the constant of `hms`, with `K = 2 hwin σ₁ δ · log (Rout σ₁ / rin σ₁ δ)`". The hypothesis is the proposition `V6/Zeta23/BL/BohrLandauPartial.lean`: "def MeanSquareUnifFrom (σ₁ : ℝ) : Prop := ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ T : ℝ, 2 ≤ T → ∫ t in (1:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T".

Step 3, the mean square for $\sigma_1\ge2/3$ (run 8; blocks M1, M2, M3a, M3 of `BohrLandauPartial.lean`).

- The Dirichlet-polynomial mean value in Montgomery-Vaughan form, `M1.dirichlet_meanSquare_le`: $\int_0^T\lvert\sum_{n\le N}a_nn^{-it}\rvert^2dt\le T\sum\lvert a_n\rvert^2+26\sum(n+1)\lvert a_n\rvert^2$. The constant is $2\cdot13$, the $13$ coming from the tree's weighted Hilbert inequality with frequencies $\log n$ and gaps $1/(n+1)$: `V6/Zeta23/BL/BohrLandauPartial.lean`: "**M1d. Dirichlet-polynomial mean value, Montgomery–Vaughan form** (constant 26 = 2·13)"; `V6/Zeta23/BL/BohrLandauPartial.lean`: "The weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen` on the index set `Icc 1 N` with frequencies `log n` and gaps `1/(n+1)`." The inequality `mvDiag_thirteen` is the tree's, not this work's.
- The approximate formula as the tree gives it, `M2.zeta_eq_four_terms`, from the tree's `Zeta0EqZeta`: for $\sigma>0$, $t\ne0$, $N\ge1$, $\zeta(s)=\sum_{n\le N}n^{-s}-\frac{N^{1-s}}{1-s}-\frac{N^{-s}}2+s\int_N^\infty\frac{\lfloor x\rfloor+\frac12-x}{x^{s+1}}dx$. Evidence: `V6/Zeta23/BL/BohrLandauPartial.lean`: "The tree's `Zeta0EqZeta` unfolded: on `Re s = σ > 0`, `t ≠ 0`, `N ≥ 1`, `ζ(s) = S_N(s) + P + Q + R`." The last term is bounded naively by $(\sigma+t)N^{-\sigma_1}/\sigma_1$ (`zeta_sub_sum_le`).
- The choice $N=\lfloor T^{3/2}\rfloor+1$ (`N_choice`) and the explicit constant of 4.6. Why $2/3$: `V6/MNF/RH/DensityPartial.lean`: "the exponent count (N = T^a needs 1/σ ≤ a ≤ 1/(2 − 2σ), a window that is non-empty exactly when σ ≥ 2/3; the proof takes a = 3/2) closes the mean square for σ ≥ 2/3 and not below".
- Result of run 8: `rightHalf_gt_sixth` and `bohrLandau_gt_sixth`, taking $\sigma_1=\tfrac12(\tfrac23+\tfrac12+\delta)$ in step 2 (`V6/Zeta23/BL/BohrLandauPartial.lean`: "For δ < 1/2 take `σ₁ := (2/3 + (1/2 + δ))/2 ∈ (2/3, 1/2 + δ)` in J8 with M3's `meanSquareUnif_naive`").

Step 4, the sharp approximate formula (run 9; `Zeta23/BL/BohrLandauClosure.lean`, steps lettered as in the file header).

- D, one Euler-Maclaurin step from the tree's `Zeta0EqZeta` (`zeta_eq_euler_maclaurin`): for $\operatorname{Re}s>0$, $s\ne1$, $N\ge1$, $\zeta(s)=\sum_{n\le N}n^{-s}+\frac{N^{1-s}}{s-1}-\frac{N^{-s}}2-s\int_N^\infty\psi(u)u^{-s-1}du$ with $\psi(u)=\{u\}-\tfrac12$. Evidence: `V6/Zeta23/BL/BohrLandauClosure.lean`: "ζ(s) = S_N(s) + N^{1−s}/(s − 1) − N^{−s}/2 − s ∫_N^∞ ψ(u) u^{−s−1} du."; `V6/Zeta23/BL/BohrLandauClosure.lean`: "rw [← Zeta0EqZeta (N := N) (by omega) hs hs1, riemannZeta0]".
- E, a second integration by parts (`tail_by_parts`): $\int_N^\infty\psi(u)u^{-s-1}du=(s+1)\int_N^\infty P(u)u^{-s-2}du$, where $P=(B_2(\{u\})-\tfrac16)/2$ is the continuous periodic antiderivative of $\psi$ with $P(n)=0$ (`V6/Zeta23/BL/BohrLandauClosure.lean`: "P = (B₂per − 1/6)/2, the continuous periodic antiderivative of ψ with P(n) = 0").
- B, the Fourier series of the second Bernoulli function (`B2per_fourier`, `P_fourier`): $B_2(\{u\})=\sum_{\nu\ge1}\frac{\cos(2\pi\nu u)}{\pi^2\nu^2}$, from Mathlib (`V6/Zeta23/BL/BohrLandauClosure.lean`: "Mathlib's `hasSum_one_div_nat_pow_mul_cos` with k = 1, unfolded"); hence $P(u)+\tfrac1{12}=\sum_{\nu\ge1}\frac{\cos(2\pi\nu u)}{2\pi^2\nu^2}$.
- A, the first-derivative test in smooth form (`first_derivative_test_amp_smooth'`, `first_derivative_test_amp_smooth`, `first_derivative_test_smooth`): for a twice differentiable phase $F$ with $F'\ge\lambda>0$ on $[a,b]$ and $F''$ continuous, and a continuously differentiable amplitude $G\ge0$ with $G'F'-GF''\le0$ (that is, $G/F'$ nonincreasing), $\lvert\int_a^bG(x)e^{iF(x)}dx\rvert\le4G(a)/\lambda$. Evidence: `V6/Zeta23/BL/BohrLandauClosure.lean`: "**First-derivative test with a nonnegative amplitude**, smooth form (Titchmarsh Lemma 4.3 with m = lam/G(a))"; the constant: `V6/Zeta23/BL/BohrLandauClosure.lean`: "(The proof gives the sharper `2 G(a) / lam`; `4` is Titchmarsh's constant, kept so the three tests have his shape.)" It was written here because the plan found none in Mathlib (`NOTES/plan/BOHR_LANDAU_PLAN.md`: "a first-derivative test for oscillatory integrals (not in Mathlib)").
- C, one Fourier mode of the tail (`tail_mode_bound'`): for $\sigma>0$, $x\ge1$, $t\le\pi x$, $\nu\ge1$, $\lvert\int_x^\infty e^{2\pi i\nu u}u^{-\sigma-it-2}du\rvert\le\frac8{\pi\nu}x^{-\sigma-2}$, by the test of A with $F(u)=2\pi\nu u-t\log u$, $G(u)=u^{-\sigma-2}$ (`V6/Zeta23/BL/BohrLandauClosure.lean`: "the first-derivative test applied on [x, X] to F(u) = 2πνu − t log u, G(u) = u^{−σ−2}"). This is where $N\ge t$ enters: $t\le N$ gives $t\le\pi N$, so $F'\ge\pi\nu$.
- F, the sharp tail (`tail_sharp`): summing the modes (dominated convergence, `hasSum_mode_integrals`; the $\nu$-th mode contributes $O(\nu^{-3})$) and using $\lvert s\rvert\lvert s+1\rvert\le12N^2$, $\lvert s\int_N^\infty\psi(u)u^{-s-1}du\rvert\le C(\sigma_0)N^{-\sigma}$ for $\sigma_0\le\sigma\le2$, $0\le t\le N$. Evidence: `V6/Zeta23/BL/BohrLandauClosure.lean`: "compare the naive bound ‖s‖ N^{−σ}/σ from the tree's `ZetaBnd_aux1b`".
- G, `zeta_approx_sharp` (4.7) from D and F.

Step 5, the mean square for every $\sigma_1>1/2$ and the closure (run 9; step I of the same file). With $N=\lceil T\rceil$ every $t\in[1,T]$ has $t\le N$, so G applies on the whole segment (`zeta_approx_sharp_segment`). Pointwise $\lvert\zeta\rvert^2\le4\lvert S_N\rvert^2+4N^{2-2\sigma_1}/t^2+4C^2$ (`norm_zeta_sq_le_sharp`), the Montgomery-Vaughan mean value of step 3 for $S_N$, and $N\le2T$ give, for $1/2<\sigma_1<1$ and $\sigma_1\le\sigma\le2$, $\int_1^T\lvert\zeta(\sigma+it)\rvert^2dt\le CT$ with the constant of `V6/Zeta23/BL/BohrLandauClosure.lean`: "explicitly `C = 4(1 + 1/(2σ₁−1)) + 112 + 416/(2−2σ₁) + 4 C_G²`"; $\sigma>2$ by the trivial bound (`meanSquare_hyp_extend`); all $\sigma_1>1/2$ by applying the result at $\min(\sigma_1,3/4)$. Then `rightHalf_all` takes $\sigma_1=\tfrac12+\tfrac\delta2$ in step 2 (`V6/Zeta23/BL/BohrLandauClosure.lean`: "`σ₁ := 1/2 + δ/2 ∈ (1/2, 3/4)` and `BLClosure.meanSquareUnifFrom_all`") and `bohrLandau_full` is step 1 applied to it (`V6/Zeta23/BL/BohrLandauClosure.lean`: "theorem bohrLandau_full : MNF.RH.BohrLandau := bohrLandau_of_right rightHalfBound").

What the tree supplied and what this layer added, in the record's words: `NOTES/plan/BOHR_LANDAU_PARTIAL.md`: "formalized from scratch on top of the tree's approximate formula `Zeta0EqZeta` (PNT+ port), the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen`, Mathlib's Jensen formula, and `zeta_lower_bound_two`".

### 5b. The zero-density estimate

Target and method: Carlson's method with one approximate formula on one window (`V6/Zeta23/Density/StripDensity.lean`: "One approximate formula of length `N ≈ T` is used on the single window `[3, T + 3]`; this is what costs the exponent (Carlson's `4σ₁(1 − σ₁)` needs `N ≈ t` dyadically — not proved here)."). The plan had 16 nodes in five stages (`NOTES/DENSITY_LEDGER.md`: "The plan is a DAG of 16 nodes in five stages (the one new piece of mathematics is the divisor-sum bound Σ_{m≤Y} d_X(m)² ≤ Y·(1 + log X)³)"). The words "new piece of mathematics" in that quote mean new to the tree; the divisor bound is elementary and the paper must not present it as a new result. Fix $1/2<\sigma_1<1$ and $\sigma_1-1/2<\delta\le1/2$.

1. The mollifier and the centre. $f_X=\zeta M_X$. For $\operatorname{Re}s>1$, $f_X-1=-\zeta\sum_{n>X}\mu(n)n^{-s}$ (4.13), through Mathlib's identity for $\zeta\cdot L(\mu)$ (`NOTES/DENSITY_LEDGER.md`: "the Möbius identity ζ·M_X − 1 = −ζ·Σ_{n>X} μ(n)n^{−s} through Mathlib's `LSeries_zeta_mul_Lseries_moebius`"); hence $\lvert f_X(s)-1\rvert\le\frac{\pi^2}{6X}$ for $\operatorname{Re}s\ge2$, $\lvert f_X(2+it)\rvert\ge\tfrac12$ and $-\log\lvert f_X(2+it)\rvert\le\frac{\pi^2}{3X}$ for $X\ge4$. Evidence: `V6/Zeta23/Density/StripDensity.lean`: "For `Re s ≥ 2`, `‖fz X s − 1‖ ≤ (π²/6)·(1/X)`"; `V6/Zeta23/Density/StripDensity.lean`: "`−log ‖fz X (2 + it)‖ ≤ π²/(3X)` for `X ≥ 4`". This replaces the term $T\log3$ of 5a, which is of order $T$, by $T\pi^2/(3X)$.
2. Zeros of $\zeta$ are zeros of $f_X$ with at least the same order (`zeta_order_le_divisor_fz`; $M_X$ is entire and not identically zero, `Mx_ne_zero_of_le_re` for $\operatorname{Re}s\ge3$), so Jensen's inequality for $f_X$ on the discs of 5a counts the zeros of $\zeta$ (`count_disc_le_fz`, `count_window_le_fz`).
3. The product polynomial and the divisor bound. $S_N(s)M_X(s)=\sum_{m\le NX}c_m\,m^{-s}$ (`S_mul_Mx_eq`), with $\lvert c_m\rvert\le d_X(m)$ (`abs_cm_le`) and $c_m=[m=1]$ for $m\le X\le N$ (`cm_eq_of_le`). The divisor bound $\sum_{m\le Y}d_X(m)^2\le Y(1+\log X)^3$ (`sum_dX_sq_le`) is proved by counting common multiples: the number of $m\le Y$ divisible by $d_1$ and $d_2$ is at most $Y\gcd(d_1,d_2)/(d_1d_2)$ (`card_filter_dvd_dvd_le`), $\gcd(d_1,d_2)\le\sum_{g\mid d_1,\,g\mid d_2}g$ (`gcd_le_sum_dvd`), and $\sum_{d\le X,\ g\mid d}1/d\le\frac1g(1+\log X)$ (`sum_div_of_dvd_le`), giving $\sum_{d_1,d_2\le X}\gcd(d_1,d_2)/(d_1d_2)\le(1+\log X)^3$ (`sum_gcd_div_le`). Evidence: `V6/Zeta23/Density/StripDensity.lean`: "The number of `m ∈ [1, Y]` divisible by both `d₁` and `d₂` is at most `Y · gcd(d₁,d₂) / (d₁ d₂)` (it equals `⌊Y / lcm(d₁,d₂)⌋`)."; `V6/Zeta23/Density/StripDensity.lean`: "`∑_{m ≤ Y} dX(X,m)² ≤ Y (1 + log X)³`. The logarithm is in `X`, not `Y`." Partial summation with generic weights (`sum_mul_le_of_partial_sums`, `tail_sum_le`, `weight_sum_le`) turns it into bounds for $\sum_{m>X}d_X(m)^2m^{-2\sigma}$ and $\sum_{m\le M}(m+1)d_X(m)^2m^{-2\sigma}$.
4. The window mean square. Product polynomial (`meanSquare_prodPoly`, by the Montgomery-Vaughan inequality of 5a): $\int_a^{a+\ell}\lvert S_NM_X\rvert^2\le\ell\bigl(1+(2+\tfrac1{2\sigma_1-1})(1+\log X)^3X^{1-2\sigma_1}\bigr)+26(2+\tfrac2{2-2\sigma_1})(1+\log X)^3(NX)^{2-2\sigma_1}$; the leading $1$ is the coefficient $c_1$ (`V6/Zeta23/Density/StripDensity.lean`: "the diagonal is `ℓ · (1 + o(1))` as `X → ∞` (the `1` is the coefficient of `m = 1`; all other coefficients `m ≤ X` vanish), the off-diagonal is the Montgomery–Vaughan term"). Remainder (`meanSquare_B_window`): $\lvert M_X\rvert\le1+\frac{X^{1-\sigma_1}}{1-\sigma_1}$, the main term $N^{1-s}/(s-1)$ of size $N^{1-\sigma_1}/t$, and the sharp error $C_GN^{-\sigma}$ of 4.7. The two are combined with a free weight, $\lvert u+v\rvert^2\le(1+\eta)\lvert u\rvert^2+(1+\tfrac1\eta)\lvert v\rvert^2$ (`norm_add_sq_le_eta`), which is `meanSquare_fz_window` (4.13).
5. The $\varepsilon$-majorant. In place of $\tfrac12\log(1+\lvert\zeta\rvert^2)$, the function $L_\varepsilon(f)=\tfrac12\log(\varepsilon^2+\lvert f\rvert^2)$; the reason: `V6/Zeta23/Density/StripDensity.lean`: "ε-majorant of `log ‖f‖` (replaces the tree's `Lz`, whose `1 +` kills every saving)". Jensen's inequality for the concave function $x\mapsto\tfrac12\log(\varepsilon^2+x)$ on the segment average (`segment_average_Leps_le`), then $\tfrac12\log(\varepsilon^2+1+E)\le\tfrac12(\varepsilon^2+E)$ (`half_log_le_half`). The source marks this as the step where the earlier proof lost the saving: `V6/Zeta23/Density/StripDensity.lean`: "This is the step at which the tree's Bohr–Landau proof (`Lz_le_half_sq`, `BohrLandauPartial.lean:1663`) threw the logarithm away." With Fubini as in 5a this gives `count_le_meanSquare_fz` (4.13): $K\,(N(\tfrac12+\delta,T)-N(\tfrac12+\delta,4))\le T\bigl(\tfrac12(\varepsilon^2+E)+\pi^2/X\bigr)$.
6. Exponent arithmetic (`exponent_single`). Parameters $X=\lfloor T^{\theta}\rfloor$, $N=\lceil T\rceil+5$, $\eta=E_0$, $\varepsilon^2=1/X$, with $\theta=\frac{2\sigma_1-1}{2\sigma_1}$ and $\kappa=\frac{(2\sigma_1-1)^2}{2\sigma_1}$. Evidence: `V6/Zeta23/Density/StripDensity.lean`: "The parameters `X = ⌊T^θ⌋₊`, `N = ⌈T⌉₊ + 5` for `T ≥ T₀ := max 8 (4^{1/θ})`: `4 ≤ X ≤ N`, `T^θ/2 ≤ X ≤ T^θ`, `T ≤ N ≤ 2T`."; `V6/Zeta23/Density/StripDensity.lean`: "The full error term of the count-to-mean-square bound at `η = E₀`, `ε² = 1/X`". The exponent identities: `V6/Zeta23/Density/StripDensity.lean`: "`(2 − 2σ₁) + θ (2 − 2σ₁) − 1 = −2κ` (the off-diagonal exponent)" and `V6/Zeta23/Density/StripDensity.lean`: "`κ + θ (2 − 2σ₁) + (1 − 2σ₁) = −κ` (the cross-term exponent: the balance)". Result: the error term is $\le K(1+\log T)^3T^{-\kappa}$ for $T\ge T_0$.
7. The geometric factor (`geom_lower`): $2h\log(R/r)\ge\Delta^{3/2}/3$ with $\Delta=\delta-(\sigma_1-\tfrac12)>0$.
8. Assembly (`count_le_Egen`, `density_single_window`): for $T\ge T_0$ divide by the geometric factor; for $2\le T<T_0$ monotonicity. The constant: `V6/Zeta23/Density/StripDensity.lean`: "Constant: `C = NRight δ T₀ + K / (2 hwin σ₁ δ · log (Rout σ₁ / rin σ₁ δ))`."

Why the exponent is weaker than Carlson's. The plan's account: `NOTES/strip/STRIP_PLAN.md`: "the balance diagonal `T·X^{1−2σ₁}` vs off-diagonal `(TX)^{2−2σ₁}` vs centre `T/X` gives Carlson's `4σ₁(1−σ₁)` at X = T^{2σ₁−1} *only* with N ≈ t per dyadic window; with one N ≈ T the main term N^{1−s}/(s−1)·M_X is large at small t, the cross term costs the factor `X^{1−σ₁}T^{−(2σ₁−1)/2}`, and the balance moves to X = T^{(2σ₁−1)/(2σ₁)}, exponent `1 − (2σ₁−1)²/(2σ₁)`". Arithmetic done for this sheet (not a quote): Carlson's exponent is $4\sigma_1(1-\sigma_1)=1-(2\sigma_1-1)^2$, so Carlson's saving is $(2\sigma_1-1)^2$ and the saving here is $(2\sigma_1-1)^2/(2\sigma_1)$, smaller by the factor $1/(2\sigma_1)\in(\tfrac12,1)$; at $\sigma_1=3/4$ the exponents are $3/4$ (Carlson) and $5/6$ (here). The dyadic version was a stretch target and was not done (`NOTES/strip/STRIP_PLAN.md`: "**Stretch target (Stage 5, same lemma chain re-parametrized dyadically): Carlson's theorem.**"; `NOTES/DENSITY_LEDGER.md`: "weaker than Carlson's 4σ₁(1 − σ₁) (which needs the dyadic windows of Stage 5, not done)"); the names `carlson_density` and `offLine_density` of the plan do not occur in `V6/Zeta23/Density/StripDensity.lean` (searched). A linear saving is out of reach of the route: `V6/Zeta23/Density/StripDensity.lean`: "A linear saving `1 − c(σ₁ − 1/2)` (Ingham) is out of reach of this route (it needs a fourth moment not on the tree)."

### 5c. The displacement bound

1. Layer cake (`reservoirMass_eq_integral`). Write $N_{\mathrm{off}}(\delta,T)=\sum_\rho m(\rho)\mathbf 1[\delta\le\lvert\beta-\tfrac12\rvert]$, exchange the finite sum and the integral over $\delta\in[0,\tfrac12]$, and use $\int_0^{1/2}\mathbf 1[\delta\le a]\,d\delta=a$ for $0\le a\le\tfrac12$ (every nontrivial zero has $\lvert\beta-\tfrac12\rvert<\tfrac12$). Evidence: `V6/MNF/RH/ReservoirMass.lean`: "interchange the Finset sum and the interval integral (`intervalIntegral.integral_finsetSum`, each term integrable by §4.3), and evaluate each `∫₀^{1/2} 1[δ ≤ |Re ρ − 1/2|] dδ = |Re ρ − 1/2|`".
2. The split. $\delta\mapsto N_{\mathrm{off}}(\delta,T)$ is antitone, so for $0\le\delta_0\le\tfrac12$: $\int_0^{\delta_0}\le\delta_0N(T)$ and $\int_{\delta_0}^{1/2}$ is bounded by the tail of any majorant (`integral_NOff_split`, `integral_NOff_le_mul_Ncount`).
3. The explicit constant (`NRight_explicit`, `bohrLandau_explicit`). Run the Jensen argument of 5a at $\sigma_1=\tfrac12+\tfrac\delta2$ with the mean-square constant made explicit in $\sigma_1$: $\int_1^T\lvert\zeta(\sigma+it)\rvert^2dt\le(\tfrac4\delta+B_{\mathrm{ms}})T$ for $\sigma\ge\tfrac12+\tfrac\delta2$ (`meanSquareUnifFrom_explicit`), and the geometric factor $K=2h\log(R/r)\ge\delta^{3/2}/12$ (`K_half_ge`, from $h\ge\sqrt\delta/4$ and $\log(R/r)\ge\delta/6$). The $\delta^{-1}$ of the mean square times the $\delta^{-3/2}$ of the geometry is the exponent $-5/2$. Evidence: `V6/MNF/RH/ReservoirMass.lean`: "by running the tree's Jensen-window argument (`count_le_meanSquare'`) at σ₁ = 1/2 + δ/2, where hwin ≥ √δ/4 and log(Rout/rin) ≥ δ/6"; `V6/MNF/RH/ReservoirMass.lean`: "`∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ (4/δ + meanSquareB) T` for all `σ ≥ 1/2 + δ/2`, `T ≥ 2`"; `V6/MNF/RH/ReservoirMass.lean`: "`K ≥ δ√δ/12`".
4. The upper and lower bounds for $N(T)$ of order $T\log T$, from the `local_count` and `main` fields of the tree's `riemannVonMangoldt_zeta`: $N(T)\le C\,T\log T$ for $T\ge3$ and $N(T)\ge\frac{T\log T}{16\pi}$ for $T\ge T_0$. The forms over zeta23's own `Ncount` (`Zeta23.Ncount_le_mul_log`, `Zeta23.mul_log_le_Ncount`) are outside the claim set; their restatements over `MNF.RH.Ncount` (`Zeta23.MNF_Ncount_le_mul_log`, `Zeta23.MNF_mul_log_le_Ncount`, quoted in 4.11) are claimed and existential in the constants, so the values $3$ and $1/(16\pi)$ are in the proofs, not in a receipted statement. Evidence: `V6/MNF/RH/ReservoirMass.lean`: "N(0,T) ≤ 4A₀'·T log T for T ≥ 3 and N(0,T) ≥ T log T/(16π) for T ≥ an explicit T₀, from the `local_count` and `main` fields of the tree's `riemannVonMangoldt_zeta`".
5. The split point and the exponent $3/5$ (`reservoirMass_le_rpow`). Take $\delta_0=(\log T)^{-2/5}$ for $T\ge\max(T_1,e^8)$ (then $\delta_0\le\tfrac12$). Head: $\delta_0N(T)\le C\,T\,\delta_0\log T=C\,T(\log T)^{3/5}$. Tail: $\int_{\delta_0}^{1/2}(A\delta^{-5/2}+B)T\,d\delta\le(\tfrac23A\,\delta_0^{-3/2}+\tfrac B2)T=(\tfrac23A(\log T)^{3/5}+\tfrac B2)T$. Evidence: `V6/MNF/RH/ReservoirMass.lean`: "Split the layer cake at `δ₀ = (log T)^{-2/5}` (`≤ 1/2` since `log T ≥ 8`): the head `∫₀^{δ₀} NOff ≤ δ₀ · N(0,T) ≤ C · T · (log T)^{3/5}`, the tail `∫_{δ₀}^{1/2} NOff ≤ ((2/3) A₂ δ₀^{-3/2} + B₂/2) · T = ((2/3) A₂ (log T)^{3/5} + B₂/2) · T`"; `V6/MNF/RH/ReservoirMass.lean`: "The exponent `3/5` is where the two pieces balance for a majorant `δ^{-5/2}`." In general: `V6/MNF/RH/ReservoirMass.lean`: "a bound N_off(δ) ≪ T/δ^{a} gives T (log T)^{(a−1)/a}".
6. Relative form and limit: dividing by the lower bound of step 4 gives `reservoirMass_le_Ncount_mul` with constant $\lvert A_1\rvert/c$; `meanDisplacement_tendsto_zero` is a squeeze between $0$ and $A(\log T)^{-2/5}$.
7. The signed sum: the reflection $\rho\mapsto1-\bar\rho$ is a multiplicity-preserving bijection of the window that negates each term (`signedReservoir_eq_zero`).

Explicitness of the constants, as the source states it: `V6/MNF/RH/ReservoirMass.lean`: "A is explicit up to the two existential constants CG and A₀'; the constant of the second bound is 16π·|A|; the Lean statements only assert ∃ A."

### 5d. The cube module and the real-zero theorem

The module is bookkeeping over finite sums, apart from the real-zero theorem and the two eventual bounds: `V6/MNF/RH/Cube.lean`: "Apart from the real-zero theorem of §3 and the two eventual bounds at the end of §5 (which call the tree's `offLine_le_one_third`), everything is bookkeeping over finite sums of zeros".

1. The mirror. `mirror` has the same body as zeta23's `reflect` (`V6/MNF/RH/Cube.lean`: "lemma aux_mirror_eq_reflect (ρ : ℂ) : mirror ρ = Zeta23.reflect ρ := rfl"); it preserves zeros, windows and multiplicities (from the tree's reflection lemmas), and its fixed points are exactly the points with $\beta=\tfrac12$ (`mirror_eq_self_iff`).
2. Degeneracy. An off-line zero and its mirror are distinct zeros with the same ordinate (`degenerate_of_not_onLine`). Conversely, if all zeros are on the line, two zeros with the same ordinate are equal, so a simple zero is not degenerate; together: `noDegenerate_iff`.
3. The gap as injectivity of the ordinate. (i) is the definition of the gap unfolded. (ii): under the gap every zero within $\Delta$ of the line is on it, and two on-line zeros with one ordinate coincide; conversely an off-line zero within $\Delta$ of the line and its mirror are distinct zeros of the band with one ordinate. Evidence: `V6/MNF/RH/Cube.lean`: "(→: under the gap every band zero is on the line, and two on-line zeros with the same ordinate coincide. ←: an off-line band zero and its mirror are distinct band zeros with the same ordinate.)" (iii): under the gap every inner index set is empty; conversely, if the band sums vanish for every $T$, a band zero with $\gamma>0$ would contribute $m(\rho)^2\ge1$ at $T=\gamma$ through its mirror; zeros with $\gamma<0$ by conjugation; zeros with $\gamma=0$ excluded by step 5.
4. The pair sum. Rewriting as a double finite sum (`pairSum_eq_sum`) and factoring gives the marginals of 4.18; `coincidentMass_eq` separates the diagonal. The bound 4.19: an ordered pair of distinct zeros with equal ordinates has at least one off-line member (`V6/MNF/RH/Cube.lean`: "for an off-line `ρ` the partners weigh at most `N(0,T)`, and for an on-line `ρ` every partner is off-line (two on-line zeros with the same ordinate coincide), so they weigh at most `NOffLine 0 T`").
5. No real zero in $(0,1)$, from one term of Euler-Maclaurin. The tree's `Zeta0EqZeta` at $N=1$ and real $s=\sigma\in(0,1)$ gives $\zeta(\sigma)=\frac{\sigma}{\sigma-1}-\frac12+\sigma J(\sigma)$ with $J(\sigma)=\int_1^\infty\frac{\lfloor x\rfloor+\frac12-x}{x^{\sigma+1}}dx$ and $\lvert J(\sigma)\rvert\le\frac1{2\sigma}$ (`zeta_em_remainder_norm_le`, using the tree's `ZetaSum_aux1_3` and `ZetaSum_aux1_4'`). If $\zeta(\sigma)=0$ then $\sigma J(\sigma)=\frac1{1-\sigma}-\frac12>\frac12$, contradicting $\lvert\sigma J(\sigma)\rvert\le\frac12$. Evidence: `V6/MNF/RH/Cube.lean`: "tree's Euler–Maclaurin representation of ζ with one term, `ζ(σ) = σ/(σ − 1) − 1/2 + σ·J(σ)` with `‖J(σ)‖ ≤ 1/(2σ)`: a zero would need `σ·J(σ) = 1/(1 − σ) − 1/2 > 1/2`"; `V6/MNF/RH/Cube.lean`: "rw [← Zeta0EqZeta (N := 1) one_pos hre hs1]"; `V6/MNF/RH/Cube.lean`: "have hσJ : (σ : ℂ) * J = 1 / (1 - (σ : ℂ)) - 1 / 2 := by linear_combination h". `nontrivial_zero_im_ne_zero` follows because a nontrivial zero with $\gamma=0$ is a real number in $(0,1)$.

How the real-zero theorem entered: the merged module first carried it as its single `sorry`, and a fifth agent then proved it (`NOTES/cube/NODE_REPORTS.md`: "the file's only `sorry` (line 398): "no nontrivial zero is real", classical but absent from Mathlib at this pin and from the tree; no node proved it."; `NOTES/DENSITY_LEDGER.md`: "the real-zero proof by a fifth agent (`cube/nodes/REALZERO/`)"). The installed file has no `sorry` (counted: no line of `V6/MNF/RH/Cube.lean` consists of `sorry`), and both theorems have standard-axiom lines in `R11/audit.out`.

## 6. What is outside the claim set, and why

The claim set of a run is the list `theorem_names` of its challenge configuration; Comparator's verdict and the axiom audit cover exactly those names. The following are in the tree and are not claimed.

6.1 The two `sorry` lemmas of `Zeta23/BohrLandau.lean`.

```lean
/-- [MISSING 1a] the critical-strip part 1/2 < σ ≤ 1 (approximate functional equation +
Dirichlet-polynomial mean value theorem). -/
theorem meanSquare_strip {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    ∫ t in (0:ℝ)..T, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ C * T := by
  sorry

theorem zetaMeanSquare : ZetaMeanSquare := fun σ hσ =>
  if h : 1 < σ then meanSquare_gt_one h else meanSquare_strip hσ (not_lt.1 h)

/-- [MISSING 2] Littlewood's lemma on rectangles + Jensen/concavity of log, applied to ζ (or a
mollified 1 − (1 − ζ M)²), turning the mean square into a count of zeros with Re ρ ≥ 1/2 + δ. -/
theorem rightHalfBound_of_meanSquare (h : ZetaMeanSquare) : RightHalfBound := by
  sorry
```

Source of the text: `V6/Zeta23/BohrLandau.lean`, lines 96 to 108.

- Every report records them: `R11/MNF_DENSITY.md`: "sorries outside the claim set: Zeta23/BohrLandau.lean: meanSquare_strip, rightHalfBound_of_meanSquare (not in the claim set)" (the same line is in the reports of runs 7 to 10).
- Why they are still there: `V6/README.md`: "the original file is kept unchanged with its sorries so that the receipts of v2 and v3 remain reproducible. No claimed theorem depends on them (the audit prints every claimed theorem's axioms)." Checked for this sheet: the file has the same sha256 in add-ons v2 to v6, and no `audit.out` line of any run mentions `sorryAx`.
- Their statements are proved under primed names in run 9: `Zeta23.BL.meanSquare_strip'` and `Zeta23.BL.rightHalfBound_of_meanSquare'` (`BohrLandauClosure.lean`, claimed). Two caveats stated in the source and needed in the paper. First, at $\sigma=1$ the $\int_0^T$ form is vacuous: `V6/Zeta23/BL/BohrLandauClosure.lean`: "there the statement holds only vacuously, because the integrand is not interval-integrable on `[0, T]`". Second, the primed implication does not use its hypothesis: `V6/Zeta23/BL/BohrLandauClosure.lean`: "The hypothesis `h : ZetaMeanSquare` is NOT used: the conclusion is the unconditional `rightHalfBound` above" and `V6/Zeta23/BL/BohrLandauClosure.lean`: "so this is not a proof of the implication by Littlewood's lemma".
- Declarations of the supplied files that depend on the sorries and are therefore not theorems: `Zeta23.BL.zetaMeanSquare`, `Zeta23.BL.bohrLandau` (`V6/Zeta23/BohrLandau.lean`: "theorem bohrLandau : MNF.RH.BohrLandau := bohrLandau_of_right (rightHalfBound_of_meanSquare zetaMeanSquare)") and `Zeta23.Bridge.on_line_density_one_of_gap_strip_only` (`V6/Zeta23/MNFBridge.lean`: "until then this theorem depends on `sorryAx`"). The paper must cite `Zeta23.BL.bohrLandau_full`, never `Zeta23.BL.bohrLandau`.

6.2 The four supplied files `Zeta23/Superlinear.lean`, `Zeta23/OffLine.lean`, `Zeta23/BohrLandau.lean`, `Zeta23/MNFBridge.lean` (299 lines together). In the tree, not claimed: `V6/README.md`: "Also in the tree, needed by the above and NOT in the claim set: `Zeta23/Superlinear.lean`, `Zeta23/OffLine.lean`, `Zeta23/MNFBridge.lean` (sorry-free)". Their sorry-free theorems are nevertheless used by claimed theorems through delegation (4.1, 4.2, step 1 of 5a), and the claimed theorems' axiom lines show only the three standard axioms, so the kernel checked those dependencies. `Zeta23/MNFBridge.lean` is imported by no module of the layer (import lines of `V6` searched): it is compiled only if something else requests it and plays no part in any claimed statement. `Zeta23/BohrLandau.lean` is mirrored in the challenge because claimed modules use its definitions (`V6/scripts/z23_gen_density_challenge.py`: ""Zeta23.BohrLandau": "MNFChallengesD.BohrLandau",") but is not in `CLAIMED`.

6.3 The five files of step B2 (`MNF/RH/Core.lean`, `Gap.lean`, `Hypotheses.lean`, `Counting.lean`, `Zeta23Restated.lean`): reused, judged in run 6, not claimed again (`V6/README.md`: "The five MNF.RH files of step B2 are reused byte-identical.").

6.4 Excluded auxiliary lemmas.

- `MNF/RH/ReservoirMass.lean`: 27 of its 65 theorems and lemmas. Reason and list: `V6/scripts/z23_gen_density_challenge.py`: "# declarations omitted from a mirror (and from the claim set) because their statements mention # zeta23-internal objects (Zeta23.Ncount, ell1, zetaZeroConfig, Zeta23.reflect) or a constant # fixed by Classical.choose (CG, meanSquareB, A₀), or use a finiteness proof as a term (`.toFinset`, which # makes Comparator compare that proof); the results claimed in their place are the # existential / MNF-vocabulary statements that follow them in the same file". The 27 names (from the generator, confirmed against `R11/audit.out`): `CG_nonneg`, `CG_spec`, `zeta_approx_segment_half`, `meanSquare_sharp_param_half`, `meanSquareB_nonneg`, `meanSquare_explicit_small_B`, `meanSquareUnifFrom_explicit`, `meanSquareUnifFrom_explicit'`, `NRight_explicit`, `A₀_nonneg`, `Ncount_self`, `Ncount_zero_nat`, `Ncount_unit_le`, `Ncount_le_mul_log`, `ell1_half`, `mul_log_le_Ncount`, `MNF_Ncount_eq`, `reflect_re`, `reflect_im`, `reflect_reflect`, `reflect_injective`, `reflect_mem_zerosIn`, `zeta_order_reflectZ`, `reflect_bijOn`, `reflect_bijOn_zerosIn`, `NOff_eq_sum_ite`, `NOff_real_eq_sum_indicator`. Consequence for the paper: the forms with the named constants (`NRight_explicit` with $A_0$, `meanSquare_explicit_small_B` with $B_{\mathrm{ms}}$, and the numerical values $3$ and $1/(16\pi)$ in the bounds for $N(T)$) are compiled and used but are not receipted statements; the receipted statements are the existential ones (4.11 with its three companions, 4.12).
- `MNF/RH/Cube.lean`: 2 of 56. `V6/README.md`: "Two `aux_` lemmas of `Cube.lean` (statements naming `Zeta23.reflect` or a finiteness proof term) are likewise outside the claim set." They are `aux_mirror_eq_reflect` and `aux_pairSum_eq_finset_sum`. The first Comparator pre-check of this module failed because they had been left in the mirror (`NOTES/DENSITY_LEDGER.md`: "first attempt failed because the generator kept the two `aux_` lemmas in the Mathlib-only mirror").
- `MNF/Extension/InjectionEjection.lean`: 13 of 69, the helper lemmas named `aux_*` (mirrored with `sorry` in the challenge but not listed among the claimed names: `V6/scripts/z23_gen_density_challenge.py`: "if "private" not in d.group("mod") and not d.group("name").startswith("aux_"):"). The add-on README does not mention this exclusion; it follows from the generator and from the counts (69 declarations, 56 claimed).

6.5 Statements of the plans that were not proved and are in no file: Carlson's exponent (`carlson_density`), the two-sided density corollary (`offLine_density`), the false bound of section 7.

## 7. The bound that was planned, found false, and replaced (cube module)

Planned (two items of the plan):

- `NOTES/cube/CUBE_PLAN.md`: "4. `offDiagonalCoincidentMass_le (T) : offDiagonalCoincidentMass T ≤ (NOffLine 0 T : ℝ) * (Ncount 0 T : ℝ)`", with the justification `NOTES/cube/CUBE_PLAN.md`: "an on-line zero has no distinct partner with the same ordinate".
- `NOTES/cube/CUBE_PLAN.md`: "7. **`offDiagonalCoincidentMass_le_third : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, offDiagonalCoincidentMass T ≤ (1 / 3 + ε) * (Ncount 0 T : ℝ) ^ 2`**".

Found false as bookkeeping by the agent of that node. The justification fails because an on-line zero can share its ordinate with an off-line zero; the counterexample to the inequality itself: `NOTES/cube/NODE_REPORTS.md`: "an on-line zero of multiplicity 2 and a mirror pair of simple off-line zeros at one ordinate give offDiag = 2+2+2+1+2+1 = 10 while NOffLine·Ncount = 2·4 = 8". No such configuration is known to occur for $\zeta$; the point is that nothing proved on the tree excludes it (`V6/MNF/RH/Cube.lean`: "an on-line zero of multiplicity 2 sharing its ordinate with an off-line mirror pair violates the bare inequality, and nothing on the tree excludes that configuration (RH does)").

Replaced by: `offDiagonalCoincidentMass_le` with the extra term $N_0(T)N_{\ne}(T)$ (4.19), `offDiagonalCoincidentMass_le_two_mul`, and the eventual constants $2/3+\varepsilon$ and $5/9+\varepsilon$ in place of $1/3+\varepsilon$ (`NOTES/cube/NODE_REPORTS.md`: "the plan's name `offDiagonalCoincidentMass_le_third` is deliberately not used"). The false statement was not admitted with a `sorry`: `NOTES/cube/NODE_REPORTS.md`: "sorrying it would misrepresent its status". The source says that $5/9$ cannot be improved from the two inputs used: `V6/MNF/RH/Cube.lean`: "for a hypothetical window with one on-line zero of multiplicity `2N/3` and `N/3` simple off-line zeros all at one ordinate, the off-diagonal coincident mass is `5N²/9 − N/3`". The ledger's summary: `NOTES/DENSITY_LEDGER.md`: "The plan's bound offDiag ≤ NOffLine·N (constant 1/3) was found to be false as bookkeeping (an on-line double zero sharing its ordinate with an off-line mirror pair violates it) and was replaced by the N0-corrected bound".

A second, smaller correction of the same kind, for completeness: the gap equivalence (iii) of 4.16 could not be closed by the node that was assigned it, because neither Mathlib at the pin nor the tree excluded real zeros; it was first delivered under an explicit hypothesis (`spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero`, still claimed) and closed after the real-zero theorem was proved (5d).

## 8. The author's vocabulary as the files define it

For the paper each of these must be defined once in standard terms and marked as the author's.

| word | where defined | standard meaning |
|---|---|---|
| MNF | `V6/MNF/Extension/InjectionEjection.lean`: "for the Messina Nullification Framework" | the author's framework; the name of the library namespace `MNF` |
| nullification (`nullify Δ x`) | `V6/MNF/RH/Gap.lean` line 181 (quoted in section 3) | the hard threshold $x\mapsto x\cdot\mathbf 1[\lvert x\rvert\ge\Delta]$ on real numbers |
| spectral gap hypothesis (`SpectralGapHyp Δ`) | section 3 | no nontrivial zero with $0<\lvert\beta-1/2\rvert<\Delta$; a zero-free strip of half-width $\Delta$ about the line, the line excluded; RH for $\Delta\ge1/2$ |
| shifted zero spectrum | `V6/MNF/RH/Core.lean` line 61 (section 3) | the set of numbers $\beta-1/2$ |
| reservoir mass (`reservoirMass T`) | 4.12 | $\sum_{0<\gamma\le T}m(\rho)\lvert\beta-1/2\rvert$ |
| mirror | 4.14 | $\rho\mapsto1-\bar\rho$ |
| degenerate (zero) | 4.14 | multiple, or sharing its ordinate with another nontrivial zero |
| cube, pair measure (`pairSum`) | 4.14 | a weighted sum over ordered pairs of zeros of a function of $(\beta-\tfrac12,\beta'-\tfrac12,\gamma-\gamma')$ |
| st()-density | `V6/MNF/RH/Density.lean`: "No nonstandard object is involved." | a nickname for `ReservoirDensityOne`; nothing nonstandard is formalized |

The word "reservoir" is used with three different meanings in the layer; the paper has to choose one and say so:

- zeros (or points) at distance at least $\Delta$ from the line: `V6/MNF/RH/Cube.lean`: "def InReservoir (Δ : ℝ) (ρ : ℂ) : Prop := Δ ≤ |ρ.re - 1 / 2|";
- all zeros off the line: `V6/MNF/RH/ReservoirMass.lean`: ""reservoir" is its word for the zeros off the critical line (Re ρ ≠ 1/2)";
- the punctured band below the threshold, $0<\lvert x\rvert<\Delta$: `V6/MNF/RH/Strip.lean`: "the open band |x| < Δ is the Δ-reservoir plus the point 0" and `V6/MNF/RH/Density.lean`: "under a gap at Δ the Δ-reservoir is empty".

The name `ReservoirDensityOne` follows the third reading (density one within $\delta$ of the line), `reservoirMass` the second, `InReservoir` the first.

## 9. Disagreements and oddities between sources (receipt preferred)

1. Job end times. The ledger gives run 8 as `NOTES/DENSITY_LEDGER.md`: "2026-11-03 22:03:08Z–22:09:39Z" and run 9 as `NOTES/DENSITY_LEDGER.md`: "2026-11-04 00:52:20Z–00:58:52Z"; the receipts give the job ends as 22:09:37Z and 00:58:43Z (section 1). The ledger's values are the timestamps of the later `density_files_after` fact (`WORK/extracted/qrh-zeta23-density-v6-receipt/receipt/facts.tsv`: `2026-11-03T22:09:39Z	density_files_after	unchanged`, `2026-11-04T00:58:52Z	density_files_after	unchanged`). Use the receipts.
2. The report of run 9 says in its "How to read this" block that Bohr-Landau is not proved (`R9/MNF_DENSITY.md`: "Bohr–Landau itself is NOT proved"), while its own axiom table lists `Zeta23.BL.bohrLandau_full`. The record carries the erratum: `REPO/DEPOSIT_MAP.md`: "for run 9 it is false, as the same report's statement block and axiom table show (`Zeta23.BL.bohrLandau_full` with standard axioms)". The reports of runs 10 and 11 have the corrected text.
3. The "What was proved" block of every density report is a strict subset of the claimed statements (section 0). The reports do not say so. The axiom tables and `audit.out` are complete.
4. `Zeta23/MNFBridge.lean` is described as "(sorry-free)" in the add-on README (quoted in 6.2). The file contains no `sorry` token in a proof, but its last theorem depends on `sorryAx` through `Zeta23.BL.bohrLandau`, as its own docstring says (quoted in 6.1). No claimed theorem uses it.
5. Date of the layer. The add-on README is dated `V6/README.md`: "Joey Messina, 2026-11-04." and the Cube file `V6/MNF/RH/Cube.lean`: "Written 2026-11-04 on the zeta23 tree"; the cold run 11 is dated 2026-11-11 UTC (section 1). `StripDensity.lean` and `ReservoirMass.lean` say "Written 2026-11-03" while the ledger files them under 2026-11-04; the difference is consistent with local time versus UTC but the files do not say which.
6. `BohrLandauPartial.lean`: the note says 2172 lines, the installed file has 2190 (section 2); its trailer says `V6/Zeta23/BL/BohrLandauPartial.lean`: "146 `#print axioms`" while the file has 145 declarations (139 theorems and lemmas, 6 definitions) and `DensityPartial.lean` says `V6/MNF/RH/DensityPartial.lean`: "145 declarations, no sorry".
7. DEPOSIT_MAP section 10 says in its first sentence `REPO/DEPOSIT_MAP.md`: "The working notes, the receipts extracted, the plan, the two adversarial prose reviews"; the ledger records more reviews than two over the five runs (first review 37 findings, second 31, closure 34, reservoir 17, strip 14, cube 14: `NOTES/DENSITY_LEDGER.md`: "37 sentences to tighten", `NOTES/DENSITY_LEDGER.md`: "A second prose review (31 findings)", `NOTES/plan/REVIEW_CLOSURE_2026-11-03.md`: "34 findings", `NOTES/DENSITY_LEDGER.md`: "17 findings", `NOTES/DENSITY_LEDGER.md`: "14 findings — an overclaim about the saving 4δ²/(1+2δ) being attained", `NOTES/DENSITY_LEDGER.md`: "14 findings, `cube/Cube.review.diff`").

## 10. Prior art and context named in the files (for the literature sheet to confirm; nothing here is a citation)

- Bohr and Landau 1914; Titchmarsh sections 9.15, 4.11, 7.2 and Lemmas 4.2, 4.3; Hardy-Littlewood (mean value); Carlson 1920; Ingham; Littlewood 1924; Selberg 1946; Montgomery 1973 (pair correlation); Montgomery-Vaughan (the mean-value inequality). All are named in the headers quoted above. No bibliographic details are in the Lean files.
- Earlier Lean work on zero density that the record itself names, which rules out an unqualified "no prior formalization" sentence for the zero-density estimate: `REPO/DEPOSIT_MAP.md`: "Lean zero-density estimates exist on Palomar (Mark Lewko, PALOMAR-2026-10-11-000010 and -10-21-000008, Lean v4.35.0-rc2, another pin), one-sided (`Re ρ ≥ σ`)". The plan flags the same: `NOTES/strip/STRIP_PLAN.md`: "novelty subject to Mark Lewko's two unverified Palomar entries, `DEPOSIT_MAP.md` §8, to be read before any claim". The files read for this sheet do not record that those entries were read afterwards.
- Bohr-Landau: the record's statement about prior Lean formalization is dated and scoped: `V6/MNF/RH/GapDensity.lean`: "Not in Mathlib or any Lean library as of 2026-10-28" (a docstring of the proposition `BohrLandau`); the header of the same file adds `V6/MNF/RH/GapDensity.lean`: "Palomar holds one-sided zero-density estimates at Lean v4.35.0-rc2 only; nothing of this kind is in Mathlib at the pin used here".
- Real zeros: only the pin-scoped statement quoted in 4.17.
- Spelling to settle in the literature sheet: the record writes the first author of the two-thirds theorem with an umlaut (`REPO/DEPOSIT_MAP.md`: "Alpöge–Furman arXiv:2608.13637"); the task brief for this paper writes "Alpoge". This sheet has not opened the arXiv page.
- The first-derivative test: only the plan's statement that it was not in Mathlib at the pin (quoted in 5a).
- The numerics of the first 400 zeros belong to another fact sheet; the cube module states that the small-distance law is a conjecture (quoted in 4.19).

## 11. Authorship statements found for these files

- Runs 7 to 9: `REPO/NOTICE`: "Zeta23/BL/{DPMV,DPMVexp,JensenDisc,BohrLandauPartial,BohrLandauClosure}.lean: written with Claude Code (Anthropic) under Joey Messina's direction; the Bohr–Landau files by parallel workflow agents from a written plan, merged, and corrected after two adversarial prose reviews; every theorem kernel-checked and Comparator-judged."
- The four supplied files: `REPO/NOTICE`: "Zeta23/Superlinear.lean, OffLine.lean, BohrLandau.lean, MNFBridge.lean: supplied by Joey Messina on 2026-11-03 (the file does not record which tool drafted them)".
- Run 10: `REPO/NOTICE`: "MNF/RH/ReservoirMass.lean and Zeta23/Density/StripDensity.lean: written with Claude Code (Anthropic) under Joey Messina's direction by parallel workflow agents from written plans".
- Run 11: `REPO/NOTICE`: "reading the strip through the simplicity of the projected zeros is Joey Messina's idea".
- `InjectionEjection.lean`: the definitions and 18 proofs are from a sketch "as received"; 38 proofs were filled by Claude Code (quoted in section 2); NOTICE adds `REPO/NOTICE`: "(the MNF2 package's algebra, co-designed with Joey's Windows-side Claude Code session)".
- A prompt and a target file for the Aristotle prover exist for the step of run 9 (`NOTES/aristotle/PROMPT.md`, `NOTES/aristotle/BohrLandauClosure.lean`); the ledger says the chain was proved by the Claude Code workflow and `NOTES/plan/BOHR_LANDAU_CLOSURE.md`: "The Aristotle package is superseded (kept as the statement of the contract that was met)." The files do not say whether the prompt was ever sent.

## 12. Open questions for the author or the editor

1. The report block "What was proved" omits 279 of the 534 statements of run 11 (every theorem with an implicit binder), among them `density_single_window`, `riemannZeta_ofReal_ne_zero_of_mem_Ioo`, `onLineDensityOne_of_gap_only`, `zeta_approx_sharp` and `meanSquareUnif_all`. Should the paper cite `audit.out` for these (as this sheet does), and should the repository README say that the block is partial?
2. Provenance of the four supplied files (`Superlinear`, `OffLine`, `BohrLandau`, `MNFBridge`): NOTICE says the tool that drafted them is not recorded. Framing rule (7) says the Lean files of runs 7 to 11 were produced with Claude Code. Which sentence should the paper use for these four files? They are outside the claim set, but 4.1, 4.2 and step 1 of 5a delegate to them.
3. "Reservoir" has three meanings in the layer (section 8). Which one does the paper adopt, and should the name `ReservoirDensityOne` be glossed as "density one within every fixed distance of the line"?
4. Paper notation for the displacement sum (this sheet uses $D(T)$) and for the off-diagonal coincident sum (this sheet uses $O(T)$, which collides with Landau's symbol and should be changed).
5. Prior Lean zero-density estimates on Palomar (Lewko) are named in DEPOSIT_MAP section 8 and were flagged in the plan as "to be read before any claim". Were they read? Do they include a power saving, or Bohr-Landau itself? Until `WORK/facts/literature.md` settles this, no "not aware of a prior Lean formalization" sentence is supported for the zero-density estimate or for Bohr-Landau; the only supported statements are the pin-scoped ones quoted in sections 4.17 and 10.
6. The two-sided form of the zero-density estimate (over $N_{\mathrm{off}}$) is not a theorem of the layer; only the right-half count is. The paper should state the right-half form, or say that the two-sided form follows from the receipted `MNF.RH.NOff_eq_right_add_left` and `MNF.RH.NLeft_eq_NRight` (stated for `MNF.RH.NRight`, which has the same body as the `Zeta23.BL.NRight` of the estimate) without being receipted itself.
7. The explicit constants ($A_0$, $B_{\mathrm{ms}}=951+4C_G^2$, the value $1/(16\pi)$ in the lower bound for $N(T)$) live in proofs or in declarations outside the claim set; the claimed statements are existential. May the paper quote them as "in the source, compiled, not in the claim set", or should it give only the existential statements?
8. `MNF/Extension/InjectionEjection.lean` and `MNF/RH/Strip.lean` (75 of the 124 theorems of run 7) are operator bookkeeping in the author's vocabulary with no statement about $\zeta$ beyond restating the gap. How much space should the paper give them? This sheet lists them in section 2 only.
9. Was the Aristotle prompt for the run 9 step ever sent (section 11)? If it was, the authorship paragraph for `BohrLandauClosure.lean` needs a sentence.
10. Section 10 of DEPOSIT_MAP speaks of "two adversarial prose reviews" while the ledger records six (section 9, item 7). Which number should the paper give?
