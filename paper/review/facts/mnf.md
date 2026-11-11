# Fact sheet: the MNF.RH library as judged in runs 3 to 6

Scope: the author's Lean library `MNF.RH` as Comparator judged it on OpenAI's tree (runs 3, 4, 5:
add-ons v1, v2, v3) and on Anthropic's zeta23 tree (run 6). Runs 7 to 11 are outside this sheet
and are mentioned only where a source read here points forward to them.

Every entry carries its evidence as a path and a short exact quote. Lean statements in fenced
blocks are copied verbatim: theorem statements from Lean's own `#check` output in the receipts,
definitions from the source files (the receipts do not print definitions).

## 0. Sources and path abbreviations

| abbreviation | path |
|---|---|
| MAP | `/home/joeyxyxyz/repos/qrh-comparator-receipts/DEPOSIT_MAP.md` (root copy; "This root copy is the current deposit map; the copies inside the add-on folders and inside the Zenodo record of 2026-10-29 are frozen", MAP lines 23-25) |
| NOTICE | `/home/joeyxyxyz/repos/qrh-comparator-receipts/NOTICE` |
| README | `/home/joeyxyxyz/repos/qrh-comparator-receipts/README.md` |
| SUMS | `/home/joeyxyxyz/repos/qrh-comparator-receipts/CHECKSUMS.sha256` |
| V3 | `/home/joeyxyxyz/repos/qrh-comparator-receipts/sources/qrh-mnf-addon-v3` (files `MNF/RH/{Core,Gap,Hypotheses,Unconditional,Counting,Reduction,Schrodinger,GapDensity}.lean`, `SturmLiouville/SimpleEigenvalues.lean`, `MNFChallenges/*`, `README.md`) |
| Z23 | `/home/joeyxyxyz/repos/qrh-comparator-receipts/sources/qrh-zeta23-addon` (files `MNF/RH/{Core,Gap,Hypotheses,Counting,Zeta23Restated}.lean`, `README.md`) |
| LIB3 | `WORK/extracted/qrh-mnf-v3-receipt/mnf-v3/MNF_LIBRARY.md` (run 5 report) |
| LIB1, LIB2 | `WORK/extracted/qrh-mnf-receipt/mnf/MNF_LIBRARY.md`, `WORK/extracted/qrh-mnf-v2-receipt/mnf-v2/MNF_LIBRARY.md` (runs 3, 4) |
| REP6 | `WORK/extracted/qrh-zeta23-mnf-receipt/mnf/MNF_ZETA23.md` (run 6 report) |
| FACTS6 | `WORK/extracted/qrh-zeta23-mnf-receipt/receipt/facts.tsv` |
| REC2 | `WORK/extracted/qrh-zeta23-receipt/receipt/RECEIPT-zeta23.md` (run 2 receipt; quotes Anthropic's `Challenge.lean`) |

WORK = `/tmp/claude-1000/-run-media-joeyxyxyz-Seagate-Portable-Drive-math-qrh-mnf-addon/57b442eb-644f-4a72-89f3-9426dd550654/scratchpad/paper`.

Register tags, as MAP defines them (MAP lines 27-31): "**[PROVED]** kernel-checked from Mathlib
alone; **[PROVED | 7/8]** kernel-checked from Mathlib plus OpenAI's 7/8 theorem (exactly as
reliable as the Comparator PASS in RECEIPT.md); **[CONDITIONAL]** proved from explicit named
hypotheses; **[LITERATURE]** a published theorem stated as a hypothesis, not formalized;
**[OPEN]** conjecture; **[WITHDRAWN]** a corpus claim that does not survive." MAP also uses
[BOOKKEEPING], [RESTATEMENT | zeta23] and [EXTERNAL | run here / not run here] (MAP sections 1, 8).

"MNF" is the author's "Messina Nullification Framework" (NOTICE: "the Messina Nullification
Framework corpus (Joey Messina), consolidated 2026-10-27/28").

## 1. The four runs

| run | add-on / label | tree | started, ended (UTC) | theorems | definitions | kernels | result | bundle sha256 |
|---|---|---|---|---|---|---|---|---|
| 3 | v1, `mnf-library` | copy of OpenAI's verified tree | 2026-10-28T00:20:02Z, 2026-10-28T00:32:46Z | 40 | 17, listed as holes | Lean | `MNF_LIBRARY=ACCEPTED` | `f9180842f8c269b64d89ad0f236898e9164af3e5b39ef0c5e1b34561b8838d6b` |
| 4 | v2, `mnf-library-v2` | same | 2026-10-28T03:25:44Z, 2026-10-28T03:39:13Z | 43 | 17, compared by body | Lean | `MNF_LIBRARY=ACCEPTED` | `c6142a402077b7f312eb22ab990dca3b92b7bdcaa94c26836dc5dc5b15d79eb6` |
| 5 | v3, `mnf-library-v3` | same | 2026-10-29T05:56:47Z, 2026-10-29T06:10:47Z | 87 | 41, compared by body | Lean | `MNF_LIBRARY=ACCEPTED` | `023d7ada93e313296e7e9d88c82569fa65c704a2624149a67e5e74c762c8159a` |
| 6 | zeta23 add-on, `zeta23-mnf` | the zeta23 checkout checked in run 2 | 2026-10-29T02:06:38Z, 2026-10-29T02:12:34Z | 62 | 23, compared by body | NanoDa and Lean | `MNF_ZETA23=ACCEPTED` | `1476f56809c5739866e538d84d41670d573dc37fb56f74ddcc1709da065c1eef` |

Evidence.

- Run 3: LIB1 "Comparator job `mnf-library`: exit 0, started 2026-10-28T00:20:02Z, ended 2026-10-28T00:32:46Z"; "40 theorems, 17 definitions named in the challenge config". Holes: MAP section 6 item 2, "The v1 run (2026-10-28, ACCEPTED) compared the 40 statements but listed the 17 definitions as holes, which Comparator compares by name, type and universe levels only".
- Run 4: LIB2 "Comparator job `mnf-library-v2`: exit 0, started 2026-10-28T03:25:44Z, ended 2026-10-28T03:39:13Z"; "43 theorems named in the challenge config; 17 definitions in the challenge, all compared by name, type and body (definition_names is empty)".
- Run 5: LIB3 "Comparator job `mnf-library-v3`: exit 0, started 2026-10-29T05:56:47Z, ended 2026-10-29T06:10:47Z"; "87 theorems named in the challenge config; 41 definitions in the challenge, all compared by name, type and body (definition_names is empty)".
- Run 6: REP6 "Comparator job `zeta23-mnf`: exit 0, started 2026-10-29T02:06:38Z, ended 2026-10-29T02:12:34Z (warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; cold with respect to MNF/)"; "62 theorems named in the challenge config; 23 definitions in the challenge, all compared by name, type and body (definition_names is empty)"; FACTS6 "mnf_theorems	62", "mnf_definitions	23", "mnf_zeta23	MNF_ZETA23=ACCEPTED".
- Kernels: the logs of runs 3 to 5 end with the three lines "Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!" and contain no NanoDa line (LIB3, last block, and the three `logs/mnf-library*.log` files; `V3/MNFChallenges/RH.json` has `"enable_nanoda": false`). Run 6: REP6 last block has, in this order, "Running nanoda kernel on solution", "Nanoda kernel accepts the solution", "Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!".
- Axioms: LIB3 and REP6 each carry a table with one row per theorem, every row "Classical.choice, Quot.sound, propext" (87 rows in LIB3; 62 rows in REP6, counted).
- Launch, all four runs: "systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G; AF_UNIX sockets in the job: denied" (LIB1, LIB2, LIB3, REP6).
- Bundle hashes: SUMS lines 11-13 and 26.
- What Comparator did, in the report's words (LIB3): "Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice."
- Pins of runs 3 to 5 (`V3/README.md`, "Pins"): "Lean v4.34.1, Mathlib d13f23b7, openai/math adc7f124, Comparator d03acab (v4.34.0 source, built with 4.34.1), lean4export 076e8e5, landrun 811cfff". Pins of run 6 (FACTS6): "lean_version	Lean (version 4.33.0-rc2, ...", "comparator_commit	75c730e9b6ef5c2c3b334fad7c3d51fe20624c88", "lean4export_commit	9fb131bb100eb32ccf6836f14e4f8328d13b6792", "nanoda_commit	68d5ca9db226849b41a6fff59d796ff19d0a8840", "mathlib_commit	51e6992efd06126df61a496bebf8f49482a4e129", "fm_commit	16a5ce41304fcdaea4e0be7c132e1c361dc26da5".

Order in time. Run 6 (02:06 to 02:12 UTC on 2026-10-29) finished before run 5 started (05:56 UTC
the same day); the numbering follows README ("5. **MNF.RH on OpenAI's tree, v3**", "6. **MNF.RH
on Anthropic's tree**"), not the clock. `V3/README.md` says of `Counting.lean`: "Byte-identical
to the file judged on the zeta23 tree the same day."

Growth of the library across runs 3 to 5.

- v1 to v2: three theorems added, `spectralGapHyp_iff_zeroFree_strip`, `spectralGapHyp_three_eighths_iff_of`, `spectralGapHyp_three_eighths_iff` (`V3/README.md`, "What changed in v2": "40 → 43 theorems; the 17 definitions are unchanged"); a diff of the `#check` name lists of LIB1 and LIB2 made for this sheet shows exactly these three names added.
- v2 to v3 (`V3/README.md`, "What changed in v3"): "Five files added: `Counting.lean`, `Reduction.lean`, `Schrodinger.lean`, `GapDensity.lean` and `SturmLiouville/SimpleEigenvalues.lean` (a third `lean_lib`). 43 → 87 theorems, 17 → 41 definitions"; "`Core.lean`, `Gap.lean` and `Hypotheses.lean` are byte-identical to v2".
- Byte identity checked for this sheet with `cmp`: `Core.lean`, `Gap.lean` identical in v1, v2, v3 and in Z23; `Hypotheses.lean` identical in v2, v3 and Z23 (v1 differs: it lacks the two v2 theorems); `Counting.lean` identical in v3 and Z23. The receipts agree: LIB3 and REP6 both list `c768a8b2b1b8cfeea30f7e4f532e490030c611ff3017b23aea919c11a04c8f25  MNF/RH/Core.lean` and `9419bf81bfddaafe641f0587998d98aade8a663b64f65cdef3bb97466840d343  MNF/RH/Counting.lean`.

Theorems per module in run 5 (counted in `V3/MNFChallenges/*.lean`): Core 14, Gap 12, Hypotheses 10,
Unconditional 8 (challenge module `RH.lean`), Counting 13, Reduction 14, SturmLiouville 4,
Schrodinger 8, GapDensity 4; total 87. Definitions: Core 7, Gap 5, Hypotheses 5, Counting 6,
Reduction 7, SturmLiouville 4, Schrodinger 3, GapDensity 4; total 41. In run 6: Core 14 + Gap 12 +
Hypotheses 10 = 36, Counting 13, Zeta23Restated 13; total 62 (`Z23/README.md`: "62 theorem names
(the 36 Mathlib-only statements of the MNF library, 13 from `Counting.lean`, 13 from
`Zeta23Restated.lean`), no definition holes, NanoDa enabled"); definitions 7 + 5 + 5 + 6 = 23.

The source files contain further helper lemmas (for example `zeta_order_ne_top`, `gap_mono`,
`feFactor_ne_zero`) that are not named in the challenge configs; the counts above are of named,
individually compared statements.

## 2. Definitions, in standard terms

Notation of the paper: $\rho=\beta+i\gamma$ a nontrivial zero, $m(\rho)$ its multiplicity.

### 2.1 Zeros and multiplicity (`V3/MNF/RH/Core.lean`, lines 51-65 and 174)

```lean
def is_nontrivial_zero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def ZetaZeros : Set ℂ := {ρ | is_nontrivial_zero ρ}

noncomputable def zeta_order (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

def ShiftedZeroSpectrum : Set ℝ := {x | ∃ ρ ∈ ZetaZeros, x = ρ.re - 1/2}

def AllZerosSimple : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ = 1

def DerivativeNonvanishing : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → deriv riemannZeta ρ ≠ 0

noncomputable def feFactor (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2)
```

Readings.

- `is_nontrivial_zero ρ`: $\zeta(\rho)=0$ and $0<\operatorname{Re}\rho<1$. Docstring: "A nontrivial zero: a zero of `ζ` in the open critical strip."
- `zeta_order ρ`: the order of vanishing of $\zeta$ at $\rho$ as a natural number, $m(\rho)$ at a nontrivial zero. It is Mathlib's `analyticOrderAt` (values in $\mathbb{N}\cup\{\infty\}$) sent to $\mathbb{N}$ with $\infty\mapsto 0$. Docstring: "Multiplicity of `ρ` as a zero of `ζ` (0 if `ζ` is not analytic there or `ζ ρ ≠ 0`; `ENat.toNat` sends `⊤` to 0, but `⊤` never occurs at a nontrivial zero: `zeta_order_ne_top`)."
- `ShiftedZeroSpectrum`: the set $S=\{\beta-\tfrac12:\rho \text{ a nontrivial zero}\}\subset\mathbb{R}$. It is a set of real numbers: ordinates and multiplicities are forgotten. Docstring: "The MNF "shifted zero spectrum": real parts of the nontrivial zeros, centred on the line." "Spectrum" here is the author's word; no operator is involved.
- `AllZerosSimple`: every nontrivial zero has $m(\rho)=1$ (the simple-zeros conjecture). `DerivativeNonvanishing`: $\zeta'(\rho)\ne0$ at every nontrivial zero.
- `feFactor s` $=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)$, the factor in the functional equation $\zeta(1-s)=F(s)\zeta(s)$. Docstring: "The factor in `ζ(1 - s) = feFactor s · ζ s`."

The same two bodies are zeta23's trusted definitions under other names. REC2 quotes Anthropic's
challenge: "def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1" and
"def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat". MAP section 8: "Its trusted
`IsNontrivialZero` and `zeroMult` are, body for body, this library's `is_nontrivial_zero` and
`zeta_order`".

### 2.2 The gap property, the threshold operator, the zero-free region (`V3/MNF/RH/Gap.lean`, lines 34, 66, 140, 164, 181; `V3/MNF/RH/Hypotheses.lean`, line 47)

```lean
def SpectralGapProperty (S : Set ℝ) (Δ : ℝ) : Prop := ∀ x ∈ S, x = 0 ∨ |x| ≥ Δ

def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def Counter : Set ℂ := {ρ | (ρ.re = 1/4 ∨ ρ.re = 3/4) ∧ (ρ.im = 1 ∨ ρ.im = -1)}

def signGate (S : Set ℝ) : Set ℝ := {x ∈ S | -x ∉ S} ∪ {0}

noncomputable def nullify (Δ x : ℝ) : ℝ := if Δ ≤ |x| then x else 0

def SpectralGapHyp (Δ : ℝ) : Prop := SpectralGapProperty ShiftedZeroSpectrum Δ
```

Readings.

- `SpectralGapProperty S Δ`: a set $S\subset\mathbb{R}$ contains no point $x$ with $0<|x|<\Delta$. Docstring: "MNF spectral gap: every element of `S` is `0` or at least `Δ` away from it." The name is the author's; this is not a spectral gap of an operator.
- `SpectralGapHyp Δ` (the author's "spectral gap hypothesis" at threshold $\Delta$): every nontrivial zero has $\beta=\tfrac12$ or $|\beta-\tfrac12|\ge\Delta$. By the theorem `spectralGapHyp_iff_zeroFree_strip` (section 3.5) this is the statement that $\zeta$ has no zeros in the open strip $\tfrac12<\operatorname{Re}s<\tfrac12+\Delta$. `Hypotheses.lean` header: "SpectralGapHyp Δ        [OPEN]        the MNF gap at threshold Δ."
- `ZeroFreeRightOf θ`: $\zeta(s)\ne0$ for $\operatorname{Re}s>\theta$. Docstring: "`ζ` has no zeros with real part greater than `θ`.  OpenAI's theorem is `ZeroFreeRightOf (7/8)`."
- `nullify Δ x` (the author's "nullification" at threshold $\Delta$): the map $x\mapsto x$ if $|x|\ge\Delta$, $x\mapsto0$ otherwise, that is, hard thresholding of a real number at level $\Delta$ (the last four words are this sheet's gloss of the definition, not the source's). Docstring: "MNF nullification at threshold `Δ`."
- `signGate S` $=\{x\in S: -x\notin S\}\cup\{0\}$. Docstring: "The sign-consistency gate: keep an element only if its negative is absent, then add `0`."
- `Counter`: the four points $\tfrac14\pm i$, $\tfrac34\pm i$, a witness set for `symmetric_bounded_not_on_line`.

Ejection operator: none in runs 3 to 6. A search of the v1, v2, v3 and zeta23 add-on sources
for "eject" finds no Lean file (only the substring in "rejected" in scripts and documents). An
operator `eject` first appears in `MNF/Extension/InjectionEjection.lean` of
`sources/qrh-zeta23-addon-v2` (run 7), in the separate namespace `MNF.Extension`:
"def eject (Δ : ℝ) (x : ℝ) : ℝ := if x = 0 then 0 else if Δ ≤ |x| then x else if 0 < x then Δ else -Δ",
docstring "[PROPOSED] Ejection operator E(Δ,x) = sgn(x)·max(|x|,Δ), E(Δ,0) = 0". That file also
declares its own `MNF.Extension.nullify`, `NorthProbe`, `SouthProbe` (different constants from
the `MNF.RH` ones here, and the probes there have a different body, `x - Δ / 2`). It belongs to
the fact sheet for runs 7 to 11.

### 2.3 Named hypotheses (`V3/MNF/RH/Hypotheses.lean`, lines 49-59)

```lean
def LeftCriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1/2}

def SpeiserTheorem : Prop := RiemannHypothesis ↔ ∀ s ∈ LeftCriticalStrip, deriv riemannZeta s ≠ 0

def DoubleZeroForcesLeftDerivZero : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ∃ s ∈ LeftCriticalStrip, deriv riemannZeta s = 0

def MultiplicityBoundOne : Prop := ∀ ρ : ℂ, is_nontrivial_zero ρ → zeta_order ρ ≤ 1
```

Readings and registers, from the file header (lines 12-30).

- `SpeiserTheorem`: RH $\iff$ $\zeta'(s)\ne0$ for $0<\operatorname{Re}s<\tfrac12$. "SpeiserTheorem          [LITERATURE]  Speiser 1934: RH ⟺ ζ' ≠ 0 on 0 < Re s < 1/2. Not in Mathlib." It is a `Prop` used as an explicit hypothesis, never asserted.
- `DoubleZeroForcesLeftDerivZero`: a nontrivial zero of multiplicity $\ge2$ forces a zero of $\zeta'$ in $0<\operatorname{Re}s<\tfrac12$. Register "[UNSUPPORTED] ... Not a theorem of the literature; kept only so the corpus's output83 argument can be stated with its assumptions visible."
- `MultiplicityBoundOne`: $m(\rho)\le1$ at every nontrivial zero.
- `RiemannHypothesis` is Mathlib's own proposition, not redefined here (`Core.lean`: "**Mathlib's `RiemannHypothesis` is exactly "every nontrivial zero has `Re = 1/2`".**").

### 2.4 Counting functions (`V3/MNF/RH/Counting.lean`, lines 52-72; `V3/MNF/RH/GapDensity.lean`, lines 62-76)

```lean
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

noncomputable def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeta_order ρ

noncomputable def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

noncomputable def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

noncomputable def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeta_order ρ = 1}).ncard

noncomputable def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

noncomputable def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeta_order ρ

noncomputable def NOff (δ T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | δ ≤ |ρ.re - 1 / 2|}, zeta_order ρ

def BohrLandau : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (NOff δ 0 T : ℝ) ≤ C * T

def NcountSuperlinear : Prop := ∀ c : ℝ, 0 < c → ∃ T₀ : ℝ, ∀ T ≥ T₀, c * T ≤ (Ncount 0 T : ℝ)
```

Readings.

| Lean | reading | counted |
|---|---|---|
| `zerosIn T₁ T₂` | the set of nontrivial zeros with $T_1<\gamma\le T_2$ | (a set) |
| `Ncount T₁ T₂` | $N(T_1,T_2)=\sum m(\rho)$ over that window; `Ncount 0 T` is $N(T)$ | with multiplicity |
| `Ndist T₁ T₂` | $N_d(T_1,T_2)$, the number of distinct zeros in the window | distinct points |
| `N0star T₁ T₂` | $N_0^*(T_1,T_2)$, distinct zeros of the window on $\operatorname{Re}s=\tfrac12$ | distinct points |
| `N0simple T₁ T₂` | $N_0^s(T_1,T_2)$, zeros of the window on the line with $m(\rho)=1$ | distinct points |
| `N0 T₁ T₂` | $\sum m(\rho)$ over zeros of the window on the line | with multiplicity |
| `NOff δ T₁ T₂` | $\sum m(\rho)$ over zeros of the window with $|\beta-\tfrac12|\ge\delta$; `NOff δ 0 T` is $N_{\mathrm{off}}(\delta,T)$ | with multiplicity |
| `cMT` | $c_1^*=\sqrt2\tan\vartheta/(1+\vartheta\tan\vartheta)$ at $\vartheta=1/\sqrt2$ | (a real constant) |

Evidence and cautions.

- Windows are one-sided in the ordinate and allow any real endpoints: "Positive-ordinate window, not |Im ρ| (a zero and its conjugate lie in different windows); `T₁ T₂` range over all of ℝ, so windows below the real axis are allowed." (`Counting.lean`, docstring of `zerosIn`).
- The vocabulary is zeta23's, renamed: "zeta23's `Ncount` with `zeroMult` replaced by `zeta_order`" (`Counting.lean`); REC2 quotes the originals, for example "def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ".
- Three on-line counts exist and differ: `N0star` (distinct), `N0simple` (simple, hence distinct), `N0` (with multiplicity). `GapDensity.lean`: "N0 (on-line count WITH multiplicity, so that the split Ncount = N0 + NOff is exact; `N0star` of Counting.lean is the distinct count)". The paper's $N_0(T)$ must say which one is meant in each statement.
- Finite sums: `∑ᶠ` and `ncard` return 0 on an infinite set; "every count below is an `ncard`/`∑ᶠ` over `zerosIn`, which would be vacuously 0 on an infinite set, so every statement about counts threads this lemma" (`Counting.lean` header, on `zerosIn_finite`).
- `cMT`: "zeta23's Montgomery–Taylor constant c₁* = √2·tan ϑ / (1 + ϑ·tan ϑ) at ϑ = 1/√2, copied character-for-character from ChallengeDeps.lean §3 (numerically 0.7532960…)". Arithmetic repeated for this sheet in floating point: $c_1^*\approx0.7532960679$, $2-1/c_1^*\approx0.6725007$, $\tfrac32-\tfrac{1}{2c_1^*}\approx0.8362504$. The decimals are not part of any Lean statement (MAP section 8: "The decimal constants quoted for it (0.67250, 0.83625) are docstrings, not statements.").
- `BohrLandau`: for every $\delta>0$ there is $C$ with $N_{\mathrm{off}}(\delta,T)\le CT$ for all $T\ge2$. `NcountSuperlinear`: for every $c>0$, $cT\le N(T)$ for all large $T$. In runs 5 and 6 both are hypotheses only: "a named `Prop`, never asserted" (`GapDensity.lean`, both docstrings). MAP section 4 records that on the zeta23 tree they became theorems in later runs (section 7 below).

### 2.5 Reduction and Schrödinger vocabulary (`V3/MNF/RH/Reduction.lean`, lines 26-27, 77-81, 105-106, 138-140, 163-165; `V3/MNF/RH/Schrodinger.lean`, lines 41-49, 87-88)

```lean
def ZeroFreeBand (Δ : ℝ) : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → ρ.re ≤ 1/2 ∨ 1/2 + Δ ≤ ρ.re

def MultipleZeroKillsGap : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → 2 ≤ zeta_order ρ → ¬ SpectralGapHyp (1/2)

def FischerForward : Prop := SpectralGapHyp (1/2) → DerivativeNonvanishing

def RealSpectrumRealization (Λ : Set ℝ) : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → ∃ l ∈ Λ, (l : ℂ) = (ρ - 1/2) / Complex.I

def GapMechanism (Δ : ℝ) : Prop :=
  ∃ P : ℂ → Prop,
    (∀ ρ : ℂ, is_nontrivial_zero ρ → 1/2 < ρ.re → ρ.re < 1/2 + Δ → P ρ) ∧ ∀ s : ℂ, ¬ P s

noncomputable def NorthProbe (ρ : ℂ) : ℝ := ρ.re - 1/2

noncomputable def SouthProbe (ρ : ℂ) : ℝ := -(ρ.re - 1/2)

def IsSchrodingerRealization (V : ℝ → ℝ) (level : ℂ → ℝ) (eigenfunction : ℂ → (ℝ → ℝ)) : Prop :=
  IsConfiningPotential V ∧
  (∀ ρ : ℂ, is_nontrivial_zero ρ → IsSturmLiouvilleEigenfunction V (level ρ) (eigenfunction ρ)) ∧
  ∀ ρ : ℂ, is_nontrivial_zero ρ → ((level ρ : ℝ) : ℂ) = (ρ - 1/2) / Complex.I

def SchrodingerRealization : Prop :=
  ∃ (V : ℝ → ℝ) (level : ℂ → ℝ) (eigenfunction : ℂ → (ℝ → ℝ)),
    IsSchrodingerRealization V level eigenfunction

def MultiplicityDictionary (V : ℝ → ℝ) (level : ℂ → ℝ) : Prop :=
  ∀ ρ : ℂ, is_nontrivial_zero ρ → IsSimpleEigenvalue V (level ρ) → zeta_order ρ = 1
```

Readings.

- `ZeroFreeBand Δ`: no nontrivial zero with $\tfrac12<\beta<\tfrac12+\Delta$.
- `MultipleZeroKillsGap`, `FischerForward`: two hypotheses of the author's earlier corpus, kept as names so that they can be shown equivalent to "RH implies all zeros simple" (section 3.7). The names are the author's.
- `RealSpectrumRealization Λ`: a set $\Lambda\subset\mathbb{R}$ containing $(\rho-\tfrac12)/i=\gamma-i(\beta-\tfrac12)$ for every nontrivial zero. Since that number is real only when $\beta=\tfrac12$, this is RH in other words (section 3.7).
- `GapMechanism Δ`: there is a predicate that holds at every zero of the band and holds nowhere; equivalent to the band being empty (section 3.7).
- `NorthProbe ρ` $=\beta-\tfrac12$, `SouthProbe ρ` $=-(\beta-\tfrac12)$: the author's "probes"; `Reduction.lean`: "The probe identities of output86 are definitional ... They constrain nothing."
- `IsSchrodingerRealization V level u`: $V$ is a confining potential (section 6), for each nontrivial zero $\rho$ the function $u_\rho$ is an $L^2(\mathbb{R})$ eigenfunction of $-u''+Vu=t\,u$ at the real level $t=\mathrm{level}(\rho)$, and $\mathrm{level}(\rho)=(\rho-\tfrac12)/i$ as complex numbers. `SchrodingerRealization`: some such triple exists. `MultiplicityDictionary V level`: if the level of $\rho$ is a simple eigenvalue then $m(\rho)=1$.

## 3. Unconditional theorems, register [PROVED] (MAP section 1)

All statements below are copied from the block "## What was proved ... As printed by Lean
(`#check`), from the audit compile" of LIB3 (lines 16-154); those of `Core`, `Gap`, `Hypotheses`
and `Counting` appear identically in REP6. "Unconditional" means: no hypothesis about $\zeta$
beyond what Mathlib proves, and no use of OpenAI's theorem. LIB3: "Everything in
`MNF/RH/Core.lean`, `Gap.lean` and `Hypotheses.lean` is proved from Mathlib alone".

MAP's heading for this register names two files ("## 1. Unconditional — [PROVED] (MNF/RH/Core.lean,
Gap.lean)") but its table also lists theorems of `Hypotheses.lean`, `Counting.lean`,
`Reduction.lean`, `SturmLiouville` and `GapDensity.lean`; this sheet follows the table.

### 3.1 Multiplicity (Core)

```lean
MNF.RH.zeta_order_ge_one {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) : 1 ≤ MNF.RH.zeta_order ρ
MNF.RH.order_one_iff_deriv {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) : MNF.RH.zeta_order ρ = 1 ↔ deriv riemannZeta ρ ≠ 0
MNF.RH.deriv_zero_of_high_order {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) (h2 : 2 ≤ MNF.RH.zeta_order ρ) :
  deriv riemannZeta ρ = 0
MNF.RH.allZerosSimple_iff_derivativeNonvanishing : MNF.RH.AllZerosSimple ↔ MNF.RH.DerivativeNonvanishing
```

Readings: $m(\rho)\ge1$ at every nontrivial zero; $m(\rho)=1\iff\zeta'(\rho)\ne0$; $m(\rho)\ge2\Rightarrow\zeta'(\rho)=0$; all zeros simple $\iff$ $\zeta'$ vanishes at no nontrivial zero. MAP section 1: "every nontrivial zero has multiplicity ≥ 1"; "simple ⟺ ζ'(ρ) ≠ 0". These are textbook facts about zeros of analytic functions, here for $\zeta$.

### 3.2 The symmetry $\rho\mapsto1-\rho$ (Core)

```lean
MNF.RH.nontrivial_zero_reflect {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) : MNF.RH.is_nontrivial_zero (1 - ρ)
MNF.RH.deriv_reflect {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) :
  deriv riemannZeta (1 - ρ) = -(MNF.RH.feFactor ρ * deriv riemannZeta ρ)
MNF.RH.deriv_ne_zero_reflect_iff {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) :
  deriv riemannZeta (1 - ρ) ≠ 0 ↔ deriv riemannZeta ρ ≠ 0
MNF.RH.analyticOrderAt_reflect {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) :
  analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ
MNF.RH.zeta_order_reflect {ρ : ℂ} (h : MNF.RH.is_nontrivial_zero ρ) : MNF.RH.zeta_order (1 - ρ) = MNF.RH.zeta_order ρ
MNF.RH.shifted_symmetric {x : ℝ} (hx : x ∈ MNF.RH.ShiftedZeroSpectrum) : -x ∈ MNF.RH.ShiftedZeroSpectrum
```

Readings: if $\rho$ is a nontrivial zero so is $1-\rho$; at a nontrivial zero $\zeta'(1-\rho)=-F(\rho)\zeta'(\rho)$ with $F$ = `feFactor`; hence $\zeta'(1-\rho)\ne0\iff\zeta'(\rho)\ne0$; $m(1-\rho)=m(\rho)$; $S=-S$. MAP section 1: "ρ zero ⟹ 1−ρ zero; the shifted spectrum is symmetric"; "ζ'(1−ρ) = −F(ρ)·ζ'(ρ) at zeros, F ≠ 0"; "multiplicities are symmetric under ρ ↦ 1−ρ". `Core.lean` docstring of `deriv_reflect`: "(This is the statement output86 assumed as the axiom `func_eq_deriv`, restricted to zeros, where it holds; stated for all `s` it is false.)"

### 3.3 Where the zeros are; Mathlib's RH in strip form (Core)

```lean
MNF.RH.in_strip_of_zero {s : ℂ} (hs : riemannZeta s = 0) (htriv : ¬∃ n, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
  0 < s.re ∧ s.re < 1
MNF.RH.riemannHypothesis_iff_strip : RiemannHypothesis ↔ ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.re = 1 / 2
MNF.RH.riemannHypothesis_iff_shifted_subset_zero : RiemannHypothesis ↔ MNF.RH.ShiftedZeroSpectrum ⊆ {0}
MNF.RH.shifted_bounded {x : ℝ} (hx : x ∈ MNF.RH.ShiftedZeroSpectrum) : |x| < 1 / 2
```

Readings: a zero of $\zeta$ that is not a trivial zero $-2(n+1)$, $n\in\mathbb{N}$, and is not $1$, lies in $0<\operatorname{Re}s<1$; Mathlib's `RiemannHypothesis` $\iff$ every nontrivial zero has $\beta=\tfrac12$ $\iff$ $S\subseteq\{0\}$; every $x\in S$ has $|x|<\tfrac12$. MAP section 1: "Mathlib's `RiemannHypothesis` ⟺ every nontrivial zero has Re = 1/2 ⟺ S ⊆ {0}", noted as replacing "the **Bridge hypothesis** of output71/72" of the corpus. `Core.lean` docstring of `in_strip_of_zero`: "(Right of the strip: Mathlib's nonvanishing on `Re s ≥ 1`.  Left of it: the functional equation, `Γ ≠ 0`, and the zeros of `cos`.)"

### 3.4 The gap property and the squeeze (Gap)

```lean
MNF.RH.tau_threshold {S : Set ℝ} {Δ : ℝ} (hgap : MNF.RH.SpectralGapProperty S Δ) (hbound : ∀ x ∈ S, |x| < Δ) : S ⊆ {0}
MNF.RH.riemannHypothesis_iff_gap_half {Δ : ℝ} (hΔ : 1 / 2 ≤ Δ) :
  RiemannHypothesis ↔ MNF.RH.SpectralGapProperty MNF.RH.ShiftedZeroSpectrum Δ
MNF.RH.shifted_bounded_of_zeroFree {θ : ℝ} (h : MNF.RH.ZeroFreeRightOf θ) {x : ℝ}
  (hx : x ∈ MNF.RH.ShiftedZeroSpectrum) : |x| ≤ θ - 1 / 2
MNF.RH.riemannHypothesis_iff_gap_of_zeroFree {θ Δ : ℝ} (h : MNF.RH.ZeroFreeRightOf θ) (hΔ : θ - 1 / 2 < Δ) :
  RiemannHypothesis ↔ MNF.RH.SpectralGapProperty MNF.RH.ShiftedZeroSpectrum Δ
MNF.RH.riemannHypothesis_iff_remaining_strip {θ : ℝ} (h : MNF.RH.ZeroFreeRightOf θ) :
  RiemannHypothesis ↔ ∀ (s : ℂ), 1 / 2 < s.re → s.re ≤ θ → riemannZeta s ≠ 0
MNF.RH.gap_below_bound_insufficient {b Δ : ℝ} (hΔ : 0 < Δ) (hb : Δ < b) :
  ∃ S ⊆ Set.Ioo (-b) b, (∀ x ∈ S, -x ∈ S) ∧ MNF.RH.SpectralGapProperty S Δ ∧ S ≠ {0}
MNF.RH.symmetric_bounded_not_on_line :
  ¬∀ (Z : Set ℂ), (∀ ρ ∈ Z, 1 - ρ ∈ Z) → (∀ ρ ∈ Z, ρ.re ≤ 7 / 8) → ∀ ρ ∈ Z, ρ.re = 1 / 2
MNF.RH.sign_gate_trivial {S : Set ℝ} (hS : ∀ x ∈ S, -x ∈ S) : MNF.RH.signGate S = {0}
MNF.RH.sign_gate_shifted : MNF.RH.signGate MNF.RH.ShiftedZeroSpectrum = {0}
MNF.RH.nullify_dilation {l : ℝ} (hl : 0 < l) (Δ x : ℝ) : MNF.RH.nullify (l * Δ) (l * x) = l * MNF.RH.nullify Δ x
MNF.RH.gap_iff_nullify_id (S : Set ℝ) (Δ : ℝ) : MNF.RH.SpectralGapProperty S Δ ↔ ∀ x ∈ S, MNF.RH.nullify Δ x = x
MNF.RH.delta_from_ratio_38_insufficient :
  1 / 2 * (3 / 8) = 3 / 16 ∧
    ∃ S ⊆ Set.Ioo (-(3 / 8)) (3 / 8), (∀ x ∈ S, -x ∈ S) ∧ MNF.RH.SpectralGapProperty S (3 / 16) ∧ S ≠ {0}
```

Readings.

- `tau_threshold` (the author's "squeeze"): a set of reals with no point in $0<|x|<\Delta$ and all points in $|x|<\Delta$ is contained in $\{0\}$. `Gap.lean`: "The squeeze: a gap at `Δ` together with the bound `|x| < Δ` forces `S ⊆ {0}`."
- `riemannHypothesis_iff_gap_half`: for every $\Delta\ge\tfrac12$, RH $\iff$ `SpectralGapHyp Δ`, with no hypothesis. The right side is spelled `SpectralGapProperty ShiftedZeroSpectrum Δ`, which is the body of `SpectralGapHyp Δ`. Reason, from the docstring: "Since `|x| < 1/2` on the spectrum (`shifted_bounded`), a gap at any `Δ ≥ 1/2` is the same as `S ⊆ {0}`, i.e. RH." MAP section 1: "**RH ⟺ SpectralGap(S, Δ) for every Δ ≥ 1/2**, no hypothesis".
- `shifted_bounded_of_zeroFree`, `riemannHypothesis_iff_gap_of_zeroFree`, `riemannHypothesis_iff_remaining_strip`: given the hypothesis that $\zeta$ has no zeros with $\operatorname{Re}s>\theta$ (an explicit argument, any real $\theta$): $|x|\le\theta-\tfrac12$ on $S$; RH $\iff$ gap at $\Delta$ for every $\Delta>\theta-\tfrac12$; RH $\iff$ $\zeta$ has no zeros with $\tfrac12<\operatorname{Re}s\le\theta$. MAP section 1: "with a zero-free region Re > θ: RH ⟺ gap at any Δ > θ−1/2 ⟺ no zeros in 1/2 < Re ≤ θ". These are implications from a hypothesis; they become statements about $\zeta$ only when the hypothesis is supplied (section 4).
- `gap_below_bound_insufficient`: for $0<\Delta<b$ there is a set $S\subseteq(-b,b)$, symmetric under $x\mapsto-x$, with no point in $0<|x|<\Delta$, and $S\ne\{0\}$ (the proof takes $S=\{\Delta,-\Delta\}$). This is a statement about abstract sets of reals, not about $\zeta$. `Gap.lean`: "Abstract model: for every `Δ` below the bound `b`, a symmetric set inside `(-b, b)` can have a gap at `Δ` and still not be `{0}`. So a gap at `Δ ≤ θ - 1/2` cannot by itself give `S ⊆ {0}`; only the bound `|x| < Δ` does the work."
- `symmetric_bounded_not_on_line`: it is false that every set $Z\subset\mathbb{C}$ closed under $\rho\mapsto1-\rho$ and contained in $\operatorname{Re}\le\tfrac78$ lies on $\operatorname{Re}=\tfrac12$ (witness: `Counter`). MAP section 1: "symmetry + Re ≤ 7/8 do not force the line (four-point witness)". The docstring also mentions conjugation symmetry; the statement itself uses only the reflection and the bound.
- `sign_gate_trivial`, `sign_gate_shifted`: on any set symmetric under $x\mapsto-x$ the sign gate returns $\{0\}$; in particular on $S$. MAP section 1: "the hackathon sign gate returns {0} on any symmetric set: applied to S it assumes RH". The value of the theorem is negative: it shows this device yields no information about $\zeta$.
- `nullify_dilation`: for $l>0$, `nullify (lΔ) (lx) = l · nullify Δ x`. `gap_iff_nullify_id`: $S$ has the gap property at $\Delta$ $\iff$ `nullify Δ` fixes every point of $S$. MAP section 1: "nullify is dilation-covariant; the gap property is "nullify is the identity on S"".
- `delta_from_ratio_38_insufficient`: $\tfrac12\cdot\tfrac38=\tfrac3{16}$, and the abstract model of `gap_below_bound_insufficient` at $b=\tfrac38$, $\Delta=\tfrac3{16}$. MAP section 1: "the Δ/scale = ½ rule gives Δ = 3/16, which is below it".

### 3.5 The gap hypothesis is a zero-free strip (Hypotheses, added in v2)

```lean
MNF.RH.spectralGapHyp_iff_zeroFree_strip {Δ : ℝ} :
  MNF.RH.SpectralGapHyp Δ ↔ ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 / 2 + Δ → riemannZeta s ≠ 0
MNF.RH.spectralGapHyp_three_eighths_iff_of (h : MNF.RH.ZeroFreeRightOf (7 / 8)) :
  MNF.RH.SpectralGapHyp (3 / 8) ↔ ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.re = 1 / 2 ∨ ρ.re = 1 / 8 ∨ ρ.re = 7 / 8
MNF.RH.gap_of_rh (h : RiemannHypothesis) (Δ : ℝ) : MNF.RH.SpectralGapHyp Δ
```

Readings.

- `spectralGapHyp_iff_zeroFree_strip`: for every real $\Delta$, `SpectralGapHyp Δ` $\iff$ $\zeta(s)\ne0$ whenever $\tfrac12<\operatorname{Re}s<\tfrac12+\Delta$. No hypothesis. MAP section 1: "**the gap hypothesis at Δ is exactly a zero-free strip 1/2 < Re s < 1/2 + Δ** (no hypothesis, any Δ)". `Hypotheses.lean` docstring: "(the left half of the strip is covered by the symmetry `ρ ↦ 1 - ρ`; for `Δ ≤ 0` both sides hold trivially)" and "in no case is it an assumption weaker than RH about *where* the zeros are."
- `spectralGapHyp_three_eighths_iff_of`: assuming no zeros with $\operatorname{Re}s>\tfrac78$ (explicit hypothesis), the gap at exactly $\Delta=\tfrac38$ $\iff$ every nontrivial zero has $\beta\in\{\tfrac12,\tfrac18,\tfrac78\}$. MAP section 1: "shows the threshold Δ > 3/8 of §2 is exact". Docstring: "The 7/8 theorem does not exclude zeros on the boundary line `Re s = 7/8`, which is why this is not RH; it is a curiosity, recorded so that the threshold `Δ > 3/8` is seen to be exact."
- `gap_of_rh`: RH implies `SpectralGapHyp Δ` for every real $\Delta$. Docstring: "RH ⟹ gap at every Δ (the converse direction; shows the gap hypothesis is never stronger than RH)." (MAP does not list this theorem by name in sections 1 to 3; it is among the 87.)

### 3.6 Counting, register [BOOKKEEPING] (Counting, added in v3; also judged in run 6)

```lean
MNF.RH.mem_zerosIn {T₁ T₂ : ℝ} {ρ : ℂ} : ρ ∈ MNF.RH.zerosIn T₁ T₂ ↔ MNF.RH.is_nontrivial_zero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂
MNF.RH.zerosIn_subset_zetaZeros (T₁ T₂ : ℝ) : MNF.RH.zerosIn T₁ T₂ ⊆ MNF.RH.ZetaZeros
MNF.RH.zerosIn_mono {T₁ T₁' T₂ T₂' : ℝ} (h₁ : T₁' ≤ T₁) (h₂ : T₂ ≤ T₂') : MNF.RH.zerosIn T₁ T₂ ⊆ MNF.RH.zerosIn T₁' T₂'
MNF.RH.zerosIn_subset_box (T₁ T₂ : ℝ) : MNF.RH.zerosIn T₁ T₂ ⊆ Set.Icc 0 1 ×ℂ Set.Icc T₁ T₂ ∩ riemannZetaZeros
MNF.RH.zerosIn_finite (T₁ T₂ : ℝ) : (MNF.RH.zerosIn T₁ T₂).Finite
MNF.RH.Ncount_eq_sum {T₁ T₂ : ℝ} (hfin : (MNF.RH.zerosIn T₁ T₂).Finite) :
  MNF.RH.Ncount T₁ T₂ = ∑ ρ ∈ hfin.toFinset, MNF.RH.zeta_order ρ
MNF.RH.Ndist_eq_sum_ones {T₁ T₂ : ℝ} (hfin : (MNF.RH.zerosIn T₁ T₂).Finite) :
  MNF.RH.Ndist T₁ T₂ = ∑ _ρ ∈ hfin.toFinset, 1
MNF.RH.Ndist_le_Ncount (T₁ T₂ : ℝ) : MNF.RH.Ndist T₁ T₂ ≤ MNF.RH.Ncount T₁ T₂
MNF.RH.N0star_le_Ndist (T₁ T₂ : ℝ) : MNF.RH.N0star T₁ T₂ ≤ MNF.RH.Ndist T₁ T₂
MNF.RH.N0simple_le_N0star (T₁ T₂ : ℝ) : MNF.RH.N0simple T₁ T₂ ≤ MNF.RH.N0star T₁ T₂
MNF.RH.riemannHypothesis_iff_window_counts : RiemannHypothesis ↔ ∀ (T₁ T₂ : ℝ), MNF.RH.N0star T₁ T₂ = MNF.RH.Ndist T₁ T₂
MNF.RH.allZerosSimple_iff_window_counts :
  MNF.RH.AllZerosSimple ↔ ∀ (T₁ T₂ : ℝ), MNF.RH.Ncount T₁ T₂ = MNF.RH.Ndist T₁ T₂
MNF.RH.N0simple_eq_deriv_form (T₁ T₂ : ℝ) :
  MNF.RH.N0simple T₁ T₂ = (MNF.RH.zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | deriv riemannZeta ρ ≠ 0}).ncard
```

Readings: each window $(T_1,T_2]$ holds finitely many nontrivial zeros (from Mathlib: "Every window contains finitely many nontrivial zeros (Mathlib's `IsCompact.inter_riemannZetaZeros_finite` on the compact box)", `Counting.lean`); $N_0^s\le N_0^*\le N_d\le N$ on every window; RH $\iff$ $N_0^*(T_1,T_2)=N_d(T_1,T_2)$ for all real $T_1,T_2$; all zeros simple $\iff$ $N(T_1,T_2)=N_d(T_1,T_2)$ for all real $T_1,T_2$; the simple on-line zeros of a window are the on-line zeros of the window with $\zeta'\ne0$.

Register and limits, MAP section 1: "[BOOKKEEPING]; zeta23's vocabulary over MNF's names"; "[BOOKKEEPING] restatements, not density results". `Counting.lean` header: "The two equivalences of §4 are restatements of the definitions, not density results: they say nothing about proportions of zeros, and nothing here advances RH or the simple-zeros conjecture."

### 3.7 The reductions (Reduction, added in v3)

```lean
MNF.RH.gap_iff_zeroFreeBand (Δ : ℝ) : MNF.RH.SpectralGapHyp Δ ↔ MNF.RH.ZeroFreeBand Δ
MNF.RH.gap_of_right_side {Δ : ℝ} (h : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → 1 / 2 < ρ.re → 1 / 2 + Δ ≤ ρ.re) :
  MNF.RH.SpectralGapHyp Δ
MNF.RH.rh_of_band_of_zeroFree {θ : ℝ} (hθ : MNF.RH.ZeroFreeRightOf θ)
  (h : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → 1 / 2 < ρ.re → θ < ρ.re) : RiemannHypothesis
MNF.RH.multipleZeroKillsGap_iff : MNF.RH.MultipleZeroKillsGap ↔ RiemannHypothesis → MNF.RH.AllZerosSimple
MNF.RH.fischerForward_iff : MNF.RH.FischerForward ↔ RiemannHypothesis → MNF.RH.AllZerosSimple
MNF.RH.re_eq_half_of_real_eigenvalue {ρ : ℂ} {l : ℝ} (h : ↑l = (ρ - 1 / 2) / Complex.I) : ρ.re = 1 / 2
MNF.RH.rh_of_realSpectrumRealization {Λ : Set ℝ} (h : MNF.RH.RealSpectrumRealization Λ) : RiemannHypothesis
MNF.RH.allZerosSimple_of_multiplicity_dictionary {Λ : Set ℝ} (mult : ℝ → ℕ)
  (hdict : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ∃ l ∈ Λ, mult l = MNF.RH.zeta_order ρ)
  (hsimple : ∀ l ∈ Λ, mult l = 1) : MNF.RH.AllZerosSimple
MNF.RH.gap_of_mechanism {Δ : ℝ} (M : MNF.RH.GapMechanism Δ) : MNF.RH.SpectralGapHyp Δ
MNF.RH.mechanism_of_gap {Δ : ℝ} (h : MNF.RH.SpectralGapHyp Δ) : MNF.RH.GapMechanism Δ
MNF.RH.gapMechanism_iff (Δ : ℝ) : MNF.RH.GapMechanism Δ ↔ MNF.RH.SpectralGapHyp Δ
MNF.RH.probe_balance (ρ : ℂ) : MNF.RH.NorthProbe ρ + MNF.RH.SouthProbe ρ = 0
MNF.RH.probe_reflect (ρ : ℂ) : MNF.RH.NorthProbe (1 - ρ) = MNF.RH.SouthProbe ρ
MNF.RH.probes_zero_iff (ρ : ℂ) : MNF.RH.NorthProbe ρ = 0 ∧ MNF.RH.SouthProbe ρ = 0 ↔ ρ.re = 1 / 2
```

In Lean's printing, `A ↔ B → C` parses as `A ↔ (B → C)`; the source writes
`MultipleZeroKillsGap ↔ (RiemannHypothesis → AllZerosSimple)` (`Reduction.lean`, line 83).

Readings.

- The gap at $\Delta$ $\iff$ no nontrivial zero with $\tfrac12<\beta<\tfrac12+\Delta$; it suffices to control the zeros with $\beta>\tfrac12$; given no zeros right of $\theta$, RH follows from the hypothesis that every nontrivial zero with $\beta>\tfrac12$ has $\beta>\theta$, which under the zero-free region says exactly that no zero has $\tfrac12<\beta\le\theta$. MAP section 1: "the gap at Δ IS the zero-free band 1/2 < Re ρ < 1/2 + Δ; one side suffices; with a region Re > θ, RH ⟺ no zero with 1/2 < Re ρ ≤ θ".
- `multipleZeroKillsGap_iff`, `fischerForward_iff`: each of the two corpus hypotheses is equivalent to the implication "RH $\Rightarrow$ all zeros simple". MAP section 1: "so neither is a route to RH and no experiment bears on them".
- `rh_of_realSpectrumRealization`: if some set of real numbers contains $(\rho-\tfrac12)/i$ for every nontrivial zero, RH holds. `allZerosSimple_of_multiplicity_dictionary`: if each zero corresponds to a point of $\Lambda$ whose assigned multiplicity equals $m(\rho)$ and all assigned multiplicities are 1, all zeros are simple. MAP section 1: "Hilbert–Pólya without an operator". `Reduction.lean`: "(The dictionary is the whole content; nothing about ζ is used.)"
- `gapMechanism_iff`: a "gap mechanism" at $\Delta$ exists $\iff$ `SpectralGapHyp Δ`. MAP section 1: "the precise form of "the gap route is RH restated"".
- Probes: $N(\rho)+S(\rho)=0$, $N(1-\rho)=S(\rho)$, and both vanish $\iff$ $\beta=\tfrac12$.

Purpose, in the file's words (`Reduction.lean` header): "Each theorem rewrites one of the corpus's "attack" hypotheses into its exact mathematical content". MAP section 9: "Nothing in them proves RH or the simple-zeros conjecture".

### 3.8 Window bookkeeping for the gap (GapDensity, added in v3)

```lean
MNF.RH.N0_le_Ncount (T₁ T₂ : ℝ) : MNF.RH.N0 T₁ T₂ ≤ MNF.RH.Ncount T₁ T₂
MNF.RH.NOff_le_Ncount (δ T₁ T₂ : ℝ) : MNF.RH.NOff δ T₁ T₂ ≤ MNF.RH.Ncount T₁ T₂
MNF.RH.gap_forces_NOff_eq {Δ : ℝ} (hΔ : 0 < Δ) (hgap : MNF.RH.SpectralGapHyp Δ) (T₁ T₂ : ℝ) :
  MNF.RH.Ncount T₁ T₂ = MNF.RH.N0 T₁ T₂ + MNF.RH.NOff Δ T₁ T₂
```

Readings: with multiplicity, the on-line count and the off-line count at any $\delta$ are each at most the total; if the gap hypothesis holds at some $\Delta>0$ then on every window $N=N_0+N_{\mathrm{off}}(\Delta)$ exactly. MAP section 1: "[BOOKKEEPING]". The third statement has the gap as a hypothesis; MAP lists it in section 1 because nothing else is assumed. `GapDensity.lean`: "The binder `0 < Δ` is mandatory: for Δ ≤ 0 every on-line zero also lies in the second piece and the equation fails."

The Sturm–Liouville theorem, which MAP also lists in section 1, is in section 6 below.

## 4. Theorems proved from OpenAI's theorem, register [PROVED | 7/8] (MAP section 2; `Unconditional.lean`; run 5, and in smaller form runs 3 and 4)

The file imports OpenAI's library and uses it once (`V3/MNF/RH/Unconditional.lean`, lines 22-27):

```lean
import OAI.NumberTheory.DirichletL.Nonvanishing

namespace MNF.RH

theorem zeroFree_seven_eighths : ZeroFreeRightOf (7/8) :=
  fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs
```

The eight statements, as printed by Lean (LIB3, lines 75-85):

```lean
MNF.RH.zeroFree_seven_eighths : MNF.RH.ZeroFreeRightOf (7 / 8)
MNF.RH.nontrivial_zero_re_le_seven_eighths {ρ : ℂ} (hρ : MNF.RH.is_nontrivial_zero ρ) : ρ.re ≤ 7 / 8
MNF.RH.shifted_bounded_three_eighths {x : ℝ} (hx : x ∈ MNF.RH.ShiftedZeroSpectrum) : |x| ≤ 3 / 8
MNF.RH.riemannHypothesis_iff_gap_three_eighths {Δ : ℝ} (hΔ : 3 / 8 < Δ) : RiemannHypothesis ↔ MNF.RH.SpectralGapHyp Δ
MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths :
  RiemannHypothesis ↔ ∀ (s : ℂ), 1 / 2 < s.re → s.re ≤ 7 / 8 → riemannZeta s ≠ 0
MNF.RH.rh_of_gap_three_eighths {Δ : ℝ} (hΔ : 3 / 8 < Δ) (h : MNF.RH.SpectralGapHyp Δ) : RiemannHypothesis
MNF.RH.spectralGapHyp_three_eighths_iff :
  MNF.RH.SpectralGapHyp (3 / 8) ↔ ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.re = 1 / 2 ∨ ρ.re = 1 / 8 ∨ ρ.re = 7 / 8
MNF.RH.rh_of_band_seven_eighths (h : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → 1 / 2 < ρ.re → 7 / 8 < ρ.re) :
  RiemannHypothesis
```

Readings: OpenAI's theorem in the library's vocabulary ($\zeta(s)\ne0$ for $\operatorname{Re}s>\tfrac78$); every nontrivial zero has $\beta\le\tfrac78$; $|x|\le\tfrac38$ on $S$ (the left bound from the reflection); for every $\Delta>\tfrac38$, RH $\iff$ `SpectralGapHyp Δ`; RH $\iff$ no zeros with $\tfrac12<\operatorname{Re}s\le\tfrac78$; gap at exactly $\tfrac38$ $\iff$ every nontrivial zero has $\beta\in\{\tfrac12,\tfrac18,\tfrac78\}$; RH follows if the closed band $\tfrac12<\beta\le\tfrac78$ holds no zero.

Status and reliability.

- `Unconditional.lean` header: "REGISTER: [WRAPPER].  No mathematics happens here; every proof is one application of a theorem of MNF/RH/Gap.lean, Hypotheses.lean or Reduction.lean to zeroFree_seven_eighths : ZeroFreeRightOf (7/8)" and "These statements are exactly as reliable as OpenAI's theorem: cite them as proved only together with a Comparator PASS for that theorem at that commit."
- MAP section 2: "Same content as the kit's `MNF_Bridge78_Unconditional.lean`, restated over the consolidated definitions."
- MAP section 8: OpenAI's theorem is "Consumed once, as `zeroFree_seven_eighths`; everything in §2 rests on it."
- Seven of the eight were in v2 (`V3/README.md`: "The seven Unconditional statements cannot be pre-checked outside OpenAI's tree"); v3 adds `rh_of_band_seven_eighths` ("adds `rh_of_band_seven_eighths`, the 7/8 instance of `rh_of_band_of_zeroFree`").
- These eight are not in run 6: the zeta23 tree is at another Lean and Mathlib pin and has no OpenAI library (MAP section 8: "it lives at a different Lean/Mathlib pin from OpenAI's tree and this library's Unconditional layer, so no file here imports it").

### 4.1 Exactly how the gap hypothesis relates to RH and to a zero-free strip

Write $G(\Delta)$ for `SpectralGapHyp Δ`: every nontrivial zero has $\beta=\tfrac12$ or $|\beta-\tfrac12|\ge\Delta$.

| range of $\Delta$ | what is proved | needs | Lean name | where |
|---|---|---|---|---|
| every real $\Delta$ | $G(\Delta)\iff\zeta$ has no zeros with $\tfrac12<\operatorname{Re}s<\tfrac12+\Delta$ | Mathlib only | `spectralGapHyp_iff_zeroFree_strip`; also `gap_iff_zeroFreeBand` | section 3.5, 3.7 |
| every real $\Delta$ | RH $\Rightarrow G(\Delta)$ | Mathlib only | `gap_of_rh` | section 3.5 |
| $\Delta\le0$ | $G(\Delta)$ holds trivially | Mathlib only | docstring of `spectralGapHyp_iff_zeroFree_strip` ("for `Δ ≤ 0` both sides hold trivially") | not a named theorem |
| $\Delta\ge\tfrac12$ | RH $\iff G(\Delta)$ | Mathlib only | `riemannHypothesis_iff_gap_half`, `rh_of_gap` | section 3.4, 5 |
| $\Delta>\theta-\tfrac12$ | RH $\iff G(\Delta)$ | hypothesis: no zeros with $\operatorname{Re}s>\theta$ | `riemannHypothesis_iff_gap_of_zeroFree`, `rh_of_gap_of_zeroFree` | section 3.4, 5 |
| $\Delta>\tfrac38$ | RH $\iff G(\Delta)$ | OpenAI's 7/8 theorem | `riemannHypothesis_iff_gap_three_eighths`, `rh_of_gap_three_eighths` | section 4 |
| $\Delta=\tfrac38$ | $G(\tfrac38)\iff$ every nontrivial zero has $\beta\in\{\tfrac12,\tfrac18,\tfrac78\}$ | OpenAI's 7/8 theorem | `spectralGapHyp_three_eighths_iff` | section 4 |
| $0<\Delta<b$ (abstract sets) | some symmetric $S\subseteq(-b,b)$ has the gap at $\Delta$ and $S\ne\{0\}$ | nothing; not about $\zeta$ | `gap_below_bound_insufficient` | section 3.4 |

What follows from the table, in the sources' words.

- MAP section 4: "`SpectralGapHyp Δ` for any Δ > 0. For Δ > 3/8 it is RH (§2); for every Δ it is, kernel-checked (`spectralGapHyp_iff_zeroFree_strip`, §1), the zero-free strip 1/2 < Re ρ < 1/2 + Δ next to the line, not known for any Δ > 0."
- `Gap.lean` header: "The gap hypothesis is therefore not a weaker assumption than RH; it is RH in other words."
- MAP section 2, on $\Delta=\tfrac38$: "it is not RH, because the 7/8 theorem leaves the line Re s = 7/8 itself open, and nobody conjectures zeros there."
- LIB3, "How to read this": "The Riemann Hypothesis is not among the theorems. `riemannHypothesis_iff_gap_three_eighths` says the MNF gap hypothesis at any Δ > 3/8 *is* RH; `gap_below_bound_insufficient` says a gap at Δ ≤ 3/8 cannot give it. `riemannHypothesis_iff_remaining_strip_seven_eighths` says what is left: no zeros with 1/2 < Re s ≤ 7/8."

Caution on "insufficient" (this sheet's reading of the Lean statements; see section 11, item 2). The
phrases "insufficient for every Δ ≤ 3/8" (MAP section 6), "cannot give it" (LIB3) and "*does not
imply RH* for any Δ ≤ 3/8 (§4, abstract model)" (`Gap.lean` header) rest on
`gap_below_bound_insufficient`, whose Lean statement requires $0<\Delta<b$ strictly and concerns
an arbitrary symmetric set of reals, not the zero set of $\zeta$. What is proved is that the
squeeze argument (symmetry plus the bound $|x|\le\tfrac38$ plus a gap at $\Delta<\tfrac38$) does
not close; it is not proved, and could not be without settling RH, that $G(\Delta)$ fails to
imply RH for $\zeta$. The case $\Delta=\tfrac38$ is covered separately by
`spectralGapHyp_three_eighths_iff`. On a tree without the 7/8 theorem (run 6 and later) the
unconditional threshold is $\tfrac12$: MAP section 6 item 4, "`SpectralGapHyp`, which is
unchanged: RH for Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2."

## 5. Conditional theorems, register [CONDITIONAL] (MAP section 3)

Each hypothesis is an explicit argument; none is asserted. `Hypotheses.lean` header: "Every
assumption the corpus ever took as an `axiom` about ζ, restated as a named `Prop` and used only
as an explicit argument.  This file adds no axiom to Lean". LIB3: "`SpeiserTheorem` and
`DoubleZeroForcesLeftDerivZero` are hypotheses (explicit arguments), not axioms; nothing here
asserts them."

```lean
MNF.RH.rh_of_gap {Δ : ℝ} (hΔ : 1 / 2 ≤ Δ) (h : MNF.RH.SpectralGapHyp Δ) : RiemannHypothesis
MNF.RH.rh_of_gap_of_zeroFree {θ Δ : ℝ} (hθ : MNF.RH.ZeroFreeRightOf θ) (hΔ : θ - 1 / 2 < Δ)
  (h : MNF.RH.SpectralGapHyp Δ) : RiemannHypothesis
MNF.RH.multiplicityBoundOne_iff_allZerosSimple : MNF.RH.MultiplicityBoundOne ↔ MNF.RH.AllZerosSimple
MNF.RH.derivativeNonvanishing_of_left
  (h : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.re ≤ 1 / 2 → deriv riemannZeta ρ ≠ 0) : MNF.RH.DerivativeNonvanishing
MNF.RH.allZerosSimple_of_speiser_and_double_zero_hyp (hRH : RiemannHypothesis) (hSp : MNF.RH.SpeiserTheorem)
  (hDZ : MNF.RH.DoubleZeroForcesLeftDerivZero) : MNF.RH.AllZerosSimple
MNF.RH.allZerosSimple_of_rh_of_line (hRH : RiemannHypothesis)
  (hline : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → ρ.re = 1 / 2 → deriv riemannZeta ρ ≠ 0) : MNF.RH.AllZerosSimple
MNF.RH.rh_of_symmetric_operator.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : E →ₗ[ℂ] E)
  (hT : T.IsSymmetric)
  (hspec : ∀ (ρ : ℂ), MNF.RH.is_nontrivial_zero ρ → Module.End.HasEigenvalue T ((ρ - 1 / 2) / Complex.I)) :
  RiemannHypothesis
MNF.RH.realization_forces_line {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) {ρ : ℂ} (hρ : MNF.RH.is_nontrivial_zero ρ) : ρ.re = 1 / 2
MNF.RH.rh_of_realization (hR : MNF.RH.SchrodingerRealization) : RiemannHypothesis
MNF.RH.realSpectrumRealization_of_realization {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) : MNF.RH.RealSpectrumRealization (Set.range level)
MNF.RH.eigenvalue_simple_of_realization {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) (ρ : ℂ) : IsSimpleEigenvalue V (level ρ)
MNF.RH.eigenfunction_unique_of_realization {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) {ρ : ℂ} (hρ : MNF.RH.is_nontrivial_zero ρ) (v : ℝ → ℝ)
  (hv : IsSturmLiouvilleEigenfunction V (level ρ) v) : ∃ c, ∀ (x : ℝ), v x = c * u ρ x
MNF.RH.allZerosSimple_of_realization {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) (hd : MNF.RH.MultiplicityDictionary V level) : MNF.RH.AllZerosSimple
MNF.RH.derivativeNonvanishing_of_realization {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) (hd : MNF.RH.MultiplicityDictionary V level) :
  MNF.RH.DerivativeNonvanishing
MNF.RH.multiplicityDictionary_iff {V : ℝ → ℝ} {level : ℂ → ℝ} {u : ℂ → ℝ → ℝ}
  (hR : MNF.RH.IsSchrodingerRealization V level u) : MNF.RH.MultiplicityDictionary V level ↔ MNF.RH.AllZerosSimple
MNF.RH.on_line_density_one_of_gap (hBL : MNF.RH.BohrLandau) (hN : MNF.RH.NcountSuperlinear) {Δ : ℝ} (hΔ : 0 < Δ)
  (hgap : MNF.RH.SpectralGapHyp Δ) (ε : ℝ) : ε > 0 → ∃ T₀, ∀ T ≥ T₀, (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0 0 T)
```

| theorem | named hypotheses | reading | MAP's note (quoted) |
|---|---|---|---|
| `rh_of_gap` | `SpectralGapHyp Δ`, $\Delta\ge\tfrac12$ | the gap at $\Delta\ge\tfrac12$ implies RH | "the hypothesis is RH itself (§1)" |
| `rh_of_gap_of_zeroFree` | `ZeroFreeRightOf θ`, `SpectralGapHyp Δ`, $\Delta>\theta-\tfrac12$ | the same with a zero-free half-plane | (not listed by name in MAP section 3) |
| `rh_of_gap_three_eighths` | `SpectralGapHyp Δ`, $\Delta>\tfrac38$; uses OpenAI's theorem | the gap at $\Delta>\tfrac38$ implies RH | "likewise, given 7/8" |
| `multiplicityBoundOne_iff_allZerosSimple` | none | $m\le1$ everywhere $\iff$ $m=1$ everywhere | "output40's "one conjecture" is the simple-zeros conjecture verbatim" |
| `derivativeNonvanishing_of_left` | none ($\zeta'\ne0$ at zeros with $\beta\le\tfrac12$ is the premise) | it suffices to check $\zeta'(\rho)\ne0$ for $\beta\le\tfrac12$ | "simplicity need only be checked for Re ρ ≤ 1/2 (symmetry does the rest)" |
| `allZerosSimple_of_speiser_and_double_zero_hyp` | RH, `SpeiserTheorem`, `DoubleZeroForcesLeftDerivZero` | under all three, all zeros are simple | "output83's argument with both assumptions visible; see §5" |
| `allZerosSimple_of_rh_of_line` | RH, $\zeta'\ne0$ at zeros on the line | under both, all zeros are simple | "a restatement; Speiser contributes nothing to simplicity" |
| `rh_of_symmetric_operator` | a symmetric linear operator $T$ on a complex inner product space with $(\rho-\tfrac12)/i$ an eigenvalue for every nontrivial zero | then RH | "Hilbert–Pólya ⟹ RH, in one step; the operator is the open part" |
| `rh_of_realization`, `realization_forces_line` | `SchrodingerRealization` (resp. `IsSchrodingerRealization V level u`) | a realization implies RH; its third conjunct alone forces $\beta=\tfrac12$ | "the realization's dictionary conjunct alone forces Re ρ = 1/2: filling it in IS proving RH" |
| `eigenvalue_simple_of_realization`, `eigenfunction_unique_of_realization`, `allZerosSimple_of_realization`, `derivativeNonvanishing_of_realization`, `multiplicityDictionary_iff` | a realization; for the last three also (or as the subject) a `MultiplicityDictionary` | every level is a simple eigenvalue (by the Sturm–Liouville theorem); with a dictionary all zeros are simple; under a realization the dictionary $\iff$ `AllZerosSimple` | "every level is a simple eigenvalue by Sturm–Liouville (free); the dictionary is ⟺ `AllZerosSimple`, so SL does not shortcut simplicity" |
| `on_line_density_one_of_gap` | `BohrLandau` [LITERATURE], `NcountSuperlinear` [LITERATURE], `SpectralGapHyp Δ` with $\Delta>0$ | for every $\varepsilon>0$ and all large $T$, $(1-\varepsilon)N(T)\le N_0(T)$, with $N_0$ = `N0` (with multiplicity) | "a zero-free strip next to the line plus Bohr–Landau gives density one on the line (which follows from RH and is not known to imply it); folklore, not new mathematics." |

Notes.

- MAP's section 3 heading names `Hypotheses.lean`, and MAP places `rh_of_gap_three_eighths` in both section 2 and section 3; that theorem lives in `Unconditional.lean` and depends on OpenAI's theorem.
- `rh_of_symmetric_operator`: `Hypotheses.lean` docstring, "eigenvalues of a symmetric operator are real, and `(ρ - 1/2) / i` is real iff `Re ρ = 1/2`. This is the whole of the implication; the operator is the open part."
- Schrödinger file header: "What the SL theorem buys: once a realization exists, "the spectrum is simple" is free. What it does not buy: the existence of `V`, or the link between spectral multiplicity and `zeta_order` (the `MultiplicityDictionary` hypothesis below).  Those two are the whole problem.  Nothing here advances RH or the simple-zeros conjecture."
- `on_line_density_one_of_gap`: `GapDensity.lean` header, ""Density one on the line" is strictly weaker than RH: it allows infinitely many zeros off the line as long as they are o(N(T))" and "a folklore implication, not new mathematics". In run 5 both literature inputs are hypotheses: "No Lean library supplies either Prop as of 2026-10-28" (`V3/README.md`). MAP section 3 adds the forward pointer: "On the zeta23 tree both literature Props are now theorems (§10), so the same conclusion holds there from the gap alone: `MNF.RH.onLineDensityOne_of_gap_only` (receipt v4). The gap enters only through the window split `gap_forces_NOff_eq`".

## 6. The Sturm–Liouville simplicity file and its authorship (run 5 only)

File: `V3/SturmLiouville/SimpleEigenvalues.lean` (581 lines; sha256 in LIB3:
`efaae3a2a6b1f929754d450d7cbdcef0d6b4d643b29eb2a018a784b4dad8a0fe  SturmLiouville/SimpleEigenvalues.lean`).
It is in the root namespace, not `MNF.RH`, and is about one-dimensional Schrödinger operators,
not about $\zeta$.

Definitions (source, lines 58-69 and 557-561):

```lean
def IsConfiningPotential (V : ℝ → ℝ) : Prop :=
  Continuous V ∧ Filter.Tendsto V (Filter.cocompact ℝ) Filter.atTop

def IsSturmLiouvilleEigenfunction (V : ℝ → ℝ) (eigval : ℝ) (u : ℝ → ℝ) : Prop :=
  Differentiable ℝ u ∧
  Differentiable ℝ (deriv u) ∧
  (∀ x, -(deriv (deriv u) x) + V x * u x = eigval * u x) ∧
  u ≠ 0 ∧
  MeasureTheory.MemLp u 2 MeasureTheory.volume

def wronskian (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * deriv v x - v x * deriv u x

def IsSimpleEigenvalue (V : ℝ → ℝ) (eigval : ℝ) : Prop :=
  ∀ u v : ℝ → ℝ,
    IsSturmLiouvilleEigenfunction V eigval u →
    IsSturmLiouvilleEigenfunction V eigval v →
    ∃ c : ℝ, ∀ x, v x = c * u x
```

The four judged statements, as printed by Lean (LIB3, lines 121-130):

```lean
wronskian_constant_same_eigenvalue (V : ℝ → ℝ) (eigval : ℝ) (u v : ℝ → ℝ)
  (hu : IsSturmLiouvilleEigenfunction V eigval u) (hv : IsSturmLiouvilleEigenfunction V eigval v) :
  ∃ C, ∀ (x : ℝ), wronskian u v x = C
wronskian_zero_of_l2 (V : ℝ → ℝ) (eigval : ℝ) (hV : IsConfiningPotential V) (u v : ℝ → ℝ)
  (hu : IsSturmLiouvilleEigenfunction V eigval u) (hv : IsSturmLiouvilleEigenfunction V eigval v) (x : ℝ) :
  wronskian u v x = 0
linearly_dependent_of_wronskian_zero (V : ℝ → ℝ) (eigval : ℝ) (hV_cont : Continuous V) (u v : ℝ → ℝ)
  (hu : IsSturmLiouvilleEigenfunction V eigval u) (hv : IsSturmLiouvilleEigenfunction V eigval v)
  (hW : ∀ (x : ℝ), wronskian u v x = 0) : ∃ c, ∀ (x : ℝ), v x = c * u x
sturm_liouville_simple_eigenvalues (V : ℝ → ℝ) (hV : IsConfiningPotential V) (eigval : ℝ) : IsSimpleEigenvalue V eigval
```

Readings.

- Confining potential: $V:\mathbb{R}\to\mathbb{R}$ continuous with $V(x)\to+\infty$ as $|x|\to\infty$ (the cocompact filter on $\mathbb{R}$).
- Eigenfunction at the real number $\lambda$: a real function $u$, differentiable with differentiable derivative, satisfying $-u''(x)+V(x)u(x)=\lambda u(x)$ for every $x$, not identically zero, and in $L^2(\mathbb{R})$.
- Theorem: for a confining potential and any real $\lambda$, any two such eigenfunctions $u,v$ satisfy $v=cu$ for a real constant $c$; that is, each $L^2$ eigenspace of $-\tfrac{d^2}{dx^2}+V$ has dimension at most one. The statement is for every real $\lambda$ and is vacuous when $\lambda$ has no eigenfunction. Route: the Wronskian of two eigenfunctions is constant, is zero for $L^2$ eigenfunctions of a confining potential, and a vanishing Wronskian gives proportionality (source docstring: "Chain: confining → `wronskian_zero_of_l2` (W ≡ 0) → `linearly_dependent_of_wronskian_zero` (v = c·u).").
- MAP section 1: "for a continuous confining `V`, any two `L²` eigenfunctions of −u'' + V u = λu are proportional"; "a statement about 1-D Schrödinger operators, not about ζ. Classical (the limit-point case of Weyl's theory: Coddington–Levinson ch. 9, Teschl *Mathematical Methods in Quantum Mechanics* ch. 9, Berezin–Shubin)".

Authorship and history.

- NOTICE: "SturmLiouville/SimpleEigenvalues.lean: co-authored by Aristotle (Harmonic), aristotle-harmonic@harmonic.fun, 2026-03-03, consolidated by Joey 2026-10-27 and ported to Mathlib d13f23b7 on 2026-10-28 (proof-internal changes only)."
- File header: "Consolidated 2026-10-27 from the three corpus variants sturm_liouville_master.lean.txt, sturm_liouville_PHASE1_COMPLETE.lean, strum_louifinal.lean.txt   (all Aristotle, Lean v4.24.0 / Mathlib f897ebcf, 2026-03-03)." and "Co-authored-by: Aristotle (Harmonic)". The header lists what was dropped in consolidation (auxiliary lemma copies containing `exact?` / `skip`, duplicates) and the kept chain of fourteen lemmas and theorems.
- `V3/README.md`: "Joey's consolidated corpus file (Aristotle, 2026-03-03; consolidated 2026-10-27)"; "Ported to this pin on 2026-10-28 with fourteen mechanical changes inside proofs (API renames, deprecated tactics, one import); no definition and no statement changed."
- NOTICE lists "the port of the Sturm–Liouville file" among the items "written with Claude Code (Anthropic) under Joey's direction".
- README, "Who did what": "The Sturm–Liouville file is co-authored by Aristotle (Harmonic); see NOTICE."
- The sources identify the co-author only as "Aristotle (Harmonic)" and do not describe the tool or divide the work between it and the author further.

Prior formalizations, as MAP states it (section 1): "as a formalization, no completed Lean proof
of this result is known to the depositor as of 2026-11-03, after searching Mathlib master (no
Sturm–Liouville, Schrödinger or function-Wronskian material), the Palomar registry, and GitHub
(atlas-lean has a Dirichlet existence theorem on [0,1]; math-physics-lab states simplicity on a
compact interval with the proof left `sorry`)". This is the depositor's statement; this sheet did
not repeat the search, and the paper may use the hedged sentence only if
`WORK/facts/literature.md` supports it (that file did not exist when this sheet was written).

Afterlife (MAP section 10; README line 176): "The Sturm–Liouville file of add-on v3 lives on as
the standalone project github.com/Joeyxyxyz/sturm-liouville-comparator-run (simplicity plus the
first oscillation step, Comparator-accepted 2026-11-03 ...)"; README: "accepted again on
2026-11-03, Lean kernel and NanoDa". That project is outside the eleven runs.

How the library uses it: only through `Schrodinger.lean` (section 5), where it shows that the
levels of a hypothetical realization are simple eigenvalues. It was not judged in run 6.

## 7. What is open, register [OPEN] (MAP section 4)

MAP section 4 lists six items; quotes are exact.

1. The gap hypothesis: "`SpectralGapHyp Δ` for any Δ > 0. For Δ > 3/8 it is RH (§2); for every Δ it is, kernel-checked (`spectralGapHyp_iff_zeroFree_strip`, §1), the zero-free strip 1/2 < Re ρ < 1/2 + Δ next to the line, not known for any Δ > 0. No source in the corpus, the hackathon, or the qexp package supplies an argument for it."
2. Simplicity: "`AllZerosSimple` / `MultiplicityBoundOne` (the simple-zeros conjecture). Nothing in the corpus bears on it: all threshold, Bloch-length and residue quantities are real-valued in [0,1], while multiplicity is an integer ≥ 1 with no gap structure to exploit."
3. "`SpeiserTheorem` [LITERATURE, Speiser 1934]: not in Mathlib; kept as a named hypothesis."
4. "`BohrLandau` and `NcountSuperlinear` [LITERATURE as of 2026-10-29]: no longer open on the zeta23 tree. `NcountSuperlinear` is proved there from zeta23's Riemann–von Mangoldt formula (`MNF.RH.ncountSuperlinear`, receipt v2 of §10) and `BohrLandau` is proved there outright (`Zeta23.BL.bohrLandau_full`, receipt v4 of §10). On the OpenAI tree (GapDensity.lean, add-on v3 of 2026-10-29) they remain named hypotheses; that file is frozen with its receipt." (In the run numbering: "receipt v2 of §10" is run 7 and "receipt v4" is run 9, by MAP's section 10 table.)
5. "`SchrodingerRealization` [OPEN]: an explicit confining `V`; the Berry–Keating / Connes programmes aim at exactly this and none is a theorem. `GapMechanism Δ` [OPEN] is ⟺ the band, hence ⟺ RH for Δ > 3/8."
6. The operator realization: "a symmetric operator whose eigenvalues are (ρ − 1/2)/i. `rh_of_symmetric_operator` (Hypotheses.lean) shows the implication to RH is immediate once such an operator is given, so this route has no content short of constructing the operator." MAP adds that the corpus's Sturm–Liouville bridge to it "is vacuous as written: the first concludes `… → True`, the second quantifies over a `Classical.choice` placeholder eigenfunction. Neither is deposited as a theorem about ζ."

RH itself is open and is not claimed anywhere: LIB3, "The Riemann Hypothesis is not among the theorems."

## 8. What was withdrawn and why, register [WITHDRAWN] (MAP section 5)

"Corpus" is the author's earlier collection of Lean files ("output28–86" and others, MAP line 5
and section 7), which the consolidated library "replaces ... for deposit purposes". Five items.

1. An axiom about double zeros. MAP: "output83 `axiom argument_principle_double_zero_forces_left_strip_zero` (cited to Levinson–Montgomery 1974). Together with Speiser it would give RH ⟹ all zeros simple, which is not a known theorem; a multiple zero on the line is a zero of ζ' **on** the line, which Speiser does not forbid. The citation does not support the axiom." Consequence: "output83's `rh_implies_all_simple`, `multiple_zero_kills_gap`, `fischer_forward_speiser_path` and the "capstone" `rh_and_all_zeros_simple_speiser_path` are withdrawn; the argument survives only in the explicit conditional form `allZerosSimple_of_speiser_and_double_zero_hyp`." In the library the former axiom is the hypothesis `DoubleZeroForcesLeftDerivZero`, register "[UNSUPPORTED]" (`Hypotheses.lean` header).
2. A false axiom for $\zeta'$. MAP: "output86 `axiom func_eq_deriv` (ζ'(1−s) = −F(s)ζ'(s) for all s in the strip): false as stated (the product rule has a ζ(s)·F'(s) term); replaced by the proved `deriv_reflect` at zeros. output86's `rh_and_speiser_implies_simple` contained a `sorry` and is withdrawn." `Hypotheses.lean` header gives the reason for the second: "Speiser's theorem concerns ζ' off the line and says nothing about the multiplicity of zeros on it, so RH ∧ Speiser → AllZerosSimple is not a theorem."
3. Statements over placeholder functions. MAP: "output40 / output66–70 (GUE): `riemann_von_mangoldt_stmt`, `montgomery_pair_correlation_stmt`, `zero_multiplicity_bound_stmt` and `ZeroDensityControl` are stated over placeholder functions (`N_count`, `pair_corr_stat := Classical.choice ⟨…⟩`) that are not the zero-counting function or the pair-correlation statistic of ζ. As the corpus's own stub 3 notes, one earlier "proof" exploited this vacuity. These statements say nothing about ζ and are not deposited."
4. Former hypotheses that are now theorems. MAP: "The corpus's `Bridge` hypothesis (output71/72) and `level1_stmt` (output40): no longer hypotheses; proved (§1)." (`Bridge` is `riemannHypothesis_iff_strip` / `riemannHypothesis_iff_shifted_subset_zero`, section 3.3.)
5. A description withdrawn. MAP: ""SpectralGap(1/2) is a physical input" (output40 inventory): under §1 it is RH verbatim, so it cannot be described as an input weaker than RH."

The pattern MAP asks to check in the rest of the corpus (section 7): "a hypothesis typed as
`True`, a `Classical.choice` placeholder standing in for a real function, or a conclusion of the
form `… → True`."

## 9. "What the deposit can claim" (MAP section 6), summarized

MAP section 6 has four numbered items.

1. A re-check of OpenAI's theorem: "An independent Comparator verification of OpenAI's 7/8 zero-free-region theorem (RECEIPT.md), with the MNF bridge compiled on top (BRIDGE.md)." (Framing rule 2 applies: README says "Not a first verification of either external result: both authors report Comparator runs of their own; these are repetitions by a second party".)
2. A kernel-checked library: "establishing that the MNF gap hypothesis is equivalent to RH for every Δ > 3/8 and insufficient for every Δ ≤ 3/8, and (v2) that at every Δ it is exactly a zero-free strip next to the critical line; the multiplicity lemmas; the functional-equation symmetry of multiplicities; and the exact relation between Mathlib's `RiemannHypothesis` and the strip form." On definitions: "the v2 run lists no holes, so it is the run in which the definition bodies were compared by Comparator (before it, they were attested by the verbatim copy in the challenge and by the audit compile)."
3. The limit: "Not RH, not simplicity, and no new technique toward either. The honest one-line summary: *the nullification framework re-expresses RH; it does not reduce it.*"
4. Added 2026-11-03/04, about the later runs: "On the zeta23 tree: the density field formalized and kernel-checked; Bohr–Landau (1914) formalized from Mathlib and the tree's own approximate formula, so that the density-one theorem has exactly one hypothesis left, the gap; the MNF2 injection/ejection algebra and the strip model as proved bookkeeping; and the Sturm–Liouville simplicity theorem with its first oscillation step as a standalone Lake project (github.com/Joeyxyxyz/sturm-liouville-comparator-run). None of this bears on `SpectralGapHyp`, which is unchanged: RH for Δ ≥ 1/2, an open zero-free strip for 0 < Δ < 1/2."

The equivalence in item 2 for $\Delta>\tfrac38$ depends on OpenAI's theorem (section 4); for
"insufficient" see the caution in section 4.1.

## 10. zeta23's Theorems A to D restated over MNF's definitions (run 6)

File: `Z23/MNF/RH/Zeta23Restated.lean` (sha256 in REP6:
`441912f9657657606c323c609e533471526a95fe71a2372fbbc1ef586c9258aa  MNF/RH/Zeta23Restated.lean`).
It imports `MNF.RH.Counting` and zeta23's `Solution`. Register: "[RESTATEMENT | zeta23] for every
theorem in this file, §5 included" (file header).

The thirteen statements, as printed by Lean (REP6, block "What was proved"):

```lean
MNF.RH.twoThirdsOnLine (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.N0star T (2 * T))
MNF.RH.twoThirdsOnLine_cumulative (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0star 0 T)
MNF.RH.twoThirdsSimpleOnLine (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.N0simple T (2 * T))
MNF.RH.twoThirdsSimpleOnLine_cumulative (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0simple 0 T)
MNF.RH.fiveSixthsDistinct (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (5 / 6 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.Ndist T (2 * T))
MNF.RH.fiveSixthsDistinct_cumulative (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (5 / 6 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.Ndist 0 T)
MNF.RH.montgomeryTaylorOnLine (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 - 1 / MNF.RH.cMT - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.N0star T (2 * T))
MNF.RH.montgomeryTaylorSimpleOnLine (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 - 1 / MNF.RH.cMT - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.N0simple T (2 * T))
MNF.RH.montgomeryTaylorSimpleOnLine_cumulative (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (2 - 1 / MNF.RH.cMT - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0simple 0 T)
MNF.RH.montgomeryTaylorDistinct (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (3 / 2 - MNF.RH.cMT⁻¹ / 2 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.Ndist T (2 * T))
MNF.RH.montgomeryTaylorDistinct_cumulative (ε : ℝ) :
  ε > 0 → ∃ T₀, ∀ T ≥ T₀, (3 / 2 - MNF.RH.cMT⁻¹ / 2 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.Ndist 0 T)
MNF.RH.twoThirdsOnLineDerivNeZero (ε : ℝ) :
  ε > 0 →
    ∃ T₀,
      ∀ T ≥ T₀,
        (2 / 3 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤
          ↑(MNF.RH.zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | deriv riemannZeta ρ ≠ 0}).ncard
MNF.RH.fiveSixthsDistinct_sandwich (ε : ℝ) :
  ε > 0 →
    ∃ T₀,
      ∀ T ≥ T₀,
        (5 / 6 - ε) * ↑(MNF.RH.Ncount T (2 * T)) ≤ ↑(MNF.RH.Ndist T (2 * T)) ∧
          ↑(MNF.RH.Ndist T (2 * T)) ≤ ↑(MNF.RH.Ncount T (2 * T))
```

| zeta23 theorem (label in its challenge) | zeta23 name delegated to | MNF name | reading: for every $\varepsilon>0$ and all $T\ge T_0(\varepsilon)$ |
|---|---|---|---|
| A, dyadic | `two_thirds_on_critical_line` | `twoThirdsOnLine` | $(\tfrac23-\varepsilon)N(T,2T)\le N_0^*(T,2T)$ |
| A, cumulative | `two_thirds_on_critical_line_cumulative` | `twoThirdsOnLine_cumulative` | $(\tfrac23-\varepsilon)N(0,T)\le N_0^*(0,T)$ |
| B, dyadic | `two_thirds_simple_on_critical_line` | `twoThirdsSimpleOnLine` | $(\tfrac23-\varepsilon)N(T,2T)\le N_0^s(T,2T)$ |
| B, cumulative | `two_thirds_simple_on_critical_line_cumulative` | `twoThirdsSimpleOnLine_cumulative` | $(\tfrac23-\varepsilon)N(0,T)\le N_0^s(0,T)$ |
| C, dyadic | `five_sixths_distinct` | `fiveSixthsDistinct` | $(\tfrac56-\varepsilon)N(T,2T)\le N_d(T,2T)$ |
| C, cumulative | `five_sixths_distinct_cumulative` | `fiveSixthsDistinct_cumulative` | $(\tfrac56-\varepsilon)N(0,T)\le N_d(0,T)$ |
| D, on-line, dyadic | `montgomery_taylor_on_critical_line` | `montgomeryTaylorOnLine` | $(2-1/c_1^*-\varepsilon)N(T,2T)\le N_0^*(T,2T)$ |
| D, simple, dyadic | `montgomery_taylor_simple_on_critical_line_mult` | `montgomeryTaylorSimpleOnLine` | $(2-1/c_1^*-\varepsilon)N(T,2T)\le N_0^s(T,2T)$ |
| D, simple, cumulative | `montgomery_taylor_simple_on_critical_line_mult_cumulative` | `montgomeryTaylorSimpleOnLine_cumulative` | $(2-1/c_1^*-\varepsilon)N(0,T)\le N_0^s(0,T)$ |
| D, distinct, dyadic | `montgomery_taylor_distinct_mult` | `montgomeryTaylorDistinct` | $(\tfrac32-\tfrac{1}{2c_1^*}-\varepsilon)N(T,2T)\le N_d(T,2T)$ |
| D, distinct, cumulative | `montgomery_taylor_distinct_mult_cumulative` | `montgomeryTaylorDistinct_cumulative` | $(\tfrac32-\tfrac{1}{2c_1^*}-\varepsilon)N(0,T)\le N_d(0,T)$ |
| (rewrite of B) | via `N0simple_eq_deriv_form` | `twoThirdsOnLineDerivNeZero` | $(\tfrac23-\varepsilon)N(T,2T)\le\#\{\rho\text{ in the window}:\beta=\tfrac12,\ \zeta'(\rho)\ne0\}$ |
| (rewrite of C) | with `Ndist_le_Ncount` | `fiveSixthsDistinct_sandwich` | $(\tfrac56-\varepsilon)N(T,2T)\le N_d(T,2T)\le N(T,2T)$ |

Here $N$ counts with multiplicity and $N_0^*,N_0^s,N_d$ count distinct points (section 2.4).
REP6: "They assert proportions of zeros in windows (T, 2T] and (0, T] for large T, counted with
multiplicity on the left and as distinct points on the right." The delegation names are from the
source (`Zeta23Restated.lean`, lines 72-144, for example "theorem twoThirdsOnLine : ... :=
_root_.two_thirds_on_critical_line"); the theorem labels A to D are those of Anthropic's
challenge as quoted in REC2 ("**Theorem A — at least 2/3 of the nontrivial zeros of ζ lie on the
critical line**", "**Theorem B**: at least 2/3 of the nontrivial zeros of ζ are *simple and* on
the critical line", "**Theorem C**: at least 5/6 of the nontrivial zeros of ζ are distinct",
"**Theorem D — the optimal (Montgomery–Taylor) window**").

Facts about the layer.

- How the proofs work: "Every theorem of §1–§4 is proved by DELEGATION to the corresponding root-namespace theorem of zeta23's Solution.lean. MNF's counting definitions are spelled character-for-character as zeta23's (ChallengeDeps.lean §1, §3) with `IsNontrivialZero` replaced by `is_nontrivial_zero` and `zeroMult` by `zeta_order`, whose bodies are in turn identical; so each delegation typechecks by definitional unfolding in the kernel. ... No new mathematics is proved in this file." (file header)
- Coverage: eleven of zeta23's seventeen statements. "This file restates the eleven ζ-theorems of the zeta23 comparator challenge ... NOT the six Dirichlet-character statements of Theorem E, for which MNF has no vocabulary" (file header). MAP section 8: "The six Dirichlet statements of zeta23 are not restated."
- Reliability: "Each theorem of §1–§4 is zeta23's theorem under a change of names that the kernel verifies by unfolding, so it carries zeta23's status and nothing more" (file header). REP6: "they hold by definitional unfolding and are exactly as reliable as the zeta23 receipt."
- The two rewrites: "Theorem B with `ζ' ≠ 0` in place of `zeta_order = 1`" and "Theorem C together with the trivial `Ndist ≤ Ncount`" (file header). The first "says nothing about `DerivativeNonvanishing`, which quantifies over every zero" (docstring).
- What the layer does not do. File header: "A proportion of zeros, however large, is not a statement about every zero. Nothing in this file discharges, weakens, or bears on `SpectralGapHyp`, `AllZerosSimple`, `MultiplicityBoundOne`, or `DerivativeNonvanishing` ... Nothing here advances RH or the simple-zeros conjecture. These theorems do not use the 7/8 theorem, and must not be combined with it in one sentence". MAP section 8: "What the two external results do not do together: nothing. The 7/8 theorem bounds how far from the line a zero can sit; zeta23 bounds what proportion of zeros sit on it; neither input enters the other's proof, and a sentence that puts "2/3" and "7/8" together as one theorem would be false advertising."
- The rest of run 6: "the 36 Mathlib-only statements of the MNF library (Core, Gap, Hypotheses, byte-identical to add-on v2), `MNF/RH/Counting.lean` ..., and `MNF/RH/Zeta23Restated.lean`" (MAP section 8, "The restatement layer (B2, 2026-10-29 UTC)"). So Core, Gap and Hypotheses were judged at two pins: Lean v4.34.1 with Mathlib `d13f23b7` (runs 3 to 5) and Lean v4.33.0-rc2 with Mathlib `51e6992e` (run 6); `Z23/README.md`: "They compile unchanged at zeta23's pin."
- Warm and cold: the run reused the compiled Zeta23 library of run 2 ("warm with respect to the Zeta23 library by design (its oleans come from the accepted first run ...); the MNF layer and the challenge are cold", `Z23/README.md`; FACTS6 "attempt_started_zeta23-mnf	warm").
- Review before the run (`Z23/README.md`): "three independent reviewers (vacuity, faithfulness and format, overclaim) found no vacuous statement; every count threads the finiteness lemma; the definitions match zeta23's character for character up to the two renamed constants." NOTICE calls these "independent model reviewers".
- "More than two thirds": the constant in A and B is $\tfrac23-\varepsilon$; the strict excess over $\tfrac23$ comes from Theorem D's $2-1/c_1^*$, whose decimal value (0.67250…) is in docstrings only (section 2.4).

## 11. Disagreements and cautions found while reading

1. Order of runs 5 and 6: by the receipts' timestamps run 6 preceded run 5 on 2026-10-29 (section 1). No source contradicts another; the numbering is simply not chronological.
2. "Insufficient for Δ ≤ 3/8": MAP section 6, LIB3 and README say a gap at $\Delta\le\tfrac38$ "cannot give" RH and cite `gap_below_bound_insufficient`. The Lean statement is for $0<\Delta<b$ strictly and for abstract symmetric sets of reals (section 4.1). The receipt's printed statement governs; the paper should say that the squeeze argument does not close below the bound, not that the gap at small $\Delta$ is known not to imply RH.
3. LIB3's "How to read this" block is inherited from v2. It says "the theorems whose names end in `_seven_eighths` / `_three_eighths` (`Unconditional.lean`) use OpenAI's theorem"; seven of the eight names in `Unconditional.lean` end that way, one (`spectralGapHyp_three_eighths_iff`) ends in `_iff`, and the Mathlib-only `spectralGapHyp_three_eighths_iff_of` of `Hypotheses.lean` also contains `three_eighths`. The block also does not mention the five files added in v3. The file of each theorem (section 1 counts, section 4 list) is the reliable criterion.
4. MAP's section headings name fewer files than their tables cover (sections 1 and 3; noted in sections 3 and 5 above). `rh_of_gap_three_eighths` appears in MAP sections 2 and 3.
5. `symmetric_bounded_not_on_line`: the docstring speaks of three structural inputs including conjugation symmetry; the checked statement has two hypotheses (reflection, bound).
6. `V3/README.md` describes the Sturm–Liouville port as "fourteen mechanical changes inside proofs (API renames, deprecated tactics, one import)"; an import is not inside a proof. NOTICE says "proof-internal changes only". Both agree that "no definition and no statement changed".
7. Three different on-line counts (`N0star`, `N0simple`, `N0`) and the paper's single symbol $N_0(T)$: see section 2.4.
8. Two different constants named `nullify`, and two pairs of probes, exist in the record (`MNF.RH.*` here, `MNF.Extension.*` from run 7); see section 2.2.

No disagreement was found between a receipt and a source file on any number, date, hash or
statement checked for this sheet (theorem and definition counts recounted from the challenge
files; file hashes of Core and Counting compared across LIB3 and REP6; start and end times
compared with MAP).

## 12. Authorship of the files judged in runs 3 to 6

- NOTICE, "Authorship of the Lean files in the add-on tarballs": "MNF/RH/Core.lean, Gap.lean, Hypotheses.lean, Unconditional.lean, Reduction.lean, Schrodinger.lean: the Messina Nullification Framework corpus (Joey Messina), consolidated 2026-10-27/28; the Comparator add-on scripts and the additions of 2026-10-28/29 (Counting.lean, Zeta23Restated.lean, GapDensity.lean, the three spectral-gap theorems of v2, the Prop forms of GapMechanism and SchrodingerRealization, the port of the Sturm–Liouville file) were written with Claude Code (Anthropic) under Joey's direction and reviewed by independent model reviewers before each Comparator run; every theorem is kernel-checked."
- README, "Who did what": "Joey Messina: the MNF corpus and library, the protocol, operation of every run, and the decisions recorded in DEPOSIT_MAP.md. OpenAI and Anthropic: the theorems under test, which are theirs and are credited as such. The kit and add-on scripts, the Lean additions of 2026-10-28/29 and these documents were produced with Claude Code (Anthropic) under Joey's direction; every theorem was kernel-checked and every claim here is tied to a receipt."
- Sturm–Liouville file: section 6.
- Provenance inside the library, from `Core.lean`'s header: "§2–§3 restate, with fresh proofs, the lemmas the corpus files output71_minimal_axiom / output79 / output84 proved at the corpus pin ... §4 proves what output86 assumed as the axiom `func_eq_deriv` (here only at zeros, which is where it is true) ... §5 proves what output71/72 assumed as the `Bridge` hypothesis". MAP's section 1 table has a "corpus origin" column per theorem (for example "new (hackathon scan item 4)", "the corpus "master theorem" (output72), now unconditional").
- The external theorems used: OpenAI's `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (runs 3 to 5, once) and Anthropic's zeta23 `Solution` theorems (run 6, by delegation); NOTICE: "openai/math ... Apache-2.0   OpenAI (artifact under test)", "anthropics/formal-math ... Apache-2.0   Anthropic, PBC (artifact under test)".

## 13. Remaining parts of MAP sections 7 to 9 (for completeness)

- Section 7 is an inventory of the rest of the corpus, "not re-examined here": "Of the 241 project documents, the RH line consolidated above is: ..."; "Everything those files prove about ζ that survives is in §1–§3; what does not is in §5."; the non-RH groups "belong to Zenodo Vol 1 (operator core) and Vol 3 (physical applications) and are outside this deposit."
- Section 8 registers the two external results with pins and says for zeta23: "It discharges none of `SpectralGapHyp Δ`, `AllZerosSimple`, `MultiplicityBoundOne`, `DerivativeNonvanishing`: a proportion of zeros, however large, is not a statement about every zero." It also lists zero-free half-planes left of 7/8 read on 2026-10-28 ("none run here ... none is used here") and notes that any of them "instantiates `riemannHypothesis_iff_gap_of_zeroFree` and `riemannHypothesis_iff_remaining_strip` verbatim at its θ, with `θ − 1/2` in place of `3/8`".
- Section 9, the "frontier package" (the author's name for `Reduction.lean` and `Schrodinger.lean`): they "rewrite every "attack" idea of the corpus as an `↔` or a named `Prop`, so the remaining content is a Lean goal: the band `1/2 < Re ρ ≤ 7/8` on one side (`rh_of_band_seven_eighths`), or a `SchrodingerRealization`. Nothing in them proves RH or the simple-zeros conjecture, and `multipleZeroKillsGap_iff` / `fischerForward_iff` show that the February "Fischer forward" chain is `RH ∧ (RH → simple) → RH ∧ simple`."
- Section 9 also records a quantum-hardware experiment of February 2026 on a lattice gauge model and states that, because the accompanying Lean hypotheses are each equivalent to "RH ⟹ all zeros simple", "the experiment is **not** evidence for or against RH and is not cited as such."

## 14. Open questions for the paper

1. Authorship wording for runs 3 to 6. Framing rule 7 speaks of "the Lean files of runs 7 to 11". For runs 3 to 6 NOTICE attributes six files to "the Messina Nullification Framework corpus (Joey Messina), consolidated 2026-10-27/28" and names specific later additions as written with Claude Code. No source read here says which tool, if any, drafted the consolidation of 2026-10-27/28 (the "fresh proofs" of `Core.lean`) or the original corpus lemmas; the paper should either quote NOTICE as it stands or the author should supply the missing statement.
2. Division of work in the Sturm–Liouville file between Aristotle (Harmonic) and the author: the sources say only "co-authored" and "consolidated by Joey".
3. The sentence "the author is not aware of a prior Lean formalization" for the Sturm–Liouville simplicity theorem: MAP supports it as the depositor's statement dated 2026-11-03; `WORK/facts/literature.md` did not exist when this sheet was written, so framing rule 8 is not yet satisfied.
4. Whether the paper should present `gap_below_bound_insufficient` as in section 4.1 (a statement about abstract sets) and reword MAP's "insufficient for every Δ ≤ 3/8" accordingly; MAP's wording is declared authoritative for framing, but the Lean statement is narrower.
5. Which on-line count the paper's $N_0(T)$ denotes (distinct, simple, or with multiplicity); the three Lean functions are used in different theorems.
6. Whether to mention MAP section 9's lattice experiment at all; it is outside mathematics and MAP itself says it is not evidence about RH.
7. Literature keys: Speiser (1934), Bohr–Landau (1914), Levinson–Montgomery (1974), Montgomery (1973), Berry–Keating, Connes, Coddington–Levinson, Teschl, Berezin–Shubin are named in the sources read here without bibliographic detail; none was checked against a web page for this sheet.
8. This sheet did not open Mathlib to quote the definition of `RiemannHypothesis`; its shape (zeros other than the trivial ones $-2(n+1)$ and other than $s=1$ have real part $\tfrac12$) is inferred from the hypotheses of `in_strip_of_zero` and the proof of `riemannHypothesis_iff_strip`.
