# Review of WORK/paper.md: Lean fidelity

Reviewer lens: every Lean statement and every plain-mathematics rendering of a theorem, checked
against the Lean sources (REPO/sources/qrh-zeta23-addon-v6, REPO/sources/qrh-mnf-addon-v3) and
against Lean's printed statements in the receipt bundles (WORK/extracted). The paper was not edited.
Paths: V6 = REPO/sources/qrh-zeta23-addon-v6, V3 = REPO/sources/qrh-mnf-addon-v3,
R11 = WORK/extracted/qrh-zeta23-density-v6-receipt/density-v6, MAP = REPO/DEPOSIT_MAP.md.

## What was checked and found correct

- The sources read are the judged ones: the 23 Lean files of V6 and the 9 of V3 re-hash to the
  values in R11/density_sha256.txt and in the run 5 bundle's library_sha256.txt (sha256sum -c: 23 OK, 9 OK).
- All 17 Lean code blocks (23 statements) are verbatim: run 1 RECEIPT.md, run 5 MNF_LIBRARY.md,
  R11/MNF_DENSITY.md or R11/audit.out, and V6 Density.lean / GapDensity.lean for the three `def`s.
- Every Lean name in the paper exists. Every lemma of the layer that the paper names is in the
  claim set of the run the paper gives for it (axiom lines of the nine audit.out files); the
  "Run" column of Appendix B is the first run whose audit lists the name, for the 27 rows of runs
  3 to 11 (rows 1 and 2 are the theorems of the receipts of runs 1 and 2).
  Names of Anthropic's tree (`Zeta0EqZeta`, `Zeta23.MV.mvDiag_thirteen`, `riemannVonMangoldt_zeta`)
  are presented as the tree's, and `Zeta23.BL.bohrLandau` (sorry-dependent) as outside every claim set.
- Plain renderings agree with Lean in hypotheses, quantifier order, ranges and constants for:
  the OpenAI statement; `two_thirds_simple_on_critical_line`; the gap/strip/RH equivalences
  (every real Delta; Delta >= 1/2; Delta > 3/8; the case 3/8); `on_line_density_one_of_gap`;
  the Sturm-Liouville statement and its three definitions; `BohrLandau`, `NcountSuperlinear`,
  `ReservoirDensityOne`, `OnLineDensityOne`; `offLine_le_one_third`; `bohrLandau_full`,
  `bohrLandau_gt_sixth`, `bohrLandau_explicit` (A, B >= 0, 0 < delta <= 1/2, T >= 2, real exponent -5/2);
  steps 1 to 7 of the architecture (`zeta_eq_euler_maclaurin`, `tail_by_parts`, `B2per_fourier`,
  `first_derivative_test_amp_smooth'`, `tail_mode_bound'`, `zeta_approx_sharp`,
  `M1.dirichlet_meanSquare_le` with the constant 26, `meanSquareUnif_all`, `geom_facts`,
  `count_le_integral`, `rightHalf_of_meanSquareUnif`, `rightHalf_all` with sigma_1 = 1/2 + delta/2);
  `M3.meanSquareUnif_explicit` (2/3 <= sigma_1 < 1, N = floor(T^(3/2)) + 1); `density_single_window`
  (strict sigma_1 - 1/2 < delta <= 1/2, T >= 2, real power of T, cube of 1 + log T) and the six
  proof steps (pi^2/(3X) for X >= 4, c_m for m <= X <= N, the divisor bound, X = floor(T^theta),
  N = ceil(T) + 5, eps^2 = 1/X); the three displacement statements (the exponents 3/5 and -2/5
  are real powers in the source); the pair sum, its marginals, `coincidentMass_eq`,
  `offDiagonalCoincidentMass_le` and the constants 5/9 and 2/3 (the 10 > 8 counterexample recomputed);
  `Degenerate`, `bandZeros`, `OrdinatesInjectiveOn`, `bandCoincidentMass` and the three equivalences;
  the real-zero theorem and its one-term Euler-Maclaurin identity.
- Conditional results are stated as conditional on the right hypotheses; existential constants are
  said to be existential; the two-sided density estimate and Carlson's exponent are said not to be proved.
- The counts 255 printed / 279 omitted of 534 (run 11) hold, and the same split holds in runs 7 to 10
  (106+18, 144+126, 171+163, 218+262).

## Findings

### 1. MAJOR. Appendix B: three rows tagged "from Mathlib alone" depend on Anthropic's library

Location: Appendix B, header "[PROVED], from Mathlib alone" and the rows
`MNF.RH.noDegenerate_iff` ("[PROVED] bookkeeping; an equivalence"),
`MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros` and
`MNF.RH.spectralGapHyp_iff_bandCoincidentMass` ("[PROVED] an equivalence").

Problem: by the paper's own definition these three are not [PROVED]. Their proofs use the zeta23
library's reflection lemma, and the third also the real-zero theorem, which the same table tags
[PROVED | this tree] and which rests on the tree's `Zeta0EqZeta`. The body says so itself ("the
third also needs that no nontrivial zero is real"). The tag is copied from the register, whose
own definition of [PROVED] it contradicts.

Evidence:
- V6/MNF/RH/Cube.lean lines 173-175: "lemma is_nontrivial_zero_mirror {ρ : ℂ} (hz : is_nontrivial_zero ρ) : is_nontrivial_zero (mirror ρ) := Zeta23.zetaZeroConfig.reflect_mem ρ hz";
  line 253 (in `degenerate_of_not_onLine`, used by `noDegenerate_iff`): "refine ⟨mirror ρ, is_nontrivial_zero_mirror hz, ?_, mirror_im ρ⟩";
  line 242 (in `mem_bandZeros_mirror`, used by the second equivalence): "refine ⟨is_nontrivial_zero_mirror hz, ?_⟩";
  lines 486-488: "theorem spectralGapHyp_iff_bandCoincidentMass (Δ : ℝ) : ... := spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero nontrivial_zero_im_ne_zero Δ";
  line 452: "rw [← Zeta0EqZeta (N := 1) one_pos hre hs1]".
- Cube.lean header: "[BOOKKEEPING] + [PROVED | this tree] Register: every declaration below is proved from Mathlib and the tree's sorry-free files".
- MAP: "**[PROVED]** kernel-checked from Mathlib alone".

Fix: tag the three rows "[PROVED \| this tree]; an equivalence" and add to the header of Appendix B:
"For the three equivalences of `Cube.lean` the register prints [PROVED]; they are tagged
[PROVED \| this tree] here, because their proofs use the reflection lemma
`zetaZeroConfig.reflect_mem` of the zeta23 library, and the third also the real-zero theorem."
In *Degenerate zeros and two equivalences* replace "The proofs use the reflection symmetry and
elementary logic" by "The proofs use the reflection symmetry of the zeros, taken from the zeta23
library (`zetaZeroConfig.reflect_mem`), and elementary logic".

### 2. minor. Architecture: the list of what the proof takes from the tree omits the reflection lemmas

Location: *Architecture of the formal proof*, "From the tree the proof takes the approximate
formula `Zeta0EqZeta`, a port from the PrimeNumberTheoremAnd project".

Problem: step 7 (reflection, with multiplicity) is not proved in the layer or from Mathlib; it
uses two lemmas of Anthropic's library. The enumeration reads as complete and names three inputs.

Evidence: V6/Zeta23/BohrLandau.lean line 40 "have hm := zetaZeroConfig.reflect_mem ρ hz", line 50
"exact (zetaZeroConfig.mult_reflect ρ hz).symm"; V6/MNF/RH/Density.lean line 278-279 "Delegated to
`Zeta23.BL.NLeft_eq_NRight`, whose proof uses zeta23's `zetaZeroConfig.reflect_mem` and `mult_reflect`."

Fix: "... the weighted Hilbert inequality `Zeta23.MV.mvDiag_thirteen` [@montgomery-vaughan-1974],
the lower bound $\lvert\zeta(2+it)\rvert\ge1/3$ and, for step 7, the reflection symmetry of the
zeros with multiplicity (`zetaZeroConfig.reflect_mem`, `zetaZeroConfig.mult_reflect`); from Mathlib ..."

### 3. minor. Appendix B: "[PROVED | this tree] ... the sorry-free files of that tree"

Location: Appendix B, "[PROVED \| this tree], on the zeta23 checkout, from Mathlib and the
sorry-free files of that tree".

Problem: the paraphrase drops the register's parenthesis "(zeta23's own library, receipted in run
2)". As printed it says every file used is sorry-free, but `Zeta23.BL.bohrLandau_full` is proved
through `bohrLandau_of_right`, `NRight` and `RightHalfBound` of `Zeta23/BohrLandau.lean`, the
supporting file that holds the two `sorry` lemmas.

Evidence: V6/Zeta23/BL/BohrLandauClosure.lean line 52 "import Zeta23.BohrLandau", line 1226
"theorem bohrLandau_full : MNF.RH.BohrLandau := bohrLandau_of_right rightHalfBound", header lines
45-47 "`Zeta23.BohrLandau` is imported for the definitions `NRight`, `RightHalfBound`,
`ZetaMeanSquare` and the sorry-free reduction `bohrLandau_of_right`; its sorried declarations are
used by nothing here."; V6/Zeta23/BohrLandau.lean lines 100 and 108 "sorry"; MAP line 296-297.

Fix: "[PROVED \| this tree], on the zeta23 checkout, from Mathlib, the zeta23 library and
sorry-free declarations of the layer (the supporting file `Zeta23/BohrLandau.lean` also holds two
`sorry` lemmas, on which no claimed theorem depends: every axiom report lists only the three
standard axioms)".

### 4. minor. Appendix B: the "Run" of the two gap equivalences of run 3

Location: Appendix B, "\"Run\" is the first run that judged the statement."

Problem: for `riemannHypothesis_iff_gap_half` and `riemannHypothesis_iff_gap_three_eighths` the
column says 3, but in run 3 `SpectralGapHyp`, `SpectralGapProperty` and `ShiftedZeroSpectrum` were
holes, compared by name and type only; the statement with definition bodies was first judged in
run 4. The body of the paper says this; the table, read alone, does not.

Evidence: MAP lines 143-146 "The v1 run (2026-10-28, ACCEPTED) compared the 40 statements but
listed the 17 definitions as holes, which Comparator compares by name, type and universe levels
only; the v2 run lists no holes, so it is the run in which the definition bodies were compared";
run 3 MNF_LIBRARY.md "40 theorems, 17 definitions named in the challenge config".

Fix: add after that sentence: "For the two rows of run 3 that mention the gap hypothesis, run 3
compared the library's definitions as holes; their bodies were first compared in run 4."

### 5. minor. "The second threshold is exact"

Location: *The MNF.RH library in standard terms*, "The second threshold is exact: by
`spectralGapHyp_three_eighths_iff`".

Problem: no Lean statement says that RH and $G(3/8)$ are not equivalent (if RH holds, both hold).
What is proved is the form of $G(3/8)$; "exact" can only mean that the argument does not reach 3/8.

Evidence: V3/MNF/RH/Unconditional.lean lines 51-52 "The boundary case: a gap at exactly `Δ = 3/8` ⟺
every nontrivial zero has real part `1/2`, `1/8` or `7/8`. Not RH (zeros on `Re s = 7/8` are not
excluded by the 7/8 theorem)."; WORK/facts/mnf.md section 11 item 2.

Fix: "At the threshold itself the statement changes form: by `spectralGapHyp_three_eighths_iff`
(`[PROVED | 7/8]`), $G(3/8)$ holds if and only if every nontrivial zero has
$\beta\in\{1/2,1/8,7/8\}$; this argument does not give RH at $\Delta=3/8$, because OpenAI's theorem
leaves the line $\operatorname{Re}s=7/8$ open."

### 6. minor. Lessons learned: two reasons given for the 29 exclusions, the sources give three

Location: *Lessons learned*, "A claimed statement may mention neither a zeta23-internal name,
which a mirror does not import, nor a constant fixed by `Classical.choose`."

Problem: some of the 27 (`NOff_eq_sum_ite`, `NOff_real_eq_sum_indicator`) and one of the 2
(`aux_pairSum_eq_finset_sum`) are excluded for the third reason, a finiteness proof used as a term.
Thirteen `aux_` lemmas of `InjectionEjection.lean` are also mirrored but not claimed.

Evidence: V6/README.md lines 39-43 "The 27 declarations of `ReservoirMass.lean` whose statements
mention zeta23-internal names (`Zeta23.Ncount`, `ell1`, `reflect`, the `Classical.choose`
constants) or a finiteness proof as a term are not in the claim set either ... Two `aux_` lemmas of
`Cube.lean` (statements naming `Zeta23.reflect` or a finiteness proof term) are likewise outside the
claim set."; V6/scripts/z23_gen_density_challenge.py line 112 "if \"private\" not in d.group(\"mod\")
and not d.group(\"name\").startswith(\"aux_\"):"; V6/MNF/Extension/InjectionEjection.lean has 69
theorems, 13 named `aux_*`, 56 claimed.

Fix: "A claimed statement may mention neither a zeta23-internal name, which a mirror does not
import, nor a constant fixed by `Classical.choose`, nor, by the previous lesson, a finiteness proof
as a term. The run 11 generator therefore omits 27 declarations of `MNF.RH.ReservoirMass` and 2 of
`MNF.RH.Cube` (the pair-measure module) and claims existential statements instead; 13 helper lemmas
of `MNF/Extension/InjectionEjection.lean` named `aux_` are in its mirror but not in the claim set."

### 7. minor. Sign of the pole term in the milestone paragraph

Location: *The milestone for distances above one sixth*, "The Montgomery–Vaughan term and the term
$N^{1-s}/(1-s)$ are of order $N^{2-2\sigma_1}$".

Problem: step 1 and the Lean statements have $N^{1-s}/(s-1)$.

Evidence: R11/audit.out, `@BLClosure.zeta_eq_euler_maclaurin`: "BLClosure.S N s + ↑N ^ (1 - s) / (s - 1) - ↑N ^ (-s) / 2 -".

Fix: "the term $N^{1-s}/(s-1)$ are of order $N^{2-2\sigma_1}$ in mean square".

### 8. minor. Appendix B does not say that `Zeta23.BL`, `Zeta23.Density` and the files under `Zeta23/` are the layer's

Location: Appendix B, "Names are as in the receipts."

Problem: the table lists `Zeta23.BL.bohrLandau_full`, `Zeta23.Density.density_single_window` and
modules `Zeta23/BL/...`, `Zeta23/Density/...` two rows below "`Solution` (zeta23, Anthropic)". Only
the Bohr-Landau section says that these declarations are not Anthropic's.

Evidence: V6/Zeta23/BL/BohrLandauClosure.lean line 1206 "namespace Zeta23.BL";
V6/Zeta23/Density/StripDensity.lean "namespace Zeta23.Density"; REPO/NOTICE attributes these files
to this work (quoted in WORK/facts/density.md section 11).

Fix: add to the header: "Modules under `Zeta23/BL/` and `Zeta23/Density/`, and the names in
`Zeta23.BL`, `Zeta23.Density`, `BLClosure`, `M1` and `DPMV`, belong to the layer of this work and
not to Anthropic's library, whose tree they are compiled in."

## Remark (no change asked)

"Reservoir" has opposite senses in the sources: `InReservoir Δ` in Cube.lean is
$\lvert\beta-1/2\rvert\ge\Delta$, while Density.lean, Strip.lean and `IsReservoir` mean
$0<\lvert\beta-1/2\rvert<\Delta$. The paper's single gloss (zeros off the line) is safe as long as
`InReservoir` is not quoted.
