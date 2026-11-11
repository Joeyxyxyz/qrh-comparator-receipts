# Fact sheet: exploratory numerics on the first 400 zeros

Status of this sheet: every entry carries its evidence as a file and a short exact quote. Paths are
abbreviated as follows.

- `N/` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/notes/density-field-2026-11-03/numeric/`
- `L` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/notes/density-field-2026-11-03/DENSITY_LEDGER.md`
- `REPO/` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/`

Primary sources read in full: `N/RESULTS.md`, `N/CUBE_NUMERIC.md`, `N/mnf_tables.md`, the text content of
`N/cascade.svg` and `N/cube.svg`. Supporting files read: `N/tail_stats.log`, `N/rs_zeros.log`,
`N/c0_variant.log`, `N/summary.json`, `N/mnf_analysis.py` (bootstrap and KS routines), the headers of
`N/make_cube.py`, `N/zeros.tsv`, `N/spacings.tsv`, `N/paircorr.tsv`, and the two preview images.

An independent recount from `N/zeros.tsv` and `N/spacings.tsv` was made for this sheet
(script `WORK/facts/_check/recount.py`); section 10 lists what it confirmed. No number below comes from
the recount alone; each is quoted from the notes.

Quotations keep the notes' own spelling (British: "normalised", "behaviour") and ASCII mathematics; the paper's
own text uses American English and TeX.

No `WORK/facts/literature.md` existed when this sheet was written, so no citation key is used here.
Section 11 lists the references the notes name; the section author must map them to keys or drop them.

## 0. Binding framing for this material

- F0.1 The numerics are exploratory and prove nothing. Evidence: `N/RESULTS.md` line 3,
  "Exploratory numerics, pure Python 3 (no numpy/mpmath), 2026-11-03."; `L`, "**This is exploration, not a
  theorem**, and it concerns the spacing of the ordinates, not the real parts."; `L`, "exploration only."
- F0.2 The statistics are about the spacing of the ordinates $\gamma_n$ of zeros on the critical line. They say
  nothing about real parts, hence nothing about RH, simplicity in general, or a zero-free strip.
  Evidence: `L`, "it concerns the spacing of the ordinates, not the real parts."
- F0.3 GUE statistics for the zeros are a conjecture, not a theorem. Evidence: `N/CUBE_NUMERIC.md`, caveat 3,
  "**GUE is a conjecture for zeta** (Montgomery's pair-correlation conjecture, proved only for test functions with
  Fourier support in (-1, 1)); the cubic law is what GUE predicts, not a theorem about the zeros."
  Also `REPO/README.md`, "the cubic small-distance law of the zeros is the GUE prediction, not a theorem."
  and `REPO/DEPOSIT_MAP.md`, "The cubic small-distance law of the zeros is the GUE prediction (Montgomery 1973),
  not a theorem".
- F0.4 The observed behavior is the known one. Evidence: `N/RESULTS.md`, Summary, "The first few hundred zeros are
  known to be slightly more rigid than the GUE limit (Odlyzko's low-zero comparisons; Berry / Bogomolny-Keating
  finite-height corrections), and that is the direction seen here."; `N/RESULTS.md` section 4, "not a different
  universality class."
- F0.5 Authorship of the code. Evidence: `REPO/NOTICE`, "notes/density-field-2026-11-03/numeric/: pure-Python code
  written with Claude Code; the tabulated zero ordinates it compares against are public (Odlyzko / LMFDB tables)
  and are reproduced only for the first ten zeros and the hundredth, to nine decimals."

## 1. Files, dates, tools

- F1.1 Tools. `N/RESULTS.md`: "Exploratory numerics, pure Python 3 (no numpy/mpmath), 2026-11-03." and
  "scripts `rs_zeros.py`, `gue_exact.py`, `mnf_analysis.py`, `make_svg.py`; data `zeros.tsv`, `spacings.tsv`,
  `paircorr.tsv`, `summary.json`; figure `cascade.svg`; logs `*.log`". `N/CUBE_NUMERIC.md`: "Pure Python 3
  (`make_cube.py`, no numpy; PIL only for the preview), 2026-11-04."
- F1.2 Double-precision floating point only; no interval or multiprecision arithmetic is mentioned anywhere in the
  notes (the phrase is "no numpy/mpmath"). The ordinates are therefore numerical values, not certified enclosures.
- F1.3 Dates. `N/RESULTS.md` is dated "2026-11-03"; `L` files the cascade numerics under "Addendum, 2026-11-04
  (morning)"; `N/CUBE_NUMERIC.md` is dated "2026-11-04". Report the dates as the documents give them.
- F1.4 The directory name inside `N/RESULTS.md` is the working path, "Directory: `density-work/numeric/`"; in the
  public repository the same files are under `notes/density-field-2026-11-03/numeric/`
  (`REPO/README.md`: "the numeric exploration of the first 400 zeros (cascade and cube)").
- F1.5 The notes folder is not covered by the deposit's checksum manifest. Evidence: `REPO/CHECKSUMS.sha256`
  line 2, "the unpacked copies under sources/ and the notes/ folder are not listed: the tarballs are canonical".
  SHA-256 of the files as read for this sheet (computed with `sha256sum` on 2026-11-10):
  - `cascade.svg` `b8b540ba7713585b84fd3ba86ab226237679e77353c96197930d5ce2e1208180`
  - `cube.svg` `0a8d896395d24f27db12ee00251817efddcb1c6dfdf5e234bf9d2c8a02fa2bd8`
  - `RESULTS.md` `ac4e3d64056f077e66d2e70025fedcd04142e3e049870d82fcdc5a73e3cc470d`
  - `CUBE_NUMERIC.md` `25f1d8979db9e3dbbb6d824aeb3aee0e81bf1b11f68579c34b55c44e52508060`
  - `mnf_tables.md` `19d9274d2a15b06bce2e4a2bc08e92588376813ce87f0f57b62f5bbb64fdbb66`
  - `zeros.tsv` `c3d3982a4618766f40439de8af76443e903a9711ac3b3929c9cb47c5f223c419`
  - `spacings.tsv` `60197c1b0fa9152362655e8a871f08d5d3ef72c1abc3dcbe9a35d6ababc5e87e`

## 2. The ordinates: how they were computed and verified

- F2.1 Range. 400 zeros, $\gamma_1 = 14.134725$ to $\gamma_{400} = 679.742198$. Evidence: `N/RESULTS.md`, Summary,
  "400 zeros located, gamma_1 = 14.134725 ... gamma_400 = 679.742198, giving M = 399 normalised spacings";
  `N/mnf_tables.md` line 2, "zeros: gamma_1 = 14.134725, gamma_400 = 679.742198".
- F2.2 Method: the Riemann-Siegel formula for Hardy's function $Z(t)$ with the main sum and the first correction
  term $C_0$ only. Evidence: `N/RESULTS.md` section 1, "Z(t) = 2 sum_(n<=N) n^(-1/2) cos(theta(t) - t log n) +
  (-1)^(N-1) (t/2pi)^(-1/4) C0(p)", with "N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, C0(p) = Psi(p) =
  cos(2pi(p^2 - p - 1/16)) / cos(2pi p)".
- F2.3 The phase $\theta(t)$ by its asymptotic series through the $t^{-9}$ term, checked against a direct
  log-Gamma evaluation. Evidence: `N/RESULTS.md` section 1, "theta was checked against Im log Gamma(1/4 + it/2) -
  (t/2) log pi computed by complex Stirling with recurrence: agreement 2e-15 (t = 14) to 5e-13 (t = 700) mod 2pi."
  (`N/rs_zeros.log`: "t=  14.0  |theta_stirling - theta_lgamma| mod 2pi = 1.78e-15", "t= 700.0 ... = 4.55e-13".)
- F2.4 Scan. Evidence: `N/RESULTS.md` section 1, "Gram points g_n (theta(g_n) = n pi) were computed by Newton; each
  Gram interval was cut into 48 grid points (19,885 points on [12, 700], final step 0.028 in t, i.e. about 0.02
  mean spacings), Z(C0) evaluated at each, and every sign change bisected to 1e-12."
- F2.5 Near-miss check. Evidence: same paragraph, "A near-miss check (local minima of |Z| below 0.08 with no sign
  change, refined on a 400-point sub-grid) found nothing." (`N/rs_zeros.log`: "sign-change zeros: 414; near-miss
  refinements: 0 (added 0)".)
- F2.6 Count check against the smooth part of the Riemann-von Mangoldt formula. Evidence: `N/RESULTS.md` section 1,
  "414 zeros lie below T = 700 against theta(700)/pi + 1 = 414.557 (so S(700) = -0.56, normal); the running counts
  agree with the Riemann-von Mangoldt smooth term at every check-point, and exactly 12 of the 414 Gram points
  below 700 violate Gram's law (count below g_n != n + 1)". The check-point table, verbatim:

  | $T$ | zeros found | $\theta(T)/\pi + 1$ | implied $S(T)$ |
  |---|---|---|---|
  | 100 | 29 | 29.002 | -0.002 |
  | 200 | 79 | 79.193 | -0.193 |
  | 300 | 138 | 137.712 | +0.288 |
  | 400 | 202 | 201.639 | +0.361 |
  | 500 | 269 | 269.587 | -0.587 |
  | 600 | 341 | 340.739 | +0.261 |
  | 700 | 414 | 414.557 | -0.557 |

  Only the first 400 of the 414 zeros found are analyzed.
- F2.7 Re-location by two further evaluators. Evidence: `N/RESULTS.md` section 1, "Each of the first 400 zeros was
  re-located with two independent evaluators started from the C0 value: Riemann-Siegel with the four further
  correction terms C1..C4 (derivatives of Psi taken by Cauchy integrals on a circle, because series division is
  unstable near p = 1/4, 3/4), and Euler-Maclaurin summation of zeta(1/2 + it) with ~t + 30 terms and 10 Bernoulli
  terms (formula-independent, ~1e-13 in Z)."
- F2.8 Size of the discrepancies between the three ordinate columns. Evidence: `N/RESULTS.md` section 1, "Over all
  400 zeros: max |gamma(C0) - gamma(EM)| = 7.5e-3 (n = 3), mean 2.1e-4, at most 1.4e-3 for gamma > 100 and 6.3e-4
  for gamma > 300. With C1..C4 the maximum discrepancy from Euler-Maclaurin drops to 3.1e-6".
- F2.9 Comparison with tabulated ordinates: eleven values only (the first ten and the hundredth), and the
  comparison values were typed from memory. Evidence: `N/RESULTS.md` section 1, "Self-check against tabulated
  ordinates (first ten and the 100th, values as recalled from the LMFDB/Odlyzko tables)" and "the Euler-Maclaurin
  ordinates agree with the tabulated values to <= 3.3e-10 (the tables carry nine decimals)"; caveat 3, "The
  tabulated comparison values are quoted from memory of the standard tables (9 decimals) and agree with the
  Euler-Maclaurin ordinates to 3e-10, which also certifies them." Example rows of the self-check (`N/rs_zeros.log`):
  "1   14.137196099   14.134725142   14.134725142   +2.47e-03   -2.65e-10" and
  "100   236.524327123   236.524229666   236.524229666   +9.75e-05   -1.84e-10".
- F2.10 Which column the analysis uses. Evidence: `N/RESULTS.md` section 1, "`zeros.tsv` holds all three columns;
  the analysis below uses the Euler-Maclaurin-verified column." (`N/mnf_tables.md` line 1: "(ordinates: column
  gamma_EM)"; `N/CUBE_NUMERIC.md`: "column `gamma_EM`, the Euler-Maclaurin-verified ordinates".)
- F2.11 Robustness to the choice of column. Evidence: `N/RESULTS.md` section 1, "Re-running everything on the raw C0
  column changes no count in any ladder row, moves every mass fraction by <= 3e-5, the minimum spacing from 0.2434
  to 0.2425, the KS distance from 0.0494 to 0.0496 and no fitted exponent at two decimals (`c0_variant/`)."
  (`N/c0_variant.log`: "min spacing s_363 = 0.2425".)
- F2.12 Stated accuracy of the analysis column. Evidence: `N/RESULTS.md` caveat 3, "the ordinates in the analysis
  column are the Euler-Maclaurin-verified ones, good to ~1e-9."
- F2.13 All 400 are treated as simple and on the critical line. Evidence: `N/CUBE_NUMERIC.md`, "the
  Euler-Maclaurin-verified ordinates, all 400 on the critical line" and "For the 400 known zeros every delta is 0
  and every multiplicity is 1". The notes locate them as sign changes of the real function $Z(t)$; they do not give
  a rigorous completeness proof (see caveat C4 in section 8).

## 3. Normalized spacings

- F3.1 Definition. $s_n = (\gamma_{n+1} - \gamma_n)\,\log(\gamma_n/2\pi)/(2\pi)$ for $n = 1, \dots, 399$.
  Evidence: `N/RESULTS.md` section 2, "s_n = (gamma_(n+1) - gamma_n) log(gamma_n / 2pi) / 2pi, n = 1..399
  (`spacings.tsv`)."
- F3.2 Summary values (all from the table of `N/RESULTS.md` section 2; the same numbers are in the header of
  `N/mnf_tables.md`):

  | quantity | value | comparison given in the notes |
  |---|---|---|
  | number of spacings $M$ | 399 | from 400 zeros |
  | $\sum_n s_n$ | 397.977 | |
  | mean | 0.99744 | "unit mean expected from the density log(t/2pi)/2pi" |
  | standard deviation | 0.3709, bootstrap 16-84 % [0.357, 0.384] | GUE 0.4221, Poisson 1 |
  | median | 0.9587 | exact GUE median 0.9628 |
  | minimum | 0.2434 | $s_{363}$: $\gamma_{363} = 630.4739$, $\gamma_{364} = 630.8058$ |
  | next smallest | 0.2471, 0.2911, 0.2965, 0.3244 | $s_{315}$, $s_{212}$, $s_{298}$, $s_{186}$ |
  | maximum | 2.2014 | $s_{379}$: $\gamma_{379} = 650.6687$, $\gamma_{380} = 653.6496$ |

  Evidence quotes: "| standard deviation | 0.3709, bootstrap 16-84 % [0.357, 0.384] | 399; GUE 0.4221, Poisson 1 |";
  "| minimum (first non-empty threshold) | 0.2434 | s_363: gamma_363 = 630.4739, gamma_364 = 630.8058 |";
  "| maximum = trace delta* | 2.2014 | s_379: gamma_379 = 650.6687, gamma_380 = 653.6496 |".
  Unrounded values in `N/summary.json`: "min_spacing : 0.243437442957661", "max_spacing : 2.2013813842084438",
  "total : 397.9771142652757", "sd : 0.3709443045501635".

## 4. The threshold cascade

### 4.1 Vocabulary (the author's; define once, in standard terms)

- F4.1 Evidence: `N/RESULTS.md` section 3, "Vocabulary: for a threshold Delta, the **nullified reading** is nu_Delta =
  sum over s >= Delta of s, the **hidden (reservoir) mass** is h_Delta = sum over s < Delta of s, and the **trace**
  delta* = sup{Delta : nu_Delta > 0} = max s."
- F4.2 Standard reading (this sheet's translation, to be used in the paper): with threshold $\Delta > 0$ on the
  normalized spacings, $h_\Delta = \sum_{s_n < \Delta} s_n$ is the total length of the spacings shorter than $\Delta$,
  $h_\Delta / \sum_n s_n$ is the fraction of the total length they carry (a truncated first moment of the empirical
  nearest-neighbor spacing distribution), $\#\{s_n < \Delta\}/M$ is the empirical distribution function of the
  spacings at $\Delta$, $\nu_\Delta = \sum_n s_n - h_\Delta$, and $\delta^*$ is the largest spacing. The notes' "threshold
  cascade" and "ladder" mean the table of these quantities over a list of thresholds; the notes use the list
  0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1, 1.5, 2 (`N/mnf_analysis.py`: "LADDER = [0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0,
  1.5, 2.0]").
- F4.3 Symbol clash to resolve in the paper. In these numerics $\Delta$ is a threshold on normalized ordinate
  spacings (in units of the mean spacing). In the Lean layer and in panel A of `cube.svg`, $\Delta$ and $\delta$ are
  distances of the real part from $1/2$, and "reservoir" refers to zeros off the line (`cube.svg` legend:
  "reservoir |delta| >= Delta: O(T^(1-c)) zeros, proved"; `REPO/DEPOSIT_MAP.md`: "the reservoir mass Σ m(ρ)·\|Re ρ −
  1/2\| over 0 < Im ρ ≤ T"). The two uses are different objects. Recommendation: in the numerics section write the
  spacing threshold with a different letter (for example $x$, which `N/CUBE_NUMERIC.md` already uses for the pair
  distance) and avoid the word "reservoir" for spacings, or define it once and say it is unrelated to the
  real-part quantity.
- F4.4 Comparison laws. Evidence: `N/RESULTS.md` section 3, "GUE surmise p(s) = (32/pi^2) s^2 exp(-4s^2/pi)";
  "GUE exact = the sine-kernel (Gaudin-Mehta) nearest-neighbour law from the Fredholm determinant E_2(0; s)
  (`gue_exact.py`: E_2(0;1) = 0.170217, small-s series matched to 5e-10, normalisation to 1e-12, surmise within
  1.5 % for s < 2)"; "Poisson p(s) = e^(-s) (reservoir fraction 1 - (1 + Delta) e^(-Delta), count fraction 1 -
  e^(-Delta))".

### 4.2 Empty below 0.243

- F4.5 No normalized spacing is below 0.2434; the three lowest thresholds 0.05, 0.1, 0.2 catch nothing.
  Evidence: `N/RESULTS.md`, Summary, "**The reservoir is empty below Delta = 0.24.** The smallest spacing is s_363 =
  0.2434 (gamma_363 = 630.4739, gamma_364 = 630.8058). For Delta in {0.05, 0.1, 0.2} the hidden mass h_Delta is
  exactly 0 (n_below = 0 of 399), where Poisson would hide 19.5, 38.0 and 72.3 spacings respectively (P(0 | Poisson
  at 0.2) = 4e-32) and GUE 0.1, 0.4 and 3.4 (P(0 | GUE at 0.2) = 0.034)."
  Figure text (`N/cascade.svg`): "reservoir empty up to D = 0.243:"; `L`: "**empty up to Δ = 0.243**".
  Rounding: the notes write 0.24, 0.243 and 0.2434 in different places; the unrounded value is 0.243437...
  (F3.2). Recommended wording for the paper: no normalized spacing is below 0.243.
- F4.6 Under GUE an empty set below 0.2 is not rare. Evidence: same sentence, "P(0 | GUE at 0.2) = 0.034";
  `N/tail_stats.log`, "Delta=0.2: observed 0, GUE exact expects 3.4; P(count <= 0) = 3.36e-02".

### 4.3 Counts at each threshold against GUE and Poisson

- F4.7 Count table (from `N/mnf_tables.md`, "Threshold ladder (count fraction), with the expected counts under each
  law"; identical in `N/RESULTS.md` section 3). $M = 399$ throughout.

  | $\Delta$ | $\#\{s<\Delta\}$ | empirical fraction | GUE surmise | GUE exact | Poisson | expected count, GUE surmise | expected count, GUE exact | expected count, Poisson |
  |---|---|---|---|---|---|---|---|---|
  | 0.05 | 0 | 0.00000 | 0.00013 | 0.00014 | 0.04877 | 0.1 | 0.1 | 19.5 |
  | 0.1 | 0 | 0.00000 | 0.00107 | 0.00109 | 0.09516 | 0.4 | 0.4 | 38.0 |
  | 0.2 | 0 | 0.00000 | 0.00839 | 0.00850 | 0.18127 | 3.3 | 3.4 | 72.3 |
  | 0.3 | 4 | 0.01003 | 0.02725 | 0.02760 | 0.25918 | 10.9 | 11.0 | 103.4 |
  | 0.5 | 29 | 0.07268 | 0.11200 | 0.11306 | 0.39347 | 44.7 | 45.1 | 157.0 |
  | 0.75 | 114 | 0.28571 | 0.30204 | 0.30359 | 0.52763 | 120.5 | 121.1 | 210.5 |
  | 1 | 224 | 0.56140 | 0.53305 | 0.53390 | 0.63212 | 212.7 | 213.0 | 252.2 |
  | 1.5 | 359 | 0.89975 | 0.87447 | 0.87336 | 0.77687 | 348.9 | 348.5 | 310.0 |
  | 2 | 398 | 0.99749 | 0.98295 | 0.98229 | 0.86466 | 392.2 | 391.9 | 345.0 |

  Evidence (one row verbatim): "| 0.5 | 29 | 399 | 0.07268 | 0.11200 | 0.11306 | 0.39347 | 44.7 | 45.1 | 157.0 |".
- F4.8 Mass table (from `N/mnf_tables.md`, "Threshold ladder (reservoir / hidden mass)"; identical in
  `N/RESULTS.md` section 3).

  | $\Delta$ | $\#\{s<\Delta\}$ | $\#\{s\ge\Delta\}$ | $h_\Delta$ | $\nu_\Delta$ | $h_\Delta/\sum s$ | GUE surmise | GUE exact | Poisson |
  |---|---|---|---|---|---|---|---|---|
  | 0.05 | 0 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00001 | 0.00001 | 0.00121 |
  | 0.1 | 0 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00008 | 0.00008 | 0.00468 |
  | 0.2 | 0 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00125 | 0.00127 | 0.01752 |
  | 0.3 | 4 | 395 | 1.0780 | 396.8991 | 0.00271 | 0.00608 | 0.00616 | 0.03694 |
  | 0.5 | 29 | 370 | 11.5369 | 386.4402 | 0.02899 | 0.04109 | 0.04145 | 0.09020 |
  | 0.75 | 114 | 285 | 66.3998 | 331.5773 | 0.16684 | 0.16145 | 0.16210 | 0.17336 |
  | 1 | 224 | 175 | 164.0166 | 233.9605 | 0.41213 | 0.36367 | 0.36368 | 0.26424 |
  | 1.5 | 359 | 40 | 329.5385 | 68.4386 | 0.82803 | 0.77973 | 0.77739 | 0.44217 |
  | 2 | 398 | 1 | 395.7757 | 2.2014 | 0.99447 | 0.96259 | 0.96108 | 0.59399 |

  Evidence (one row verbatim): "| 0.3 | 4 | 395 | 399 | 1.0780 | 396.8991 | 0.00271 | 0.00608 | 0.00616 | 0.03694 |".
- F4.9 Narrative of the cascade. Evidence: `N/RESULTS.md` section 4, "The reservoir opens only at the 0.3 rung, with 4
  spacings (mass 1.078, fraction 0.27 %, against 0.62 % GUE and 3.69 % Poisson), reaches 29 spacings (2.90 %, GUE
  4.15 %, Poisson 9.02 %) at 0.5, and only catches up with GUE around Delta = 0.75 (114 spacings, 16.7 % vs 16.2 %),
  after which it runs *above* GUE (224 spacings and 41.2 % at Delta = 1 vs 36.4 %; 359 and 82.8 % at 1.5 vs 77.7 %)
  because the distribution is narrower than GUE on both sides."
- F4.10 Tail probabilities of the observed counts. Method: "Poisson approximation to the binomial, `tail_stats.log`"
  (`N/RESULTS.md` section 3). Table from `N/RESULTS.md` section 3:

  | event | observed | GUE exact expects | $P(\le n \mid \text{GUE})$ | Poisson expects | $P(\le n \mid \text{Poisson})$ |
  |---|---|---|---|---|---|
  | $s < 0.2$ | 0 | 3.4 | 0.034 | 72.3 | 4e-32 |
  | $s < 0.3$ | 4 | 11.0 | 0.015 | 103.4 | 6e-39 |
  | $s < 0.5$ | 29 | 45.1 | 0.007 | 157.0 | 4e-36 |
  | $s \ge 2.0$ | 1 | 7.1 | 0.007 | 54.0 | 2e-22 |
  | $s \ge \delta^* = 2.2014$ | 1 | 2.7 | 0.26 | 44.1 | 3e-18 |

  Evidence: `N/tail_stats.log`, "Delta=0.5: observed 29, GUE exact expects 45.1; P(count <= 29) = 7.03e-03" and
  "Delta=2.0000: observed 1 spacings >= Delta, GUE exact expects 7.1; P(count <= 1) = 6.88e-03".
- F4.11 The largest spacing. Evidence: `N/RESULTS.md`, Summary, "The trace delta* (largest threshold with a nonzero
  reading) is the maximum spacing, **2.2014** (s_379, between gamma_379 = 650.6687 and gamma_380 = 653.6496); GUE
  expects 2.7 spacings beyond it among 399 (P(<=1) = 0.26), Poisson expects 44."
- F4.12 Deviation from GUE within the sample: fewer small and fewer large spacings than GUE. Evidence:
  `N/RESULTS.md`, Summary, "Within GUE there is a visible finite-height signature: *fewer* small spacings and *fewer*
  large spacings than GUE (29 below 0.5 vs 45.1 expected, P = 0.007; 1 above 2.0 vs 7.1 expected, P = 0.007; sd
  0.371 [0.357, 0.384] vs 0.422)." Size as the notes state it: `N/RESULTS.md` section 4, "it is a ~2-2.5 sigma effect
  on 400 zeros and is in the direction expected for low zeros (section 6), not a different universality class."

### 4.4 Fitted exponents and their bands

- F4.13 Small-threshold asymptotics of the comparison laws (theory, not data). Evidence: `N/RESULTS.md` section 4,
  "Under Poisson the hidden mass below Delta is h_Delta / sum s = 1 - (1 + Delta) e^(-Delta) ~ Delta^2 / 2 and the
  hidden count is ~ Delta"; "with the exact law c = pi^2/3, count ~ (pi^2/9) Delta^3 = 1.097 Delta^3 and mass ~
  (pi^2/12) Delta^4 = 0.822 Delta^4"; "with the surmise c = 32/pi^2, count ~ (32/3pi^2) Delta^3 = 1.081 Delta^3 and
  mass ~ (8/pi^2) Delta^4 = 0.811 Delta^4". In TeX: under GUE the count fraction is $\sim (\pi^2/9)\Delta^3$ and the
  mass fraction $\sim (\pi^2/12)\Delta^4$; under Poisson $\sim \Delta$ and $\sim \Delta^2/2$.
- F4.14 What was fitted. Evidence: `N/RESULTS.md` section 4, "Least-squares log-log slopes of h_Delta / sum s versus
  Delta, with the identical fit applied to the theoretical laws at the same thresholds (the pure Delta^4 / Delta^2
  regime is only reached as Delta -> 0; at Delta ~ 0.5 the local GUE slope is already 3.6-3.8, and the empirical
  slope has to be compared with that, not with 4)".
- F4.15 Fit table (from `N/mnf_tables.md`, "Small-threshold exponent of the reservoir mass h_Delta / sum s";
  identical in `N/RESULTS.md` section 4). Bands are bootstrap 16-84 % intervals.

  | thresholds | $\#\{s<\Delta\}$ at each | mass exponent | band | same fit: GUE surmise / GUE exact / Poisson | count exponent | band | same fit: GUE surmise / GUE exact / Poisson |
  |---|---|---|---|---|---|---|---|
  | 0.2, 0.3, 0.5 (2 non-empty used) | 0, 4, 29 | 4.64 | [3.77, 5.79] (1962 resamples) | 3.81 / 3.80 / 1.79 | 3.88 | [3.07, 5.02] | 2.83 / 2.82 / 0.84 |
  | 0.2, 0.3, 0.5, 0.75 (3 non-empty used) | 0, 4, 29, 114 | 4.50 | [4.01, 5.23] (1969 resamples) | 3.68 / 3.68 / 1.74 | 3.67 | [3.19, 4.40] | 2.72 / 2.71 / 0.81 |
  | 0.20 to 0.60 step 0.05 (8 non-empty used) | 0, 2, 4, 6, 14, 21, 29, 40, 55 | 4.62 | [3.96, 5.33] (1715 resamples) | 3.76 / 3.76 / 1.77 | 3.86 | [3.21, 4.56] | 2.79 / 2.78 / 0.83 |
  | 0.25 to 0.75 step 0.05 (11 used) | 2, 4, 6, 14, 21, 29, 40, 55, 70, 88, 114 | 4.52 | [4.07, 5.05] (1723 resamples) | 3.63 / 3.62 / 1.71 | 3.71 | [3.26, 4.23] | 2.67 / 2.67 / 0.79 |

  Evidence (last row verbatim): "| fine grid 0.25..0.75 step 0.05 (fit uses the 11 non-empty) | 2, 4, 6, 14, 21, 29,
  40, 55, 70, 88, 114 | 4.52 | [4.07, 5.05] (1723 resamples) | 3.63 / 3.62 / 1.71 | 3.71 | [3.26, 4.23] | 2.67 / 2.67
  / 0.79 |".
- F4.16 Headline fit. Evidence: `N/RESULTS.md`, Summary, "A log-log fit of h_Delta / sum s on Delta = 0.25, 0.30,
  ..., 0.75 (11 thresholds, n_below from 2 to 114) gives exponent **4.52** (bootstrap 16-84 %: [4.07, 5.05]). The
  same fit applied to the exact GUE law on the same thresholds gives 3.62, to the Wigner surmise 3.63, and to
  Poisson 1.71."
- F4.17 The statement the notes call robust. Evidence: `N/RESULTS.md` section 4, "on every choice of thresholds the
  empirical exponent (4.5-4.6, with 16-84 % bootstrap bands of roughly +-0.5) lies **above** the GUE value for the
  same thresholds (3.6-3.8) and far above Poisson (1.7-1.8); for the hidden count the empirical exponent is 3.7-3.9
  against GUE 2.7-2.8 and Poisson 0.8."
- F4.18 How the bands were made. Evidence: `N/mnf_analysis.py`, "random.seed(20261103)", "for _ in range(2000):",
  "# bootstrap over spacings (resample with replacement), on the thresholds that are" / "# non-empty in the actual
  sample; resamples that empty one of them are skipped". So each band is from 2000 resamples of the 399 spacings
  minus the skipped ones (`N/summary.json`: "'boot_skipped': 277" and "'boot_n': 1723" for the 0.25 to 0.75 grid).
  The fitted points are cumulative quantities at nested thresholds, so they are not independent observations; the
  notes do not claim a standard error from the least-squares fit, only the bootstrap band.
- F4.19 Do not read the exponent as a measured asymptotic law. Evidence: `N/RESULTS.md` caveat 2, "**The asymptotic
  exponents are not directly observable with M = 399.**" (full text in section 8, C2).

## 5. Kolmogorov-Smirnov distances

- F5.1 Table (from `N/mnf_tables.md`, "Kolmogorov-Smirnov distance of the empirical spacing CDF (M = 399)";
  identical in `N/RESULTS.md` section 3):

  | law | $D_M$ | approximate p-value |
  |---|---|---|
  | GUE surmise | 0.0494 | 0.277 |
  | GUE exact | 0.0508 | 0.247 |
  | Poisson | 0.3285 | 2.7e-38 |

  Evidence (verbatim rows): "| GUE surmise | 0.0494 | 0.277 |", "| GUE exact | 0.0508 | 0.247 |",
  "| Poisson | 0.3285 | 2.7e-38 |".
- F5.2 Prose form. Evidence: `N/RESULTS.md`, Summary, "Kolmogorov-Smirnov distance of the spacing CDF 0.051 from the
  exact GUE law (p ~ 0.25, M = 399), 0.049 from the surmise (p ~ 0.28), 0.33 from Poisson (p ~ 3e-38)."
- F5.3 How the p-values were computed. Evidence: `N/mnf_analysis.py`, function `ks_pvalue`, docstring "Asymptotic
  Kolmogorov distribution with the usual finite-n correction." with "lam = (math.sqrt(n) + 0.12 + 0.11 /
  math.sqrt(n)) * D". This is the one-sample test for independent draws; see reviewer note R1 in section 8.
- F5.4 Correct reading: the sample is compatible with the GUE spacing law at this sample size (not rejected) and
  incompatible with Poisson. A non-rejection with $M = 399$ is not evidence that the law is exactly GUE; the notes
  say so (caveat C1: "Nothing here distinguishes \"GUE plus finite-height corrections\" from a slightly different
  law; 400 spacings cannot.").

## 6. Histogram and binned pair correlation (cascade data set)

- F6.1 Histogram, bin width 0.2 (panel B of `cascade.svg`). Evidence: `N/RESULTS.md` section 4, "The peak bins
  [0.6, 1.0) hold 169 spacings where GUE expects 141.4 and Poisson 72.2; both tails are thinner than GUE
  ([0.0, 0.4): 14 vs 24.4; [2.0, 3.2): 1 vs 6.9)." Row examples from `N/mnf_tables.md`: "| [0.0, 0.2) | 0 | 0.000 |
  0.042 | 0.043 | 0.906 | 3.3 / 72.3 |", "| [0.8, 1.0) | 87 | 1.090 | 0.929 | 0.925 | 0.407 | 74.1 / 32.5 |";
  "spacings >= 3.2: 0". The full 16-row table is in `N/mnf_tables.md`, "Spacing histogram (bin 0.2), density = n /
  (M * 0.2)".
- F6.2 Binned pair correlation: unfolding and normalization. Evidence: `N/RESULTS.md` section 5, "Unfolded ordinates
  x_n = theta(gamma_n)/pi + 1 (the smooth counting function; this unfolding and the local-density normalisation
  used for the spacings agree to O(1/gamma)). All pairs i < j with x_j - x_i < 2 were binned in steps of 0.1 and
  divided by (L - u_mid) x 0.1 with L = x_400 - x_1 = 398.96 (the edge correction L - u instead of L is 0.5 %). GUE
  column = bin average of Montgomery's 1 - (sin(pi u)/(pi u))^2 by Simpson integration; Poisson = 1."
- F6.3 Totals. Evidence: `N/mnf_tables.md`, "window length L = x_400 - x_1 = 398.959; pairs with distance < 2: 599";
  "pairs with u in [0.0,0.5): n = 29, GUE expects 45.1 (+-6.7), Poisson expects 199.4"; "pairs with u in [0.0,1.0):
  n = 222, GUE expects 218.5 (+-14.8), Poisson expects 398.5"; "pairs with u in [1.0,2.0): n = 377, GUE expects
  388.1 (+-19.7), Poisson expects 397.5". `N/RESULTS.md` section 5: "Across [0, 2) the 599 pairs match GUE's 606.6
  expected within 1 sigma."
- F6.4 Bin-level scatter. Evidence: `N/RESULTS.md` section 5, "**Small-sample note.** Each bin expects only ~40 pairs
  at u ~ 1 (and 0.4-20 pairs for u < 0.5), so the per-bin standard error is +-0.13 to +-0.19 on R_2 at u ~ 1 and
  the empirical values scatter from 0.70 to 1.38 around 1 (the [0.9, 1.0) bin, 55 vs 39.6, is a +2.4 sigma
  fluctuation; [1.1, 1.2), 28 vs 39.1, is -1.8 sigma)."
- F6.5 The small-distance deficit is the same 29 nearest-neighbor pairs as in the threshold table. Evidence: same
  paragraph, "the five bins below u = 0.5 hold 29 pairs against 45.1 +- 6.7 for GUE and 199 for Poisson - a clear
  repulsion hole, slightly deeper than GUE, and the same 29 spacings as the Delta = 0.5 rung of the ladder (no
  non-adjacent pair is that close)." The 20-row bin table is in `N/mnf_tables.md`, "Pair correlation at small
  distance".

## 7. The pair measure on the line (the author's "cube")

### 7.1 Definition

- F7.1 Evidence: `N/CUBE_NUMERIC.md`, "The \"cube\" is the measure that puts every ordered pair (rho, rho') of
  nontrivial zeros at the point (delta1, delta2, s) = (Re rho - 1/2, Re rho' - 1/2, (gamma - gamma')
  log(gamma_min/2pi)/2pi), with weight m(rho) m(rho') (multiplicities), gamma_min = min(gamma, gamma'). The faces
  |delta| = 1/2 are the edges of the critical strip."
  In TeX: the point $(\beta - \tfrac12,\ \beta' - \tfrac12,\ (\gamma - \gamma')\log(\gamma_{\min}/2\pi)/(2\pi))$ with
  weight $m(\rho)m(\rho')$. Standard term: the pair measure of the zeros (a two-point counting measure) in
  coordinates given by the two real-part offsets and one normalized ordinate difference.
- F7.2 Difference from the Lean module. The Lean pair measure is stated with the raw ordinate difference:
  `REPO/DEPOSIT_MAP.md`, "ordered pairs of zeros at (Re ρ − 1/2, Re ρ′ − 1/2, Im ρ − Im ρ′) with weight m(ρ)m(ρ′)".
  The numerics rescale the third coordinate by the local density. The figure is therefore an illustration of the
  object, not a plot of a Lean-checked quantity.
- F7.3 What the data look like. Evidence: `N/CUBE_NUMERIC.md`, "For the 400 known zeros every delta is 0 and every
  multiplicity is 1, so the empirical measure lies on the s axis (the line delta1 = delta2 = 0) with:" followed by
  three bullets: "the atom at the origin = the diagonal pairs rho = rho', mass sum m(rho)^2 = 400;"; "the
  off-diagonal atom (distinct zeros with equal ordinates, which an off-line zero would create together with its
  mirror 1 - conj(rho)) = 0;"; "a hole: no pair of distinct zeros has 0 < |s| < 0.2434 (the smallest spacing,
  s_363); level repulsion."
- F7.4 The off-axis part is empty by construction, not by observation. Evidence: `N/CUBE_NUMERIC.md` caveat 4 (full
  text in section 8, K4).

### 7.2 Integrated pair count per zero

- F7.5 Definition. Evidence: `N/CUBE_NUMERIC.md`, "y(x) = #{ordered pairs of distinct zeros with 0 < |s| <= x} /
  400. Each unordered pair i < j counts twice (both orders), which is why the Poisson line is 2x and the GUE curve
  is 2 int_0^x (1 - (sin pi u / pi u)^2) du."
  In TeX: $y(x) = \#\{(\rho,\rho') : \rho \ne \rho',\ 0 < |s| \le x\}/400$, compared with
  $2\int_0^x \bigl(1 - (\sin \pi u/\pi u)^2\bigr)\,du$ (GUE) and $2x$ (Poisson).
- F7.6 Unfolding. Evidence: `N/CUBE_NUMERIC.md`, "for a pair gamma_i < gamma_j, s = (gamma_j - gamma_i)
  log(gamma_i/2pi)/2pi, i.e. the local density at the **smaller** ordinate. For adjacent zeros this is exactly the
  s_n of `spacings.tsv`, so the small-x part of the count is the spacing ladder of RESULTS.md section 3 (times 2)."
- F7.7 Reference curves. Evidence: `N/CUBE_NUMERIC.md`, "GUE integral by Simpson (2000 panels); Poisson 2x; the
  cubic reference (2 pi^2/9) x^3 is the small-x asymptote of the GUE curve (R_2(u) ~ (pi^2/3) u^2, so int_0^x R_2 ~
  (pi^2/9) x^3, times 2)."
- F7.8 Table (from `N/CUBE_NUMERIC.md`, "Integrated pair count per zero"):

  | $x$ | unordered pairs with $s \le x$ | zeros: $y(x)$ | GUE $2\int_0^x R_2$ | Poisson $2x$ | cubic $(2\pi^2/9)x^3$ |
  |---|---|---|---|---|---|
  | 0.1 | 0 | 0.0000 | 0.0022 | 0.2 | 0.0022 |
  | 0.2 | 0 | 0.0000 | 0.0170 | 0.4 | 0.0175 |
  | 0.3 | 4 | 0.0200 | 0.0552 | 0.6 | 0.0592 |
  | 0.5 | 29 | 0.1450 | 0.2263 | 1.0 | 0.2742 |
  | 0.75 | 114 | 0.5700 | 0.6112 | 1.5 | 0.9253 |
  | 1 | 224 | 1.1200 | 1.0972 | 2.0 | 2.1932 |
  | 1.5 | 408 | 2.0400 | 2.0689 | 3.0 | 7.4022 |
  | 2 | 602 | 3.0100 | 3.0501 | 4.0 | 17.546 |
  | 3 | 1006 | 5.0300 | 5.0336 | 6.0 | 59.218 |

  Evidence (verbatim row): "| 0.5 | 29 | 0.1450 | 0.2263 | 1.0 | 0.2742 |". Note on the cubic column: "(The cubic
  column is only meaningful where it coincides with the GUE column, x <~ 0.3; it is drawn as a reference line of
  slope 3.)"
- F7.9 Headline value at $x = 0.5$. Evidence: `N/CUBE_NUMERIC.md`, Verification, "29 nearest-neighbour pairs -> 58
  ordered pairs -> 58/400 = 0.145 per zero, as expected. GUE: 0.226, Poisson: 1."
- F7.10 Large-$x$ normalization check. Evidence: `N/CUBE_NUMERIC.md`, "At x = 2, 2.5, 3 the data give 3.010, 3.965,
  5.030 against GUE 3.050, 4.041, 5.034 and 2x - 1 = 3, 4, 5 (Poisson 4, 5, 6). The pairs lost at the top of the
  window are about x / sum s = 0.75 % of the count at x = 3, which is inside the sqrt(n) noise."
- F7.11 Totals. Evidence: `N/CUBE_NUMERIC.md`, "2012 ordered pairs in all" (those with $|s| \le 3$) and "Of the 1006
  unordered pairs with s <= 3, 399 are adjacent and 607 non-adjacent."

### 7.3 Slopes

- F7.12 Evidence: `N/CUBE_NUMERIC.md`, "**Fitted log-log slopes on x in [0.25, 0.75]** (11 points): zeros **3.71**,
  GUE on the same points **2.67**, Poisson 1.00, cubic 3.00 exactly."
- F7.13 These are the count-fraction exponents of section 4 again, not new information. Evidence: same paragraph,
  "These are the same numbers as the \"count fraction\" exponents of RESULTS.md (fine grid 0.25..0.75: 3.71
  empirical, 2.67 GUE exact), as they must be, since below x = 1 every close pair is a nearest-neighbour pair."
  The band for 3.71 is therefore the one in F4.15, [3.26, 4.23].
- F7.14 Local slope of the GUE curve itself. Evidence: same paragraph, "The local log-slope of the GUE curve is 2.98
  at x = 0.1, 2.90 at 0.25, 2.63 at 0.5, 2.23 at 0.75, 1.82 at 1: the x^3 regime is only reached as x -> 0, where
  the data have no pairs at all."
- F7.15 Why the empirical slope exceeds the GUE slope on the window. Evidence: same paragraph, "The empirical curve
  is steeper than GUE on the fit window because it starts later (nothing below 0.2434, 4 pairs below 0.3, 29 below
  0.5 against GUE's 3.4, 11.0, 45.1) and catches up by x ~ 0.75-1: the same deficit of small spacings as in
  RESULTS.md, a ~2-2.5 sigma effect in the direction expected for low zeros."
- F7.16 Fit method. Evidence: `N/CUBE_NUMERIC.md`, "Log-log slopes: least squares of log10 y on log10 x at x = 0.25,
  0.30, ..., 0.75 (11 points, all non-empty for the data), the identical fit applied to the GUE, Poisson and cubic
  curves at the same points."

### 7.4 Internal cross-checks stated in the notes

- F7.17 Evidence: `N/CUBE_NUMERIC.md`, Verification, "At x = 0.5: `spacings.tsv` has 29 spacings below 0.5; the
  all-pairs count of s <= 0.5 is also 29, of which 0 are non-adjacent pairs (the closest non-adjacent pair is
  beyond 0.5)."; "The smallest |s| over all pairs equals the smallest spacing, 0.2434 (gamma_363, gamma_364)."
- F7.18 The two unfoldings give slightly different counts. Evidence: `N/CUBE_NUMERIC.md`, Verification, "Cross-check
  with `paircorr.tsv` (which uses the theta(gamma)/pi unfolding and half-open bins): 29 pairs with u < 0.5 (same),
  222 with u < 1 against 224 here with s <= 1 (the two unfoldings differ by O(1/gamma) and the bin edge is
  inclusive here), 599 with u < 2 against 602 here." If the paper quotes pair counts it must say which unfolding.

## 8. Caveats (every one the notes state)

From `N/RESULTS.md` section 6, "Caveats" (C1 to C5), quoted in full:

- C1 "**Only the first 400 zeros.** The GUE limit is approached as log(gamma/2pi) -> infinity; here log(gamma/2pi)
  runs from 0.81 to 4.68. The observed narrowing (sd 0.371 vs 0.422, fewer spacings below 0.5 and above 2.0, both
  at P ~ 0.007) is consistent with the known behaviour of low zeros, which are more rigid than GUE (the number
  variance saturates and the small-u pair correlation is depleted). Nothing here distinguishes \"GUE plus
  finite-height corrections\" from a slightly different law; 400 spacings cannot."
- C2 "**The asymptotic exponents are not directly observable with M = 399.** Below Delta = 0.3 there are 4 spacings,
  below 0.2 none, so any exponent fit lives at Delta ~ 0.25-0.75 where the GUE log-slope is already 3.6-3.8. The
  comparison made is fit-against-fit at the same thresholds. The bootstrap resamples spacings independently, which
  ignores their (weak) correlations, so the bands are indicative only."
- C3 "**Riemann-Siegel accuracy.** With the main sum and C0 only, |Z_RS - Z| is 2e-3 to 1e-2 for t < 35 and 7e-5 at
  t = 700; zero ordinates are off by up to 7.5e-3 (n = 3) and typically 2e-4. That is irrelevant for the statistics
  (counts and exponents unchanged, fractions shift by <= 3e-5) but the ordinates in the analysis column are the
  Euler-Maclaurin-verified ones, good to ~1e-9. The tabulated comparison values are quoted from memory of the
  standard tables (9 decimals) and agree with the Euler-Maclaurin ordinates to 3e-10, which also certifies them."
- C4 "**Completeness of the zero list** rests on the count argument (414 found below 700 vs theta(700)/pi + 1 =
  414.56; Gram-point bookkeeping; no near-miss on a grid of 0.02 mean spacings), not on a Turing-style proof. A
  missed close pair would show up as an implied S(T) of about -2.5, which is not seen anywhere."
- C5 "The surmise is used where the task asked for it; the exact sine-kernel law is given alongside and differs from
  the surmise by < 0.004 in both fractions on this ladder (and by 1.5 % in the small-s coefficient of p(s))."

Further caveats stated inside the body of `N/RESULTS.md`:

- C6 Small-sample note on the binned pair correlation (F6.4): "Each bin expects only ~40 pairs at u ~ 1 (and 0.4-20
  pairs for u < 0.5)".
- C7 The excess of the fitted exponent over GUE is a modest effect: "it is a ~2-2.5 sigma effect on 400 zeros and is
  in the direction expected for low zeros (section 6), not a different universality class."
- C8 The $\Delta^4$ and the constant $32/3\pi^2$ belong to different quantities: "(The Delta^4 belongs to the mass
  and the 32/3pi^2 to the count; the two should not be combined.)"
- C9 The theoretical slopes in the fit table are finite-window slopes, not asymptotic exponents: "(The theoretical
  columns are the same least-squares log-log slope evaluated on the exact laws at the same thresholds: the Delta^4 /
  Delta^2 asymptotics are only reached as Delta -> 0, and at Delta ~ 0.5 the local GUE slope is already below 4.)"

From `N/CUBE_NUMERIC.md`, "Caveats" (K1 to K5), quoted in full:

- K1 "**400 zeros only.** The counts below x = 0.5 rest on 29 pairs, below 0.3 on 4; the curve is noisy there and the
  fitted slope has a bootstrap band of roughly +-0.5 (RESULTS.md)."
- K2 "**The asymptotic cubic regime is not reached.** Even for GUE the log-slope is already 2.6-2.9 on the fit
  window; the data contain no pair below 0.2434, where the x^3 law would live. \"Slope 3\" is the small-x
  prediction, not an observed quantity."
- K3 "**GUE is a conjecture for zeta** (Montgomery's pair-correlation conjecture, proved only for test functions with
  Fourier support in (-1, 1)); the cubic law is what GUE predicts, not a theorem about the zeros."
- K4 "**The cube's off-axis part is empty here by construction**: all 400 zeros are on the line and simple, and RH is
  verified numerically to heights far beyond gamma_400 = 679.7, so the band, reservoir and 7/8-face zones of panel A
  are drawn to show where mass *would* go (an off-line zero rho contributes, with its mirror 1 - conj(rho), ordered
  pairs at delta = +-(Re rho - 1/2) with s = 0, i.e. an off-diagonal atom at the origin of the s axis and points off
  the axis); Delta = 1/8 is illustrative and the zone labels (gap hypothesis open; reservoir O(T^(1-c)) proved) are
  the status of the statements, not features of the data."
- K5 "The preview PNG is a rough rasterisation (DejaVu Sans instead of the SVG's font stack, dashed strokes drawn
  solid and lighter); the SVG is the figure."

From the ledger (`L`):

- L1 "**This is exploration, not a theorem**, and it concerns the spacing of the ordinates, not the real parts."
- L2 "exploration only." (the cube numerics entry).

Reviewer notes added by this sheet (not statements of the notes; use only as cautions, do not attribute to the
record):

- R1 The KS p-values (F5.3) and the count tail probabilities (F4.10) are computed as if the 399 spacings were
  independent draws. The notes make the independence caveat only for the bootstrap (C2: "ignores their (weak)
  correlations, so the bands are indicative only"). The same qualification applies to those p-values; the paper
  should call all of them indicative.
- R2 The notes report several one-sided tail probabilities at thresholds chosen after looking at the data and
  mention no adjustment for that (the word "multiple" does not occur in `N/RESULTS.md` or
  `N/CUBE_NUMERIC.md`). The P = 0.007 values should not be presented as significance tests.
- R3 The word "certifies" in C3 is too strong for values typed from memory and compared at eleven ordinates. A sober wording:
  the Euler-Maclaurin ordinates of $\gamma_1, \dots, \gamma_{10}$ and $\gamma_{100}$ agree with the commonly
  tabulated nine-decimal values to within $3.3 \times 10^{-10}$.
- R4 That all zeros up to height 700 are simple and on the line is a classical computational fact with a
  literature; the notes' own argument is the non-rigorous count check of C4. The paper should cite the literature
  for it (key needed, see section 11) and present the notes' check as a consistency check only.

## 9. Figures

The SVG files are the figures (K5: "the SVG is the figure"); the PNG files next to them are rough previews made
for layout checking and should not be used in the paper.

### Figure A: `N/cascade.svg`

- Path: `/home/joeyxyxyz/repos/qrh-comparator-receipts/notes/density-field-2026-11-03/numeric/cascade.svg`
  (39127 bytes, viewBox 980 x 500; sha256 in F1.5).
- What it contains. Evidence: `N/RESULTS.md` section 7, "panel A is the cumulative reservoir fraction h_Delta / sum s
  versus Delta (empirical staircase with one step per spacing, ladder thresholds as dots carrying their counts in
  tooltips, exact GUE and Poisson curves) with a log-log inset of the small-threshold region showing the fitted
  slope 4.5 against 3.6 (GUE) and 1.7 (Poisson) on the same points; panel B is the spacing histogram (bin 0.2)
  against the Wigner surmise and e^(-s)."
- Text embedded in the figure (read from the SVG): title "First 400 nontrivial zeros of zeta, read through the MNF
  threshold cascade"; "Ordinates by Riemann-Siegel (C0 term), verified by Euler-Maclaurin. Panel A uses the exact
  GUE law, panel B the Wigner surmise."; "reservoir empty up to D = 0.243:"; "0 below 0.2 (GUE 3.4, Poisson 72)";
  "4 below 0.3 (GUE 11.0)"; "29 below 0.5 (GUE 45.1)"; "zeros slope 4.5 [4.1, 5.0]"; "GUE 3.6, Poisson 1.7 here";
  "KS distance of the spacing CDF: GUE exact 0.051 (p ~ 0.25), surmise 0.049 (p ~ 0.28), Poisson 0.329 (p ~ 3e-38).
  Trace delta* = max s = 2.201."; "Hover the dots and bars for the counts."
- Proposed caption:

  > **Figure 1 (exploratory).** Normalized spacings $s_n = (\gamma_{n+1}-\gamma_n)\log(\gamma_n/2\pi)/(2\pi)$ of the
  > first 400 nontrivial zeros of $\zeta$ ($n = 1,\dots,399$; ordinates located by the Riemann-Siegel formula and
  > re-located by Euler-Maclaurin summation). Panel A: the fraction $h_\Delta/\sum_n s_n$ of the total spacing length
  > carried by spacings shorter than the threshold $\Delta$ (in the figure, $D$), as an empirical staircase with one
  > step per spacing, against the same quantity for the exact GUE nearest-neighbor law and for Poisson spacings; dots
  > mark the thresholds of the table in the text. No spacing is below 0.243. Inset: the same data on log-log axes for
  > $\Delta = 0.25, 0.30, \dots, 0.75$; the least-squares slope is 4.5 (bootstrap 16-84 % band $[4.1, 5.0]$), against
  > 3.6 for GUE and 1.7 for Poisson fitted at the same thresholds. Panel B: histogram of the 399 spacings (bin width
  > 0.2) against the Wigner surmise and $e^{-s}$. In-figure labels use the author's working vocabulary ("reservoir",
  > "hidden mass", "trace", "MNF threshold cascade"), defined in the text. The figure shows the GUE-like level
  > repulsion that is well known for the low zeros; it concerns the spacing of ordinates on the critical line, was
  > computed in double precision without certified error bounds, and proves nothing.

### Figure B: `N/cube.svg`

- Path: `/home/joeyxyxyz/repos/qrh-comparator-receipts/notes/density-field-2026-11-03/numeric/cube.svg`
  (67225 bytes, viewBox 1000 x 620; sha256 in F1.5).
- What it contains. Evidence: `N/CUBE_NUMERIC.md`, "Panel A of the figure sketches the cube in oblique projection
  with the (delta1, delta2) zones shaded on the floor and the band extruded as a translucent column: the line delta =
  0 (the 0.0e zone, carrying all the mass), the band 0 < |delta| < Delta (empty under the gap hypothesis, open), the
  reservoir |delta| >= Delta (O(T^(1-c)) zeros, proved), and the 7/8 face |delta| >= 3/8; zones are by max(|delta1|,
  |delta2|) and Delta = 1/8 is illustrative. The ordered pairs with |s| <= 3 are drawn as a density strip along the s
  axis (bins of 0.1 in s, bar half-width proportional to the count; nothing is jittered), 2012 ordered pairs in all;
  the hole around the atom is the empty bins [-0.2, 0.2)." Panel B is the curve $y(x)$ of F7.5 on log-log axes with
  the GUE, Poisson and cubic reference curves and the fit window $[0.25, 0.75]$.
- Text embedded in the figure (read from the SVG): title "The strip cube: ordered pairs of the first 400 nontrivial
  zeros of zeta"; "A. The cube (delta1, delta2, s) and its support under RH"; "line delta = 0 (the 0.0e zone): the s
  axis, carries all the mass"; "band 0 < |delta| < Delta: empty under the gap hypothesis (open)"; "reservoir |delta|
  >= Delta: O(T^(1-c)) zeros, proved"; "7/8 face |delta| >= 3/8"; "Delta = 1/8 in the drawing is illustrative; zones
  by max(|delta1|, |delta2|)"; "the atom: diagonal mass 400," / "off-diagonal 0"; "hole |s| < 0.243: no pair" /
  "(level repulsion)"; "B. The on-line slice: integrated pair count per zero (log-log)"; "The small-x cubic law is
  the GUE prediction for zeta, not a theorem."; "zeros 3.71"; "GUE, same points 2.67"; "Poisson 1.00"; "cubic
  asymptote 3 (GUE, x -> 0)"; "R2 ~ (pi^2/3) u^2 is Montgomery's" / "conjecture; GUE is already flatter here.";
  "x = 2, 3: zeros 3.01, 5.03" / "GUE 3.05, 5.03; 2x - 1 = 3, 5"; footer "400 zeros, 2012 ordered pairs; x = 0.5: 29
  nn pairs = 58 ordered = 0.145/zero (GUE 0.226, Poisson 1); hole 0.243; slope on [0.25, 0.75]: zeros 3.71, GUE 2.67,
  Poisson 1; atom 400 / 0."
- Proposed caption:

  > **Figure 2 (exploratory).** The pair measure of the first 400 nontrivial zeros of $\zeta$ in the coordinates
  > $(\beta-\tfrac12,\ \beta'-\tfrac12,\ s)$ with $s = (\gamma-\gamma')\log(\gamma_{\min}/2\pi)/(2\pi)$, which the
  > author calls the "cube". Panel A is a schematic: since all 400 zeros are simple and on the critical line, the
  > empirical measure lies on the $s$-axis; the 2012 ordered pairs of distinct zeros with $0<|s|\le 3$ are drawn as a
  > density strip in bins of 0.1, with the diagonal atom of mass 400 at the origin and no pair with $|s| < 0.243$.
  > The shaded zones off the axis contain no data: they show where an off-line zero would place mass, their labels
  > give the status of statements discussed in the text (the gap hypothesis is open; the count of zeros at distance at
  > least $\Delta$ from the line is $O(T^{1-c})$ by the formalized density estimate), and $\Delta = 1/8$ is chosen
  > only for the drawing. Panel B: the integrated pair count per zero,
  > $y(x) = \#\{(\rho,\rho') : \rho\neq\rho',\ 0<|s|\le x\}/400$, on log-log axes, against the GUE prediction
  > $2\int_0^x (1-(\sin\pi u/\pi u)^2)\,du$, the Poisson line $2x$ and the cubic reference $(2\pi^2/9)x^3$. At
  > $x = 0.5$ the zeros give 0.145 (GUE 0.226, Poisson 1); the least-squares log-log slope on $[0.25, 0.75]$ is 3.71
  > for the zeros and 2.67 for GUE at the same points. The cubic small-distance law is a prediction of the GUE
  > conjecture, not a theorem, and the data contain no pair in the range where it would hold. The figure reproduces
  > known behavior of the low zeros and proves nothing.

- Figure handling notes: (i) both SVGs carry hover tooltips and the line "Hover the dots and bars for the counts",
  which do nothing in a PDF; (ii) labels are ASCII ("gamma", "pi", "Delta", "D") and use the author's vocabulary,
  including "the 0.0e zone", which neither `N/RESULTS.md` nor `N/CUBE_NUMERIC.md` defines; (iii) the SVG font stack
  is "Inter, -apple-system, 'Segoe UI', Helvetica, Arial, sans-serif", so the rendering depends on the converter;
  (iv) in `cube_preview.png` the annotation "R2 ~ (pi^2/3) u^2 is Montgomery's conjecture; GUE is already flatter
  here." overlaps the plotted curves; check the converted figure; (v) the title of panel A says "its support under
  RH": the caption must keep the schematic status explicit, as above. (vi) On the machine where this sheet was
  written, none of `rsvg-convert`, `inkscape`, `cairosvg`, `magick`, `convert` or `pandoc` was on the shell's PATH
  (checked with `which` on 2026-11-10), so the conversion of the SVGs for the PDF is still to be arranged.

## 10. Independent recount made for this sheet

Script `WORK/facts/_check/recount.py` (reads `N/zeros.tsv`, `N/spacings.tsv`, `N/paircorr.tsv`; double precision).
It reproduced, to the digits printed in the notes:

- 400 strictly increasing ordinates, first 14.134725141735, last 679.742197882528; spacings recomputed from the
  `gamma_EM` column agree with `spacings.tsv` to 5e-7 (the file's rounding).
- max |C0 - EM| = 7.544e-03 at n = 3, mean 2.138e-04, 1.366e-03 for gamma > 100, 6.333e-04 for gamma > 300;
  max |C0..C4 - EM| = 3.134e-06 (at n = 1).
- sum 397.9771, mean 0.99744, standard deviation 0.3709 (with the $M-1$ divisor), median 0.9587, minimum 0.2434 at
  n = 363, maximum 2.2014 at n = 379, the five smallest spacings and their indices, $\log(\gamma/2\pi)$ from 0.81 to
  4.68.
- every count, $h_\Delta$, $\nu_\Delta$ and empirical fraction of the two threshold tables, and the Poisson columns.
- the fine-grid counts 2, 4, 6, 14, 21, 29, 40, 55, 70, 88, 114; slopes 4.52 (mass) and 3.71 (count); the surmise
  slopes 3.63 and 2.67; the Poisson slopes 1.71 and 0.79.
- KS distance 0.0494 to the surmise and 0.3285 to Poisson (the exact-GUE distance was not recomputed).
- the pair table of F7.8 in full (unordered counts 0, 0, 4, 29, 114, 224, 408, 602, 1006; GUE, Poisson and cubic
  columns), 3.965 at $x = 2.5$, 1006 = 399 adjacent + 607 non-adjacent, 2012 ordered pairs, slope 3.71 for the zeros
  and 2.67 for GUE.
- `paircorr.tsv` totals 599, 29, 222, 377.

One additional fact from the recount, not stated in this form in the notes: the closest non-adjacent pair has
$s = 1.1254$ in the smaller-ordinate unfolding. This supports the notes' sentence "below x = 1 every close pair is a
nearest-neighbour pair" (`N/CUBE_NUMERIC.md`). Not recomputed: the bootstrap bands, the exact-GUE columns, the KS
p-values, the tail probabilities, and the ordinates themselves.

## 11. Disagreements between sources, and references named in the notes

Disagreements (none changes a conclusion):

- D1 Size of the deviation from GUE. `L`: "fewer small and fewer large spacings, each a ≈2σ effect";
  `N/RESULTS.md` section 4: "a ~2-2.5 sigma effect"; the tail probabilities are "P = 0.007" each (F4.12). Prefer the
  numbers: 29 against 45.1 expected and 1 against 7.1 expected, each with one-sided tail probability 0.007 under the
  exact GUE law.
- D2 Extent of the table comparison. `L`: "checked against the standard tables to 3·10⁻¹⁰"; `N/RESULTS.md`: eleven
  ordinates, "values as recalled" (F2.9). Prefer the narrower statement of `N/RESULTS.md`.
- D3 Sign convention in one log. `N/rs_zeros.log`: "n=  3  gamma=25.018401  diff=-7.54e-03" under the heading "five
  largest C0-vs-EM discrepancies", whereas `N/zeros.tsv` column `diff_C0_minus_EM` has "+7.544e-03" for n = 3 and the
  self-check table has "+7.54e-03". The magnitude agrees; the log line uses the opposite sign. Quote magnitudes only.
- D4 Rounding of the same quantities across files: minimum spacing "0.24" / "0.243" / "0.2434"; KS distance to
  Poisson "0.33" / "0.329" / "0.3285"; its p-value "~ 3e-38" / "2.7e-38"; mass exponent "4.5" / "4.52" with band
  "[4.1, 5.0]" / "[4.07, 5.05]"; expected GUE count below 0.2 "3.3" (surmise, panel B of `cascade.svg`) and "3.4"
  (exact law, panel A). Use the table values of sections 4 to 7 and say which GUE law is meant.
- D5 Two unfoldings, two pair counts: 222 against 224 below distance 1 and 599 against 602 below distance 2 (F7.18).
- D6 Dates: 2026-11-03 in `N/RESULTS.md`, "2026-11-04 (morning)" for the same item in `L` (F1.3).

References the notes name, with no bibliographic detail given there (keys must come from
`WORK/facts/literature.md`; none is asserted here):

- Montgomery's pair-correlation conjecture and the function $1 - (\sin \pi u/\pi u)^2$ (`N/RESULTS.md` sections 5;
  `N/CUBE_NUMERIC.md` caveat 3; `REPO/DEPOSIT_MAP.md` writes "Montgomery 1973").
- Odlyzko's computations and tables of zeros, and the LMFDB zero tables (`N/RESULTS.md`: "Odlyzko's low-zero
  comparisons", "LMFDB/Odlyzko tables"; `REPO/NOTICE`: "Odlyzko / LMFDB tables").
- Berry and Bogomolny-Keating on finite-height corrections (`N/RESULTS.md`: "Berry / Bogomolny-Keating finite-height
  corrections").
- The Gaudin-Mehta nearest-neighbor spacing law and the Wigner surmise (`N/RESULTS.md` section 3).
- The Riemann-Siegel formula, Gram points and Gram's law, Euler-Maclaurin summation for $\zeta$, Turing's method
  (`N/RESULTS.md` sections 1 and 6).
- Numerical verification of RH to large height: `N/CUBE_NUMERIC.md` caveat 4 asserts "RH is verified numerically to
  heights far beyond gamma_400 = 679.7" and names no source.

## 12. What the paper may and may not say (summary for the section author)

May say, with the numbers above: the first 400 ordinates were recomputed in double precision by two independent
formulas; the 399 normalized spacings have no value below 0.243; their distribution is not rejected against the GUE
spacing law at this sample size (KS distance 0.051) and is far from Poisson (0.33); there are somewhat fewer very
small and very large spacings than the GUE limit predicts, which is the known direction for low zeros; finite-window
log-log slopes are 4.52 (band [4.07, 5.05]) for the length fraction and 3.71 (band [3.26, 4.23]) for the count,
against 3.62 and 2.67 for GUE on the same window.

May not say: that an exponent 4 or a cubic law was observed or confirmed (C2, K2); that the zeros "are" GUE (C1,
K3); that the deviation from GUE is a finding (C1, C7); that any of this bears on real parts, RH, the simplicity of
the zeros in general, or a zero-free strip (F0.2, K4); that the zero list is rigorously complete or the ordinates certified
(C4, F1.2, R3).
