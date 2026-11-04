# The first 400 nontrivial zeros of zeta, read through the MNF threshold cascade

Exploratory numerics, pure Python 3 (no numpy/mpmath), 2026-11-03.
Directory: `density-work/numeric/` (scripts `rs_zeros.py`, `gue_exact.py`, `mnf_analysis.py`, `make_svg.py`;
data `zeros.tsv`, `spacings.tsv`, `paircorr.tsv`, `summary.json`; figure `cascade.svg`; logs `*.log`).

## Summary

* 400 zeros located, gamma_1 = 14.134725 ... gamma_400 = 679.742198, giving M = 399 normalised spacings
  with mean 0.99744 and standard deviation 0.371 (GUE: 0.422, Poisson: 1).
* **The reservoir is empty below Delta = 0.24.** The smallest spacing is s_363 = 0.2434 (gamma_363 = 630.4739,
  gamma_364 = 630.8058). For Delta in {0.05, 0.1, 0.2} the hidden mass h_Delta is exactly 0 (n_below = 0 of 399),
  where Poisson would hide 19.5, 38.0 and 72.3 spacings respectively (P(0 | Poisson at 0.2) = 4e-32)
  and GUE 0.1, 0.4 and 3.4 (P(0 | GUE at 0.2) = 0.034).
* **The cascade of hidden mass rises like a high power of Delta, not like Delta^2.** A log-log fit of h_Delta / sum s
  on Delta = 0.25, 0.30, ..., 0.75 (11 thresholds, n_below from 2 to 114) gives exponent **4.52**
  (bootstrap 16-84 %: [4.07, 5.05]). The same fit applied to the exact GUE law on the same thresholds gives 3.62,
  to the Wigner surmise 3.63, and to Poisson 1.71. So the empirical cascade is at least as steep as GUE
  (asymptotically Delta^4) and far from Poisson (Delta^2).
* Over the whole ladder the zeros track GUE: Kolmogorov-Smirnov distance of the spacing CDF 0.051 from the exact
  GUE law (p ~ 0.25, M = 399), 0.049 from the surmise (p ~ 0.28), 0.33 from Poisson (p ~ 3e-38).
* Within GUE there is a visible finite-height signature: *fewer* small spacings and *fewer* large spacings than GUE
  (29 below 0.5 vs 45.1 expected, P = 0.007; 1 above 2.0 vs 7.1 expected, P = 0.007; sd 0.371 [0.357, 0.384] vs 0.422).
  The first few hundred zeros are known to be slightly more rigid than the GUE limit (Odlyzko's low-zero
  comparisons; Berry / Bogomolny-Keating finite-height corrections), and that is the direction seen here.
* The trace delta* (largest threshold with a nonzero reading) is the maximum spacing, **2.2014** (s_379, between
  gamma_379 = 650.6687 and gamma_380 = 653.6496); GUE expects 2.7 spacings beyond it among 399 (P(<=1) = 0.26),
  Poisson expects 44.
* Pair correlation on (0, 2) in bins of 0.1 follows Montgomery's 1 - (sin(pi u)/(pi u))^2 within the
  sqrt(n) noise of 599 pairs: 29 pairs with u < 0.5 (GUE 45 +- 7, Poisson 199), 222 with u < 1 (GUE 218 +- 15,
  Poisson 399), 377 in [1, 2) (GUE 388 +- 20, Poisson 398).

## 1. Zeros: method and verification

**Riemann-Siegel.** Z(t) = 2 sum_(n<=N) n^(-1/2) cos(theta(t) - t log n) + (-1)^(N-1) (t/2pi)^(-1/4) C0(p),
N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, C0(p) = Psi(p) = cos(2pi(p^2 - p - 1/16)) / cos(2pi p);
theta(t) = (t/2) log(t/2pi) - t/2 - pi/8 + 1/(48t) + 7/(5760 t^3) + 31/(80640 t^5) + 127/(430080 t^7) + 511/(1216512 t^9).
theta was checked against Im log Gamma(1/4 + it/2) - (t/2) log pi computed by complex Stirling with recurrence:
agreement 2e-15 (t = 14) to 5e-13 (t = 700) mod 2pi.

**Scan.** Gram points g_n (theta(g_n) = n pi) were computed by Newton; each Gram interval was cut into 48 grid points
(19,885 points on [12, 700], final step 0.028 in t, i.e. about 0.02 mean spacings), Z(C0) evaluated at each, and
every sign change bisected to 1e-12. A near-miss check (local minima of |Z| below 0.08 with no sign change,
refined on a 400-point sub-grid) found nothing. 414 zeros lie below T = 700 against theta(700)/pi + 1 = 414.557
(so S(700) = -0.56, normal); the running counts agree with the Riemann-von Mangoldt smooth term at every
check-point, and exactly 12 of the 414 Gram points below 700 violate Gram's law (count below g_n != n + 1):

```
  N(  100) found =   29   theta(T)/pi + 1 =    29.002   S(T) implied = -0.002
  N(  200) found =   79   theta(T)/pi + 1 =    79.193   S(T) implied = -0.193
  N(  300) found =  138   theta(T)/pi + 1 =   137.712   S(T) implied = +0.288
  N(  400) found =  202   theta(T)/pi + 1 =   201.639   S(T) implied = +0.361
  N(  500) found =  269   theta(T)/pi + 1 =   269.587   S(T) implied = -0.587
  N(  600) found =  341   theta(T)/pi + 1 =   340.739   S(T) implied = +0.261
  N(  700) found =  414   theta(T)/pi + 1 =   414.557   S(T) implied = -0.557
  Gram points below 700.0: 414; with count(zeros < g_n) != n+1: 12  (Gram-law failures, expected a few dozen)
```

**Accuracy.** Each of the first 400 zeros was re-located with two independent evaluators started from the C0 value:
Riemann-Siegel with the four further correction terms C1..C4 (derivatives of Psi taken by Cauchy integrals on a
circle, because series division is unstable near p = 1/4, 3/4), and Euler-Maclaurin summation of zeta(1/2 + it)
with ~t + 30 terms and 10 Bernoulli terms (formula-independent, ~1e-13 in Z). Values of Z itself:

```
== Z(t): Riemann-Siegel (C0 only / C0..C4) vs Euler-Maclaurin ==
   t       Z_RS(C0)        Z_RS(C0..C4)     Z_EM            Im(e^{i th} zeta)  |RS0-EM|   |RS4-EM|
    14.0  -0.1078305681  -0.1056286256  -0.1056262678  -1.8e-15   2.2e-03   2.4e-06
    17.5  +2.3043230451  +2.3018422245  +2.3018457553  +7.7e-15   2.5e-03   3.5e-06
    21.0  +0.0277653427  +0.0250809141  +0.0250838670  -1.9e-15   2.7e-03   3.0e-06
    25.0  -0.0251194421  -0.0148742265  -0.0148724839  -1.3e-15   1.0e-02   1.7e-06
    30.0  +0.5994592581  +0.5960275739  +0.5960285192  +3.2e-15   3.4e-03   9.5e-07
    40.0  -1.3086736691  -1.3088822771  -1.3088823935  -6.3e-15   2.1e-04   1.2e-07
    60.0  +0.5871238821  +0.5869506412  +0.5869504907  +1.5e-14   1.7e-04   1.5e-07
   100.0  +2.6894071203  +2.6926970194  +2.6926970567  -1.5e-14   3.3e-03   3.7e-08
   150.0  -0.0912046031  -0.0910109107  -0.0910109233  +3.0e-15   1.9e-04   1.3e-08
   250.0  -0.9180025624  -0.9186334201  -0.9186334184  -3.3e-14   6.3e-04   1.8e-09
   400.0  -0.0992457965  -0.0982811291  -0.0982811283  -5.4e-15   9.6e-04   8.2e-10
   550.0  +1.7527094680  +1.7529844849  +1.7529844847  -4.6e-13   2.8e-04   1.5e-10
   700.0  -0.9472748099  -0.9472035973  -0.9472035973  +3.8e-13   7.1e-05   3.7e-11
```

Self-check against tabulated ordinates (first ten and the 100th, values as recalled from the LMFDB/Odlyzko tables):

```
== self-check against tabulated zeros (LMFDB/Odlyzko values as recalled) ==
     n   gamma_RS(C0)      gamma_EM          tabulated        RS-tab      EM-tab
     1   14.137196099   14.134725142   14.134725142   +2.47e-03   -2.65e-10
     2   21.024376714   21.022039639   21.022039639   +2.34e-03   -2.28e-10
     3   25.018401401   25.010857580   25.010857580   +7.54e-03   +1.46e-10
     4   30.427645833   30.424876126   30.424876126   +2.77e-03   -1.40e-10
     5   32.932561762   32.935061588   32.935061588   -2.50e-03   -2.61e-10
     6   37.586861886   37.586178159   37.586178159   +6.84e-04   -1.74e-10
     7   40.918839130   40.918719012   40.918719012   +1.20e-04   +1.48e-10
     8   43.326490197   43.327073281   43.327073281   -5.83e-04   -8.50e-11
     9   48.006380332   48.005150881   48.005150881   +1.23e-03   +1.67e-10
    10   49.772640645   49.773832478   49.773832478   -1.19e-03   -3.28e-10
   100   236.524327123   236.524229666   236.524229666   +9.75e-05   -1.84e-10
```

So: C0-only Riemann-Siegel places the first three zeros at 14.137196, 21.024377, 25.018401 against 14.134725,
21.022040, 25.010858, i.e. errors of +2.5e-3, +2.3e-3, +7.5e-3 - exactly the size of the omitted
(t/2pi)^(-3/4) C1 term at these heights. Over all 400 zeros: max |gamma(C0) - gamma(EM)| = 7.5e-3 (n = 3), mean 2.1e-4,
at most 1.4e-3 for gamma > 100 and 6.3e-4 for gamma > 300. With C1..C4 the maximum discrepancy from Euler-Maclaurin
drops to 3.1e-6, and the Euler-Maclaurin ordinates agree with the tabulated values to <= 3.3e-10 (the tables carry
nine decimals). `zeros.tsv` holds all three columns; the analysis below uses the Euler-Maclaurin-verified column.
Re-running everything on the raw C0 column changes no count in any ladder row, moves every mass fraction by
<= 3e-5, the minimum spacing from 0.2434 to 0.2425, the KS distance from 0.0494 to 0.0496 and no fitted exponent at
two decimals (`c0_variant/`).

## 2. Normalised spacings

s_n = (gamma_(n+1) - gamma_n) log(gamma_n / 2pi) / 2pi, n = 1..399 (`spacings.tsv`).

| quantity | value | n |
|---|---|---|
| number of spacings M | 399 | from 400 zeros |
| sum s = total reading at Delta = 0 | 397.977 | 399 |
| mean | 0.99744 | 399 (unit mean expected from the density log(t/2pi)/2pi) |
| standard deviation | 0.3709, bootstrap 16-84 % [0.357, 0.384] | 399; GUE 0.4221, Poisson 1 |
| median | 0.9587 | 399; exact GUE median 0.9628 |
| minimum (first non-empty threshold) | 0.2434 | s_363: gamma_363 = 630.4739, gamma_364 = 630.8058 |
| next smallest | 0.2471, 0.2911, 0.2965, 0.3244 | s_315, s_212, s_298, s_186 |
| maximum = trace delta* | 2.2014 | s_379: gamma_379 = 650.6687, gamma_380 = 653.6496 |

## 3. MNF threshold ladder

Vocabulary: for a threshold Delta, the **nullified reading** is nu_Delta = sum over s >= Delta of s, the **hidden
(reservoir) mass** is h_Delta = sum over s < Delta of s, and the **trace** delta* = sup{Delta : nu_Delta > 0} = max s.
Theory columns: GUE surmise p(s) = (32/pi^2) s^2 exp(-4s^2/pi) (reservoir fraction 1 - (1 + 4Delta^2/pi) exp(-4Delta^2/pi),
count fraction erf(2Delta/sqrt(pi)) - (4Delta/pi) exp(-4Delta^2/pi); both also checked by Simpson integration to 1e-8);
GUE exact = the sine-kernel (Gaudin-Mehta) nearest-neighbour law from the Fredholm determinant E_2(0; s)
(`gue_exact.py`: E_2(0;1) = 0.170217, small-s series matched to 5e-10, normalisation to 1e-12, surmise within 1.5 %
for s < 2); Poisson p(s) = e^(-s) (reservoir fraction 1 - (1 + Delta) e^(-Delta), count fraction 1 - e^(-Delta)).

| Delta | n_below = #{s<Delta} | n_above = #{s>=Delta} | M | h_Delta = sum_{s<Delta} s | nu_Delta = sum_{s>=Delta} s | h_Delta/sum s (empirical) | GUE surmise | GUE exact | Poisson |
|---|---|---|---|---|---|---|---|---|---|
| 0.05 | 0 | 399 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00001 | 0.00001 | 0.00121 |
| 0.1 | 0 | 399 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00008 | 0.00008 | 0.00468 |
| 0.2 | 0 | 399 | 399 | 0.0000 | 397.9771 | 0.00000 | 0.00125 | 0.00127 | 0.01752 |
| 0.3 | 4 | 395 | 399 | 1.0780 | 396.8991 | 0.00271 | 0.00608 | 0.00616 | 0.03694 |
| 0.5 | 29 | 370 | 399 | 11.5369 | 386.4402 | 0.02899 | 0.04109 | 0.04145 | 0.09020 |
| 0.75 | 114 | 285 | 399 | 66.3998 | 331.5773 | 0.16684 | 0.16145 | 0.16210 | 0.17336 |
| 1 | 224 | 175 | 399 | 164.0166 | 233.9605 | 0.41213 | 0.36367 | 0.36368 | 0.26424 |
| 1.5 | 359 | 40 | 399 | 329.5385 | 68.4386 | 0.82803 | 0.77973 | 0.77739 | 0.44217 |
| 2 | 398 | 1 | 399 | 395.7757 | 2.2014 | 0.99447 | 0.96259 | 0.96108 | 0.59399 |

| Delta | n_below | M | #{s<Delta}/M (empirical) | GUE surmise | GUE exact | Poisson | expected n_below: GUE surmise | GUE exact | Poisson |
|---|---|---|---|---|---|---|---|---|---|
| 0.05 | 0 | 399 | 0.00000 | 0.00013 | 0.00014 | 0.04877 | 0.1 | 0.1 | 19.5 |
| 0.1 | 0 | 399 | 0.00000 | 0.00107 | 0.00109 | 0.09516 | 0.4 | 0.4 | 38.0 |
| 0.2 | 0 | 399 | 0.00000 | 0.00839 | 0.00850 | 0.18127 | 3.3 | 3.4 | 72.3 |
| 0.3 | 4 | 399 | 0.01003 | 0.02725 | 0.02760 | 0.25918 | 10.9 | 11.0 | 103.4 |
| 0.5 | 29 | 399 | 0.07268 | 0.11200 | 0.11306 | 0.39347 | 44.7 | 45.1 | 157.0 |
| 0.75 | 114 | 399 | 0.28571 | 0.30204 | 0.30359 | 0.52763 | 120.5 | 121.1 | 210.5 |
| 1 | 224 | 399 | 0.56140 | 0.53305 | 0.53390 | 0.63212 | 212.7 | 213.0 | 252.2 |
| 1.5 | 359 | 399 | 0.89975 | 0.87447 | 0.87336 | 0.77687 | 348.9 | 348.5 | 310.0 |
| 2 | 398 | 399 | 0.99749 | 0.98295 | 0.98229 | 0.86466 | 392.2 | 391.9 | 345.0 |

trace delta* = max spacing = 2.2014; nu_Delta = 0 for Delta > delta*, and nu_Delta = sum s = 397.9771 for Delta <= min s = 0.2434

Tail probabilities of the observed counts (Poisson approximation to the binomial, `tail_stats.log`):

| threshold | observed n | GUE exact expects | P(<= n \| GUE) | Poisson expects | P(<= n \| Poisson) |
|---|---|---|---|---|---|
| s < 0.2 | 0 | 3.4 | 0.034 | 72.3 | 4e-32 |
| s < 0.3 | 4 | 11.0 | 0.015 | 103.4 | 6e-39 |
| s < 0.5 | 29 | 45.1 | 0.007 | 157.0 | 4e-36 |
| s >= 2.0 | 1 | 7.1 | 0.007 | 54.0 | 2e-22 |
| s >= delta* = 2.2014 | 1 | 2.7 | 0.26 | 44.1 | 3e-18 |

| law | D_M | approx p-value |
|---|---|---|
| GUE surmise | 0.0494 | 0.277 |
| GUE exact | 0.0508 | 0.247 |
| Poisson | 0.3285 | 2.7e-38 |

## 4. What the cascade shows

**Level repulsion is an empty reservoir near Delta -> 0.** Under Poisson the hidden mass below Delta is
h_Delta / sum s = 1 - (1 + Delta) e^(-Delta) ~ Delta^2 / 2 and the hidden count is ~ Delta: the reservoir fills
from the very first threshold (19.5 of 399 spacings expected below 0.05). Under GUE, p(s) ~ c s^2 at small s, so
the count below Delta is ~ (c/3) Delta^3 and the mass is ~ (c/4) Delta^4: with the surmise c = 32/pi^2,
count ~ (32/3pi^2) Delta^3 = 1.081 Delta^3 and mass ~ (8/pi^2) Delta^4 = 0.811 Delta^4; with the exact law
c = pi^2/3, count ~ (pi^2/9) Delta^3 = 1.097 Delta^3 and mass ~ (pi^2/12) Delta^4 = 0.822 Delta^4.
(The Delta^4 belongs to the mass and the 32/3pi^2 to the count; the two should not be combined.)

The zeros do this and a little more. The first three rungs of the ladder (0.05, 0.1, 0.2) read the full total,
nu_Delta = 397.977, with nothing hidden: 0 of 399. The reservoir opens only at the 0.3 rung, with 4 spacings
(mass 1.078, fraction 0.27 %, against 0.62 % GUE and 3.69 % Poisson), reaches 29 spacings (2.90 %, GUE 4.15 %,
Poisson 9.02 %) at 0.5, and only catches up with GUE around Delta = 0.75 (114 spacings, 16.7 % vs 16.2 %), after
which it runs *above* GUE (224 spacings and 41.2 % at Delta = 1 vs 36.4 %; 359 and 82.8 % at 1.5 vs 77.7 %) because
the distribution is narrower than GUE on both sides.

**Fitted exponent.** Least-squares log-log slopes of h_Delta / sum s versus Delta, with the identical fit applied to
the theoretical laws at the same thresholds (the pure Delta^4 / Delta^2 regime is only reached as Delta -> 0; at
Delta ~ 0.5 the local GUE slope is already 3.6-3.8, and the empirical slope has to be compared with that, not with 4):

| thresholds used | n_below at each threshold | fitted exponent of h/sum s | bootstrap 16-84 % | same fit applied to GUE surmise / exact / Poisson | fitted exponent of count fraction | bootstrap 16-84 % | GUE surmise / exact / Poisson |
|---|---|---|---|---|---|---|---|
| ladder points 0.2, 0.3, 0.5 (fit uses the 2 non-empty) | 0, 4, 29 | 4.64 | [3.77, 5.79] (1962 resamples) | 3.81 / 3.80 / 1.79 | 3.88 | [3.07, 5.02] | 2.83 / 2.82 / 0.84 |
| ladder points 0.2, 0.3, 0.5, 0.75 (fit uses the 3 non-empty) | 0, 4, 29, 114 | 4.50 | [4.01, 5.23] (1969 resamples) | 3.68 / 3.68 / 1.74 | 3.67 | [3.19, 4.40] | 2.72 / 2.71 / 0.81 |
| fine grid 0.20..0.60 step 0.05 (fit uses the 8 non-empty) | 0, 2, 4, 6, 14, 21, 29, 40, 55 | 4.62 | [3.96, 5.33] (1715 resamples) | 3.76 / 3.76 / 1.77 | 3.86 | [3.21, 4.56] | 2.79 / 2.78 / 0.83 |
| fine grid 0.25..0.75 step 0.05 (fit uses the 11 non-empty) | 2, 4, 6, 14, 21, 29, 40, 55, 70, 88, 114 | 4.52 | [4.07, 5.05] (1723 resamples) | 3.63 / 3.62 / 1.71 | 3.71 | [3.26, 4.23] | 2.67 / 2.67 / 0.79 |

(The theoretical columns are the same least-squares log-log slope evaluated on the exact laws at the same thresholds: the Delta^4 / Delta^2 asymptotics are only reached as Delta -> 0, and at Delta ~ 0.5 the local GUE slope is already below 4.)

The robust statement: on every choice of thresholds the empirical exponent (4.5-4.6, with 16-84 % bootstrap
bands of roughly +-0.5) lies **above** the GUE value for the same thresholds (3.6-3.8) and far above Poisson (1.7-1.8);
for the hidden count the empirical exponent is 3.7-3.9 against GUE 2.7-2.8 and Poisson 0.8. The excess over GUE is
the same deficit of small spacings seen in the ladder: it is a ~2-2.5 sigma effect on 400 zeros and is in the
direction expected for low zeros (section 6), not a different universality class.

**Histogram** (bin 0.2; the figure's panel B):

| bin | n | empirical density | GUE surmise (bin avg) | GUE exact | Poisson | expected n GUE / Poisson |
|---|---|---|---|---|---|---|
| [0.0, 0.2) | 0 | 0.000 | 0.042 | 0.043 | 0.906 | 3.3 / 72.3 |
| [0.2, 0.4) | 14 | 0.175 | 0.265 | 0.267 | 0.742 | 21.1 / 59.2 |
| [0.4, 0.6) | 41 | 0.514 | 0.587 | 0.590 | 0.608 | 46.8 / 48.5 |
| [0.6, 0.8) | 82 | 1.028 | 0.844 | 0.844 | 0.497 | 67.3 / 39.7 |
| [0.8, 1.0) | 87 | 1.090 | 0.929 | 0.925 | 0.407 | 74.1 / 32.5 |
| [1.0, 1.2) | 63 | 0.789 | 0.836 | 0.831 | 0.333 | 66.7 / 26.6 |
| [1.2, 1.4) | 50 | 0.627 | 0.636 | 0.633 | 0.273 | 50.8 / 21.8 |
| [1.4, 1.6) | 33 | 0.414 | 0.418 | 0.416 | 0.224 | 33.3 / 17.8 |
| [1.6, 1.8) | 20 | 0.251 | 0.239 | 0.240 | 0.183 | 19.1 / 14.6 |
| [1.8, 2.0) | 8 | 0.100 | 0.120 | 0.122 | 0.150 | 9.6 / 12.0 |
| [2.0, 2.2) | 0 | 0.000 | 0.054 | 0.055 | 0.123 | 4.3 / 9.8 |
| [2.2, 2.4) | 1 | 0.013 | 0.021 | 0.022 | 0.100 | 1.7 / 8.0 |
| [2.4, 2.6) | 0 | 0.000 | 0.007 | 0.008 | 0.082 | 0.6 / 6.6 |
| [2.6, 2.8) | 0 | 0.000 | 0.002 | 0.003 | 0.067 | 0.2 / 5.4 |
| [2.8, 3.0) | 0 | 0.000 | 0.001 | 0.001 | 0.055 | 0.1 / 4.4 |
| [3.0, 3.2) | 0 | 0.000 | 0.000 | 0.000 | 0.045 | 0.0 / 3.6 |
spacings >= 3.2: 0

The peak bins [0.6, 1.0) hold 169 spacings where GUE expects 141.4 and Poisson 72.2; both tails are thinner than GUE
([0.0, 0.4): 14 vs 24.4; [2.0, 3.2): 1 vs 6.9).

## 5. Pair correlation at small distance

Unfolded ordinates x_n = theta(gamma_n)/pi + 1 (the smooth counting function; this unfolding and the local-density
normalisation used for the spacings agree to O(1/gamma)). All pairs i < j with x_j - x_i < 2 were binned in steps of
0.1 and divided by (L - u_mid) x 0.1 with L = x_400 - x_1 = 398.96 (the edge correction L - u instead of L is 0.5 %).
GUE column = bin average of Montgomery's 1 - (sin(pi u)/(pi u))^2 by Simpson integration; Poisson = 1.

window length L = x_400 - x_1 = 398.959; pairs with distance < 2: 599; empirical R2 = count / ((L - u_mid) * 0.1); error bar = sqrt(count) on the same scale

| bin u | pair count n | empirical R2 | +- (Poisson sqrt n) | GUE 1-(sin pi u/pi u)^2 (bin average) | Poisson | expected n (GUE) | expected n (Poisson) |
|---|---|---|---|---|---|---|---|
| [0.0, 0.1) | 0 | 0.000 | 0.025 | 0.011 | 1.000 | 0.4 | 39.9 |
| [0.1, 0.2) | 0 | 0.000 | 0.025 | 0.074 | 1.000 | 3.0 | 39.9 |
| [0.2, 0.3) | 4 | 0.100 | 0.050 | 0.191 | 1.000 | 7.6 | 39.9 |
| [0.3, 0.4) | 10 | 0.251 | 0.079 | 0.344 | 1.000 | 13.7 | 39.9 |
| [0.4, 0.5) | 15 | 0.376 | 0.097 | 0.512 | 1.000 | 20.4 | 39.9 |
| [0.5, 0.6) | 26 | 0.653 | 0.128 | 0.672 | 1.000 | 26.8 | 39.8 |
| [0.6, 0.7) | 33 | 0.829 | 0.144 | 0.808 | 1.000 | 32.2 | 39.8 |
| [0.7, 0.8) | 48 | 1.205 | 0.174 | 0.908 | 1.000 | 36.2 | 39.8 |
| [0.8, 0.9) | 31 | 0.779 | 0.140 | 0.970 | 1.000 | 38.6 | 39.8 |
| [0.9, 1.0) | 55 | 1.382 | 0.186 | 0.996 | 1.000 | 39.6 | 39.8 |
| [1.0, 1.1) | 38 | 0.955 | 0.155 | 0.997 | 1.000 | 39.7 | 39.8 |
| [1.1, 1.2) | 28 | 0.704 | 0.133 | 0.984 | 1.000 | 39.1 | 39.8 |
| [1.2, 1.3) | 35 | 0.880 | 0.149 | 0.968 | 1.000 | 38.5 | 39.8 |
| [1.3, 1.4) | 39 | 0.981 | 0.157 | 0.956 | 1.000 | 38.0 | 39.8 |
| [1.4, 1.5) | 45 | 1.132 | 0.169 | 0.953 | 1.000 | 37.9 | 39.8 |
| [1.5, 1.6) | 37 | 0.931 | 0.153 | 0.959 | 1.000 | 38.1 | 39.7 |
| [1.6, 1.7) | 32 | 0.805 | 0.142 | 0.971 | 1.000 | 38.6 | 39.7 |
| [1.7, 1.8) | 46 | 1.158 | 0.171 | 0.983 | 1.000 | 39.1 | 39.7 |
| [1.8, 1.9) | 36 | 0.907 | 0.151 | 0.994 | 1.000 | 39.5 | 39.7 |
| [1.9, 2.0) | 41 | 1.033 | 0.161 | 0.999 | 1.000 | 39.7 | 39.7 |
pairs with u in [0.0,0.5): n = 29, GUE expects 45.1 (+-6.7), Poisson expects 199.4
pairs with u in [0.0,1.0): n = 222, GUE expects 218.5 (+-14.8), Poisson expects 398.5
pairs with u in [1.0,2.0): n = 377, GUE expects 388.1 (+-19.7), Poisson expects 397.5

**Small-sample note.** Each bin expects only ~40 pairs at u ~ 1 (and 0.4-20 pairs for u < 0.5), so the per-bin
standard error is +-0.13 to +-0.19 on R_2 at u ~ 1 and the empirical values scatter from 0.70 to 1.38 around 1
(the [0.9, 1.0) bin, 55 vs 39.6, is a +2.4 sigma fluctuation; [1.1, 1.2), 28 vs 39.1, is -1.8 sigma). The informative
part is the dip: the five bins below u = 0.5 hold 29 pairs against 45.1 +- 6.7 for GUE and 199 for Poisson - a
clear repulsion hole, slightly deeper than GUE, and the same 29 spacings as the Delta = 0.5 rung of the ladder
(no non-adjacent pair is that close). Across [0, 2) the 599 pairs match GUE's 606.6 expected within 1 sigma.

## 6. Caveats

1. **Only the first 400 zeros.** The GUE limit is approached as log(gamma/2pi) -> infinity; here log(gamma/2pi) runs
   from 0.81 to 4.68. The observed narrowing (sd 0.371 vs 0.422, fewer spacings below 0.5 and above 2.0, both at
   P ~ 0.007) is consistent with the known behaviour of low zeros, which are more rigid than GUE (the number variance
   saturates and the small-u pair correlation is depleted). Nothing here distinguishes "GUE plus finite-height
   corrections" from a slightly different law; 400 spacings cannot.
2. **The asymptotic exponents are not directly observable with M = 399.** Below Delta = 0.3 there are 4 spacings, below
   0.2 none, so any exponent fit lives at Delta ~ 0.25-0.75 where the GUE log-slope is already 3.6-3.8. The comparison
   made is fit-against-fit at the same thresholds. The bootstrap resamples spacings independently, which ignores their
   (weak) correlations, so the bands are indicative only.
3. **Riemann-Siegel accuracy.** With the main sum and C0 only, |Z_RS - Z| is 2e-3 to 1e-2 for t < 35 and 7e-5 at
   t = 700; zero ordinates are off by up to 7.5e-3 (n = 3) and typically 2e-4. That is irrelevant for the statistics
   (counts and exponents unchanged, fractions shift by <= 3e-5) but the ordinates in the analysis column are the
   Euler-Maclaurin-verified ones, good to ~1e-9. The tabulated comparison values are quoted from memory of the standard
   tables (9 decimals) and agree with the Euler-Maclaurin ordinates to 3e-10, which also certifies them.
4. **Completeness of the zero list** rests on the count argument (414 found below 700 vs theta(700)/pi + 1 = 414.56;
   Gram-point bookkeeping; no near-miss on a grid of 0.02 mean spacings), not on a Turing-style proof. A missed close
   pair would show up as an implied S(T) of about -2.5, which is not seen anywhere.
5. The surmise is used where the task asked for it; the exact sine-kernel law is given alongside and differs from
   the surmise by < 0.004 in both fractions on this ladder (and by 1.5 % in the small-s coefficient of p(s)).

## 7. Figure

`cascade.svg` (hand-written SVG, 980 x 500; `cascade_preview.png` is a rough PIL rasterisation of it for checking): panel A is the cumulative reservoir fraction h_Delta / sum s versus Delta
(empirical staircase with one step per spacing, ladder thresholds as dots carrying their counts in tooltips, exact GUE
and Poisson curves) with a log-log inset of the small-threshold region showing the fitted slope 4.5 against 3.6 (GUE)
and 1.7 (Poisson) on the same points; panel B is the spacing histogram (bin 0.2) against the Wigner surmise and e^(-s).
