# The strip cube of the first 400 Riemann zeros

Pure Python 3 (`make_cube.py`, no numpy; PIL only for the preview), 2026-11-04. Inputs: `zeros.tsv`
(column `gamma_EM`, the Euler-Maclaurin-verified ordinates, all 400 on the critical line), `spacings.tsv`
(s_n = (gamma_{n+1} - gamma_n) log(gamma_n/2pi)/2pi), `paircorr.tsv` (cross-check only). Outputs: `cube.svg`
(1000 x 620, hand-written SVG with tooltips), `cube_preview.png` (rough PIL rasterisation for a layout check).

## What the cube is

The "cube" is the measure that puts every ordered pair (rho, rho') of nontrivial zeros at the point

    (delta1, delta2, s) = (Re rho - 1/2, Re rho' - 1/2, (gamma - gamma') log(gamma_min/2pi)/2pi),

with weight m(rho) m(rho') (multiplicities), gamma_min = min(gamma, gamma'). The faces |delta| = 1/2 are the
edges of the critical strip. For the 400 known zeros every delta is 0 and every multiplicity is 1, so the empirical
measure lies on the s axis (the line delta1 = delta2 = 0) with:

* the atom at the origin = the diagonal pairs rho = rho', mass sum m(rho)^2 = 400;
* the off-diagonal atom (distinct zeros with equal ordinates, which an off-line zero would create together with its
  mirror 1 - conj(rho)) = 0;
* a hole: no pair of distinct zeros has 0 < |s| < 0.2434 (the smallest spacing, s_363); level repulsion.

Panel A of the figure sketches the cube in oblique projection with the (delta1, delta2) zones shaded on the floor
and the band extruded as a translucent column: the line delta = 0 (the 0.0e zone, carrying all the mass), the band
0 < |delta| < Delta (empty under the gap hypothesis, open), the reservoir |delta| >= Delta (O(T^(1-c)) zeros, proved),
and the 7/8 face |delta| >= 3/8; zones are by max(|delta1|, |delta2|) and Delta = 1/8 is illustrative. The ordered
pairs with |s| <= 3 are drawn as a density strip along the s axis (bins of 0.1 in s, bar half-width proportional to
the count; nothing is jittered), 2012 ordered pairs in all; the hole around the atom is the empty bins [-0.2, 0.2).

## How the slice (panel B) was computed

* Unfolding: for a pair gamma_i < gamma_j, s = (gamma_j - gamma_i) log(gamma_i/2pi)/2pi, i.e. the local density at
  the **smaller** ordinate. For adjacent zeros this is exactly the s_n of `spacings.tsv`, so the small-x part of the
  count is the spacing ladder of RESULTS.md section 3 (times 2). (Using the mean of the two densities would change s by
  a factor 1 + O(1/(gamma log gamma)), less than 0.1 % at these heights.)
* y(x) = #{ordered pairs of distinct zeros with 0 < |s| <= x} / 400. Each unordered pair i < j counts twice
  (both orders), which is why the Poisson line is 2x and the GUE curve is 2 int_0^x (1 - (sin pi u / pi u)^2) du.
* GUE integral by Simpson (2000 panels); Poisson 2x; the cubic reference (2 pi^2/9) x^3 is the small-x asymptote of
  the GUE curve (R_2(u) ~ (pi^2/3) u^2, so int_0^x R_2 ~ (pi^2/9) x^3, times 2).
* Normalisation check at large x: for x >> 1 the GUE curve is 2x - 2 int_0^x sinc^2 -> 2x - 1. At x = 2, 2.5, 3 the
  data give 3.010, 3.965, 5.030 against GUE 3.050, 4.041, 5.034 and 2x - 1 = 3, 4, 5 (Poisson 4, 5, 6). The pairs lost
  at the top of the window are about x / sum s = 0.75 % of the count at x = 3, which is inside the sqrt(n) noise.
* Log-log slopes: least squares of log10 y on log10 x at x = 0.25, 0.30, ..., 0.75 (11 points, all non-empty for the
  data), the identical fit applied to the GUE, Poisson and cubic curves at the same points.

## Integrated pair count per zero

| x | unordered pairs with s <= x | zeros: y(x) (ordered, per zero) | GUE 2 int_0^x R_2 | Poisson 2x | cubic (2 pi^2/9) x^3 |
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

(The cubic column is only meaningful where it coincides with the GUE column, x <~ 0.3; it is drawn as a reference
line of slope 3.)

**Fitted log-log slopes on x in [0.25, 0.75]** (11 points): zeros **3.71**, GUE on the same points **2.67**, Poisson
1.00, cubic 3.00 exactly. These are the same numbers as the "count fraction" exponents of RESULTS.md (fine grid
0.25..0.75: 3.71 empirical, 2.67 GUE exact), as they must be, since below x = 1 every close pair is a nearest-neighbour
pair. The local log-slope of the GUE curve is 2.98 at x = 0.1, 2.90 at 0.25, 2.63 at 0.5, 2.23 at 0.75, 1.82 at 1:
the x^3 regime is only reached as x -> 0, where the data have no pairs at all. The empirical curve is steeper than
GUE on the fit window because it starts later (nothing below 0.2434, 4 pairs below 0.3, 29 below 0.5 against GUE's
3.4, 11.0, 45.1) and catches up by x ~ 0.75-1: the same deficit of small spacings as in RESULTS.md, a ~2-2.5 sigma
effect in the direction expected for low zeros.

## Verification

* At x = 0.5: `spacings.tsv` has 29 spacings below 0.5; the all-pairs count of s <= 0.5 is also 29, of which 0 are
  non-adjacent pairs (the closest non-adjacent pair is beyond 0.5). So 29 nearest-neighbour pairs -> 58 ordered pairs
  -> 58/400 = 0.145 per zero, as expected. GUE: 0.226, Poisson: 1.
* The smallest |s| over all pairs equals the smallest spacing, 0.2434 (gamma_363, gamma_364).
* Cross-check with `paircorr.tsv` (which uses the theta(gamma)/pi unfolding and half-open bins): 29 pairs with u < 0.5
  (same), 222 with u < 1 against 224 here with s <= 1 (the two unfoldings differ by O(1/gamma) and the bin edge is
  inclusive here), 599 with u < 2 against 602 here.
* Of the 1006 unordered pairs with s <= 3, 399 are adjacent and 607 non-adjacent.

## Caveats

1. **400 zeros only.** The counts below x = 0.5 rest on 29 pairs, below 0.3 on 4; the curve is noisy there and the
   fitted slope has a bootstrap band of roughly +-0.5 (RESULTS.md).
2. **The asymptotic cubic regime is not reached.** Even for GUE the log-slope is already 2.6-2.9 on the fit window;
   the data contain no pair below 0.2434, where the x^3 law would live. "Slope 3" is the small-x prediction, not an
   observed quantity.
3. **GUE is a conjecture for zeta** (Montgomery's pair-correlation conjecture, proved only for test functions with
   Fourier support in (-1, 1)); the cubic law is what GUE predicts, not a theorem about the zeros.
4. **The cube's off-axis part is empty here by construction**: all 400 zeros are on the line and simple, and RH is
   verified numerically to heights far beyond gamma_400 = 679.7, so the band, reservoir and 7/8-face zones of panel A
   are drawn to show where mass *would* go (an off-line zero rho contributes, with its mirror 1 - conj(rho), ordered
   pairs at delta = +-(Re rho - 1/2) with s = 0, i.e. an off-diagonal atom at the origin of the s axis and points off
   the axis); Delta = 1/8 is illustrative and the zone labels (gap hypothesis open; reservoir O(T^(1-c)) proved) are
   the status of the statements, not features of the data.
5. The preview PNG is a rough rasterisation (DejaVu Sans instead of the SVG's font stack, dashed strokes drawn solid
   and lighter); the SVG is the figure.
