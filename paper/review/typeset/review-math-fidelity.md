# Review: math fidelity (paper.md against typ/*.typ, main.typ and main.pdf)

Reviewer lens: math fidelity only. No source file was edited. Pages refer to main.pdf (34 pages, built 20:29; a rebuild
from the current sources gives the same text).

## Verdict

No major problem. Every formula of paper.md has exactly one Typst counterpart, in the same order, with the same symbols,
subscripts, exponents, bounds, inequality directions and constants. All findings below are minor: they concern how a
correct formula is set (slash against stacked fraction, line breaks inside delimiters, one fraction size, one fallback glyph).

## What was checked

- All 599 formulas of paper.md (593 inline, 6 displayed) were paired one to one, in order,
  with the formulas of main.typ (abstract, 2) and typ/01, 03, 04, 05, 06, 08, 09, 10 (62, 74, 135, 170, 43, 2, 3, 108).
  Files 02 and 07 contain no formula, as in paper.md. The six displays of paper.md (2 in section 4, 4 in section 5) are
  displays in Typst.
- Each pair was read by eye and also compared mechanically after normalising both sides to the same token stream, once with
  parentheses stripped and once with literal parentheses kept: no difference in any symbol, number or literal parenthesis.
  The only systematic difference is the fraction style reported in findings 1 to 3.
- Every multi-letter name used in Typst math is an intended symbol or function (no fused letters): Delta, Pi, RR, abs, alpha,
  approx, beta, bold, ceil, cos, delta, dif, dot, ell, epsilon, eta, floor, gamma, in, infinity, inline, integral, kappa,
  lambda, log, mu, nu, op, overline, pi, plus.minus, psi, rho, sigma, slash, sum, theta, thick, thin, tilde, times, wide, zeta.
- Rendered pages read at 110 dpi and, for every display and every nested exponent or fraction, at 200 to 300 dpi:
  pp. 1-4, 10-21, 22-25, 29-31.

Items named in the task, all correct in source and on the page:

| Item | Source | Page | Result |
|---|---|---|---|
| zero-density exponent, inline | typ/01-introduction.typ:43 | 3 | T^(1-(2σ₁-1)²/(2σ₁)) (1+log T)³, correct |
| zero-density exponent, display | typ/05-density-cube.typ:21 | 17 | correct |
| κ and θ of the exponent arithmetic | typ/05-density-cube.typ:56 | 18 | correct |
| zero-density exponent, Limitations | typ/06-numerics.typ:55 | 24 | same value, but set as a stacked fraction (finding 2) |
| zero-density exponent, Appendix B | typ/10-appendix-b.typ:66 | 31 | correct |
| Euler-Maclaurin, display | typ/04-bohr-landau.typ:88 | 15 | correct (size of the last 1/2: finding 5) |
| sharp approximate formula, display | typ/04-bohr-landau.typ:100 | 15 | correct |
| one-term formula with J(σ), display | typ/05-density-cube.typ:142 | 21 | correct |
| pair sum Π_T, display | typ/05-density-cube.typ:93 | 19 | correct |
| inequality for P(T), display | typ/05-density-cube.typ:101 | 20 | correct |
| corrected bound for P(T), Errata | typ/06-numerics.typ:75 | 25 | correct (line break: finding 4) |
| Montgomery-Vaughan mean value | typ/04-bohr-landau.typ:104 | 16 | correct, constant 26 and factor (n+1) present |
| elementary mean value (DPMV row) | typ/10-appendix-b.typ:54 | 31 | correct |
| formulas in the Appendix A table | typ/09-appendix-a.typ:26,27,29 | 29 | correct |
| formulas in the Appendix B table | typ/10-appendix-b.typ:43-71 | 30-31 | correct |

Operators: Re is upright with a thin space before s everywhere (op("Re")); log and cos are upright; "off" in N_off is upright;
the indicator 1 is bold upright. No exponent swallows a following factor (checked T^(1-κ)(1+log T)³, T^(5/6)(log T)³,
e^(iF(x)) dx, N^(-σ₁)/σ₁, δ₀^(-3/2), T³N^(-2σ₁), s²e^(-4s²/π)). No parenthesis is missing.

Not findings (they follow the guide or the stated conventions): the differential d is upright (`dif`), where TeX has an italic d;
`\varepsilon` is `epsilon`, which this font shows in the curly form; `\bar\rho` is `overline(rho)`; the literal characters
Δ, ζ, ≤ inside quotations are kept literal, as in paper.md.

## Findings

### 1. minor: typ/04-bohr-landau.typ, 26 inline formulas, pp. 14-17: slashed fractions of paper.md are set as stacked fractions

paper.md writes these with an inline slash (`1/2`, `2/3`, `\delta/2`). The Typst source uses `/`, which builds a stacked
fraction, against pitfall (3) of TYPST_GUIDE.md ("when a slash should stay a slash ... use `slash`"). Sections 1, 3, 5 and both
appendices keep the slash for the same quantities, so the paper shows |β - 1/2| with a slash on pp. 2-4, 10-11, 17-20, 30-31
and with a stacked ½ on pp. 14-17. On p. 16 (section 4.4) one paragraph has "1/σ₁ ≤ a ≤ 1/(2 - 2σ₁)" with slashes next to
stacked 2/3, 3/2, 1/2 and 1/6; on p. 17 the stacked "Δ ≥ ½" of section 4.5 and the slashed "σ = 1/2 + δ" of section 5.1 are on
one page. The meaning is unchanged.

Fix: in the formulas below write ` slash ` for `/`.

- line 34: `$0 < abs(beta - 1/2) < delta$` -> `$0 < abs(beta - 1 slash 2) < delta$`; `$abs(beta - 1/2) >= Delta$` -> `$abs(beta - 1 slash 2) >= Delta$`
- line 39: `$2/3 - epsilon$` -> `$2 slash 3 - epsilon$`
- line 47: `$1/3 + epsilon$` -> `$1 slash 3 + epsilon$`
- line 69: `$sigma > 1/2$` -> `$sigma > 1 slash 2$`
- line 73: `$abs(beta - 1/2) >= delta$` -> `$abs(beta - 1 slash 2) >= delta$`
- line 74: `$sigma > 1/2$` -> `$sigma > 1 slash 2$`
- line 81: `to the right of $1/2$` -> `to the right of $1 slash 2$`
- line 82: `$abs(zeta(2 + i t)) >= 1/3$` -> `$abs(zeta(2 + i t)) >= 1 slash 3$`
- line 113: `$sigma > 1/2$` -> `$sigma > 1 slash 2$`
- line 116: `$1/2 < sigma_1 < 1$` -> `$1 slash 2 < sigma_1 < 1$`; `$sigma_1 - 1/2 < delta <= 1/2$` -> `$sigma_1 - 1 slash 2 < delta <= 1 slash 2$`
- line 117: `$beta >= 1/2 + delta$` -> `$beta >= 1 slash 2 + delta$`
- line 119: `$delta > sigma_1 - 1/2$` -> `$delta > sigma_1 - 1 slash 2$` (the first formula of the line, `$N(1/2 + delta, T) = O(T)$`, stays: paper.md has `\tfrac12`)
- line 120: `$0 < delta < 1/2$` -> `$0 < delta < 1 slash 2$`; `$sigma_1 = 1/2 + delta/2$` -> `$sigma_1 = 1 slash 2 + delta slash 2$`; `$delta >= 1/2$` -> `$delta >= 1 slash 2$`
- line 136: `$sigma_1 >= 2/3$` -> `$sigma_1 >= 2 slash 3$`
- line 137: `$a = 3/2$` -> `$a = 3 slash 2$`; `$2/3 <= sigma_1 < 1$` -> `$2 slash 3 <= sigma_1 < 1$`; `$delta > sigma_1 - 1/2$` -> `$delta > sigma_1 - 1 slash 2$`; `$delta > 1/6$` -> `$delta > 1 slash 6$`
- line 139: `$sigma_1 > 1/2$` -> `$sigma_1 > 1 slash 2$`
- line 153: `$Delta >= 1/2$` -> `$Delta >= 1 slash 2$`; `$0 < Delta < 1/2$` -> `$0 < Delta < 1 slash 2$`; `$1/2 < op("Re") s < 1/2 + Delta$` -> `$1 slash 2 < op("Re") s < 1 slash 2 + Delta$`

Leave `/` where paper.md has `\frac` or `\tfrac`: line 88 (display), line 89 (`1/6`), line 96 (`8/(pi nu)`), line 100 (display),
line 118 (`N(1/2 + delta, T)`, `N(1/2 + delta, 4)`, `1/2 log(...)`, `1/2 abs(zeta)^2`), line 119 (first formula), line 123.

Tested on a scratch copy together with findings 2 and 3: compiles, still 34 pages, no line leaves the text block.

### 2. minor: typ/06-numerics.typ line 55, p. 24: the zero-density exponent and the exponent 3/5 are set as stacked fractions

Source: `the density exponent $1 - (2 sigma_1 - 1)^2/(2 sigma_1)$` and `the displacement bound $O(T (log T)^(3/5))$`.
On the page the exponent reads 1 - (2σ₁-1)² over 2σ₁ as a small stacked fraction in the text line, and O(T(log T)^(3/5))
has a stacked 3/5 in the exponent and enlarged outer parentheses. paper.md has `1-(2\sigma_1-1)^2/(2\sigma_1)` and
`(\log T)^{3/5}`; the other occurrences of this exponent (pp. 3, 17 and 31, and κ on p. 18) and of (log T)^(3/5) (pp. 3, 19, 31) use the slash.
Same value, different notation in the one place where the paper compares its exponent with Carlson's.

Fix: `$1 - (2 sigma_1 - 1)^2 slash (2 sigma_1)$` and `$O(T (log T)^(3 slash 5))$`.

### 3. minor: typ/06-numerics.typ lines 38, 72, 75, pp. 23-25: slashed fractions set as stacked fractions

- line 38 (caption of Figure 2, p. 23, 9 pt): `#box[$beta - 1/2$]` -> `#box[$beta - 1 slash 2$]`;
  `#box[$abs(beta - 1/2) > 3/8$]` -> `#box[$abs(beta - 1 slash 2) > 3 slash 8$]`;
  `#box[$abs(beta - 1/2) >= Delta$]` -> `#box[$abs(beta - 1 slash 2) >= Delta$]`;
  `#box[$0 < abs(beta - 1/2) < Delta$]` -> `#box[$0 < abs(beta - 1 slash 2) < Delta$]`.
  The figure itself labels its axes "-1/2 to 1/2" and "3/8" with slashes.
- line 72 (p. 24): `$1/3 + epsilon$` -> `$1 slash 3 + epsilon$`
- line 75 (p. 25): `$2/3 + epsilon$` -> `$2 slash 3 + epsilon$`; `$5/9 + epsilon$` -> `$5 slash 9 + epsilon$`

paper.md has `1/2`, `3/8`, `1/3+\varepsilon`, `2/3+\varepsilon`, `5/9+\varepsilon`; section 5.3 (p. 20) prints the same constants as
1/3 + ε and 5/9 + ε with slashes.

### 4. minor: inline formulas broken across lines inside a pair of delimiters (six places)

A break after a relation between two lines is normal; these six fall inside bars or parentheses.

- typ/01-introduction.typ line 35, p. 2: `$abs(beta - 1 slash 2) >= delta$` prints "|β -" at the end of one line and "1/2| ≥ δ" on the next.
  Fix: `#box[$abs(beta - 1 slash 2) >= delta$]`.
- typ/01-introduction.typ line 44, p. 3: `$sum_(0 < gamma <= T) m(rho) thin abs(beta - 1 slash 2) <= A thin T (log T)^(3 slash 5)$` breaks inside the bars ("|β -" / "1/2| ≤ A T(log T)^(3/5)").
  Fix: wrap the formula in `#box[...]`.
- typ/03-runs-mnf.typ line 99, p. 12: `$zeta'(1 - s) = -F(s) zeta'(s)$` prints "ζ′(1 -" / "s) = -F(s)ζ′(s)".
  Fix: `#box[$zeta'(1 - s) = -F(s) zeta'(s)$]`.
- typ/04-bohr-landau.typ line 89, p. 15: `$psi_2 = (B_2({u}) - 1/6) slash 2$` breaks inside the enlarged parentheses ("(B₂({u}) -" / "⅙)/2").
  Fix: `#box[$psi_2 = (B_2({u}) - 1/6) slash 2$]`; this leaves the line before it loosely spaced, so it is the least clear gain of the six.
- typ/05-density-cube.typ line 30, p. 17: `$3 (1 - sigma) slash (2 - sigma)$` prints "3(1 -" / "σ)/(2 - σ)".
  Fix: `#box[$3 (1 - sigma) slash (2 - sigma)$]`.
- typ/06-numerics.typ line 75, p. 25: `$P(T) <= N_(!=)(T) thin (N(T) + N_0(T))$` prints "(N(T) +" / "N₀(T))".
  Fix: `#box[$P(T) <= N_(!=)(T) thin (N(T) + N_0(T))$]`.

`#box[$...$]` is already used for this purpose in typ/06-numerics.typ and typ/10-appendix-b.typ. Tested on a scratch copy with
all six boxes and the fixes of findings 1 to 3: compiles, 34 pages, no line leaves the text block. Line breaks move when findings
1 to 3 are applied, so look at pp. 2, 3, 12, 15, 17 and 25 again afterwards and box only what still breaks.

### 5. minor: typ/04-bohr-landau.typ line 88, p. 15: `\tfrac12` of the Euler-Maclaurin display is set as a full-size fraction

Source: `wide psi(u) = {u} - 1/2 . $`. paper.md has `\psi(u)=\{u\}-\tfrac12`, a text-size fraction; the page shows a display-size
1 over 2. The pair-sum display (typ/05-density-cube.typ line 93) renders `\tfrac12` with `inline(1/2)`.
Fix: `wide psi(u) = {u} - inline(1/2) . $` (tested: compiles and gives the small fraction).

### 6. minor: typ/06-numerics.typ line 86, p. 25: the two literal "≤" inside quotations come from a fallback font

Source: `"says a gap at Δ ≤ 3/8 cannot give it"` and `"insufficient for every Δ ≤ 3/8"`. The characters are literal in paper.md
and must stay literal. The text font supplies no glyph for U+2264 here, so Typst takes it from Libertinus Serif (these are
the only two glyphs of the PDF in that font): the sign is visibly smaller and lighter than the Δ and the 3/8 around it.
Fix that keeps the character: `Δ #text(font: "New Computer Modern Math")[≤] 3/8` in both quotations (tested: same character in
the PDF text, glyph as in the formulas). The literal Δ and ζ of the other quotations (typ/03 lines 75 and 99, typ/04 line 138)
come from the text font and need nothing.
