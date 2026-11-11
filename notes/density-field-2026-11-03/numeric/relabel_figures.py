#!/usr/bin/env python3
"""Make relabeled copies of the two figures: text labels only, geometry and data untouched.
Each replacement must match exactly once; the script stops otherwise."""
import sys, pathlib
W = pathlib.Path(sys.argv[1])
def rep(t, old, new, n=1):
    c = t.count(old)
    if c != n:
        sys.exit(f"anchor count {c} != {n}: {old!r}")
    return t.replace(old, new)

# ---------- Figure 1
t = (W / "figures/cascade.svg").read_text(encoding="utf-8")
R1 = [
 (">First 400 nontrivial zeros of zeta, read through the MNF threshold cascade<",
  ">Normalized spacings of the first 400 nontrivial zeros of zeta<"),
 (">Normalised spacings s_n = (gamma_n+1 - gamma_n) log(gamma_n/2pi)/2pi, n = 1..399 (M = 399, mean 0.997, sd 0.371; GUE sd 0.422).<",
  ">Normalized spacings s_n = (gamma_n+1 - gamma_n) log(gamma_n/2pi)/2pi, n = 1..399 (M = 399, mean 0.997, sd 0.371; surmise sd 0.422).<"),
 (">Ordinates by Riemann-Siegel (C0 term), verified by Euler-Maclaurin. Panel A uses the exact GUE law, panel B the Wigner surmise.<",
  ">Ordinates (uncertified) by Riemann-Siegel (C0 term), re-located by Euler-Maclaurin. Panel A: exact GUE law; panel B: Wigner surmise.<"),
 (">A. Hidden (reservoir) mass below the threshold, h_D / sum s<",
  ">A. Fraction of the total spacing length in spacings below x<"),
 (">zeros (staircase; dots = ladder D)<", ">zeros (staircase; dots = thresholds)<"),
 (">threshold D (units of mean spacing)<", ">threshold x (units of mean spacing)<"),
 (">hidden mass fraction h_D / sum s<", ">fraction of total spacing length<"),
 (">reservoir empty up to D = 0.243:<", ">no spacing below 0.243:<"),
 (">log-log, D = 0.25..0.75:<", ">log-log, x = 0.25..0.75:<"),
 (">normalised spacing s<", ">normalized spacing s<"),
 (" Poisson 0.329 (p ~ 3e-38). Trace delta* = max s = 2.201.<", " Poisson 0.329 (p ~ 3e-38).<"),
 (" local-density unfolding log(gamma/2pi)/2pi. Hover the dots and bars for the counts.<",
  " local-density unfolding log(gamma/2pi)/2pi.<"),
 ("<title>MNF cascade of the first 400 Riemann zeros</title>",
  "<title>Normalized spacings of the first 400 zeros of zeta</title>"),
]
for o, n in R1: t = rep(t, o, n)
(W / "figures/cascade-relabeled.svg").write_text(t, encoding="utf-8")

# ---------- Figure 2
t = (W / "figures/cube.svg").read_text(encoding="utf-8")
R2 = [
 (">The strip cube: ordered pairs of the first 400 nontrivial zeros of zeta<",
  ">Ordered pairs of the first 400 nontrivial zeros of zeta<"),
 (">All 400 zeros (zeros.tsv, Euler-Maclaurin column) are simple and on the line: the measure lies on the s axis, hole of radius 0.243 round the atom (mass 400 / 0).<",
  ">Uncertified computation: all 400 zeros found simple and on the line; the measure lies on the s axis, no pair with 0 &lt; |s| &lt; 0.243 (atom 400 / 0).<"),
 (">A. The cube (delta1, delta2, s) and its support under RH<",
  ">A. Schematic of the coordinates; the data lie on the s axis<"),
 (">line delta = 0 (the 0.0e zone): the s axis, carries all the mass<",
  ">line delta = 0: the s axis, carries all the mass of these zeros<"),
 (">band 0 &lt; |delta| &lt; Delta: empty under the gap hypothesis (open)<",
  ">band 0 &lt; |delta| &lt; Delta: empty iff the gap hypothesis holds (unproved)<"),
 (">reservoir |delta| &gt;= Delta: O(T^(1-c)) zeros, proved<",
  ">|delta| &gt;= Delta: O(T^(1-c)) zeros up to height T (Carlson 1920)<"),
 (">7/8 face |delta| &gt;= 3/8<", ">|delta| &gt; 3/8: no zeros (OpenAI's 7/8 theorem)<"),
 ("<title>The strip cube of the first 400 Riemann zeros</title>",
  "<title>Ordered pairs of the first 400 zeros of zeta</title>"),
]
for o, n in R2: t = rep(t, o, n)
(W / "figures/cube-relabeled.svg").write_text(t, encoding="utf-8")
print("ok")
