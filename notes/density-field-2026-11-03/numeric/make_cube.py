#!/usr/bin/env python3
"""Draw cube.svg (the "strip cube" of the first 400 Riemann zeros) from zeros.tsv / spacings.tsv,
write cube_preview.png (rough PIL rasterisation, same approach as svg_preview.py) and print the
numbers that go into CUBE_NUMERIC.md.  Pure Python 3; PIL only for the preview.

The cube: every ordered pair (rho, rho') of zeros is placed at
    (delta1, delta2, s) = (Re rho - 1/2, Re rho' - 1/2, (gamma - gamma') log(gamma_min/2pi)/2pi)
with weight m(rho) m(rho').  Unfolding: local density at the SMALLER ordinate gamma_min = min(gamma, gamma'),
which for adjacent zeros is exactly the s_n of spacings.tsv.
"""
import math, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PI = math.pi

def read_tsv(name):
    rows = []
    with open(os.path.join(HERE, name)) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            line = line.strip()
            if not line: continue
            rows.append(dict(zip(head, line.split("\t"))))
    return rows

zeros = [float(r["gamma_EM"]) for r in read_tsv("zeros.tsv")]
spacings = [float(r["s_n"]) for r in read_tsv("spacings.tsv")]
paircorr = read_tsv("paircorr.tsv")
NZ = len(zeros)
assert NZ == 400 and len(spacings) == 399 and zeros == sorted(zeros)

# ---------------------------------------------------------------- pairs ---
SMAX = 3.0
pairs = []            # (s, i, j) for i < j with 0 < s <= SMAX, s unfolded at the smaller ordinate gamma_i
for i in range(NZ):
    dens = math.log(zeros[i] / (2 * PI)) / (2 * PI)
    for j in range(i + 1, NZ):
        s = (zeros[j] - zeros[i]) * dens
        if s > SMAX: break
        pairs.append((s, i, j))
pairs.sort()
svals = [p[0] for p in pairs]
n_adjacent = sum(1 for s, i, j in pairs if j == i + 1)
n_nonadj_half = sum(1 for s, i, j in pairs if j > i + 1 and s <= 0.5)
diag_mass = NZ            # sum m(rho)^2, all simple
offdiag_atom = 0          # pairs of distinct zeros with equal ordinates
import bisect
def N_emp(x):
    """ordered pairs of distinct zeros with 0 < |s| <= x, per zero (factor 2: both orders)."""
    return 2 * bisect.bisect_right(svals, x) / NZ

# ---------------------------------------------------------------- theory ---
def R2(u):
    if u == 0: return 0.0
    t = math.sin(PI * u) / (PI * u)
    return 1 - t * t
def simpson(f, a, b, n=2000):
    if n % 2: n += 1
    h = (b - a) / n
    acc = f(a) + f(b)
    for k in range(1, n):
        acc += (4 if k % 2 else 2) * f(a + k * h)
    return acc * h / 3
def N_gue(x): return 2 * simpson(R2, 0.0, x)
def N_poi(x): return 2 * x
def N_cubic(x): return (2 * PI ** 2 / 9) * x ** 3

# ---------------------------------------------------------------- checks ---
n_sp_below_half = sum(1 for s in spacings if s < 0.5)
n_pairs_half = bisect.bisect_right(svals, 0.5)
print(f"zeros: {NZ}, gamma_1 = {zeros[0]:.6f}, gamma_400 = {zeros[-1]:.6f}")
print(f"unordered pairs i<j with 0 < s <= {SMAX}: {len(pairs)} (adjacent {n_adjacent}, non-adjacent {len(pairs)-n_adjacent}); ordered = {2*len(pairs)}")
print(f"check at x = 0.5: spacings.tsv has {n_sp_below_half} spacings < 0.5; all-pairs count s <= 0.5 is {n_pairs_half} "
      f"(non-adjacent among them: {n_nonadj_half}); ordered pairs {2*n_pairs_half}; per zero {N_emp(0.5):.4f}")
smallest = pairs[0][0]
print(f"smallest |s| over all pairs: {smallest:.4f} (min spacing {min(spacings):.4f}); hole radius = that")
print("normalisation check (large x: GUE -> 2x - 1, Poisson 2x):")
for x in (2.0, 2.5, 3.0):
    print(f"  x = {x}: empirical {N_emp(x):.4f}  GUE {N_gue(x):.4f}  2x-1 = {2*x-1:.4f}  Poisson {N_poi(x):.4f}")
# edge effect: pairs near the top of the window are missing for one partner; crude correction factor (1 - x/L)
L = sum(spacings)
print(f"  window length sum s = {L:.3f}; naive edge loss at x = 3 is about x/L = {3/L:.4f} of the count")

TABLE_X = [0.1, 0.2, 0.3, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]
table = []
for x in TABLE_X:
    k = bisect.bisect_right(svals, x)
    table.append((x, k, N_emp(x), N_gue(x), N_poi(x), N_cubic(x)))
print("\nx\tunordered pairs<=x\tordered per zero\tGUE\tPoisson\tcubic (2pi^2/9)x^3")
for x, k, e, g, p, c in table:
    print(f"{x}\t{k}\t{e:.4f}\t{g:.4f}\t{p:.4f}\t{c:.4f}")

# log-log slopes on x in [0.25, 0.75], grid step 0.05 (11 points), least squares of log10 y on log10 x
FIT_X = [0.25 + 0.05 * k for k in range(11)]
def fit_slope(fn):
    pts = [(math.log10(x), math.log10(fn(x))) for x in FIT_X if fn(x) > 0]
    n = len(pts); mx = sum(p[0] for p in pts) / n; my = sum(p[1] for p in pts) / n
    sxx = sum((p[0] - mx) ** 2 for p in pts); sxy = sum((p[0] - mx) * (p[1] - my) for p in pts)
    return sxy / sxx, n
slope_emp, n_emp = fit_slope(N_emp)
slope_gue, _ = fit_slope(N_gue)
slope_poi, _ = fit_slope(N_poi)
slope_cub, _ = fit_slope(N_cubic)
print(f"\nlog-log slope on x = 0.25..0.75 (11 points, {n_emp} non-empty): empirical {slope_emp:.2f}, GUE {slope_gue:.2f}, Poisson {slope_poi:.2f}, cubic {slope_cub:.2f}")
# local GUE log-slope at a few x for reference
def local_slope(fn, x, h=1e-3):
    return (math.log(fn(x * (1 + h))) - math.log(fn(x * (1 - h)))) / (math.log(1 + h) - math.log(1 - h))
print("local GUE log-slope: " + ", ".join(f"x={x}: {local_slope(N_gue, x):.2f}" for x in (0.1, 0.25, 0.5, 0.75, 1.0)))

# density strip along the s axis: ordered pairs, both signs, bins of 0.1
BIN = 0.1
nb = int(round(2 * SMAX / BIN))
strip = [0] * nb
for s in svals:
    k = int((s + SMAX) / BIN);  k = min(k, nb - 1)          # s > 0 side
    strip[k] += 1
    k2 = int((-s + SMAX) / BIN); k2 = min(max(k2, 0), nb - 1)  # mirror (ordered pair the other way round)
    strip[k2] += 1
strip_max = max(strip)
print(f"\ndensity strip: {nb} bins of {BIN}; max count per bin {strip_max}; empty bins around 0: "
      + ", ".join(f"[{-SMAX + k*BIN:.1f},{-SMAX + (k+1)*BIN:.1f})" for k in range(nb) if strip[k] == 0))

# ================================================================== SVG ===
SURF, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8984", "#e6e5e0"
C_ZERO, C_GUE, C_POI, C_CUB = "#2a78d6", "#eb6834", "#1baf7a", "#8e5bd1"
Z_LINE, Z_BAND, Z_RES, Z_FACE = "#2a78d6", "#f3e3a2", "#f6c9b4", "#d9dde6"
FONT = "font-family=\"Inter, -apple-system, 'Segoe UI', Helvetica, Arial, sans-serif\""
W, H = 1000, 620
out = []
def add(s): out.append(s)
def esc(s): return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
def fmt(x, d=2):
    t = f"{x:.{d}f}".rstrip("0").rstrip(".")
    return t if t not in ("", "-0") else "0"

add(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" {FONT} font-size="12">')
add('<title>The strip cube of the first 400 Riemann zeros</title>')
add(f'<rect x="0" y="0" width="{W}" height="{H}" fill="{SURF}"/>')
add(f'<text x="24" y="28" font-size="16" font-weight="600" fill="{INK}">The strip cube: ordered pairs of the first 400 nontrivial zeros of zeta</text>')
add(f'<text x="24" y="47" fill="{INK2}">Each ordered pair (rho, rho\') sits at (delta1, delta2, s) = (Re rho - 1/2, Re rho\' - 1/2, (gamma - gamma\') log(gamma_min/2pi)/2pi), weight m(rho) m(rho\').</text>')
add(f'<text x="24" y="63" fill="{INK2}">All 400 zeros (zeros.tsv, Euler-Maclaurin column) are simple and on the line: the measure lies on the s axis, hole of radius {smallest:.3f} round the atom (mass {diag_mass} / 0).</text>')

# ------------------------------------------------------------- panel A ---
AX = 24
add(f'<text x="{AX}" y="88" font-size="13" font-weight="600" fill="{INK}">A. The cube (delta1, delta2, s) and its support under RH</text>')
legend = [(Z_LINE, "line delta = 0 (the 0.0e zone): the s axis, carries all the mass"),
          (Z_BAND, "band 0 &lt; |delta| &lt; Delta: empty under the gap hypothesis (open)"),
          (Z_RES, "reservoir |delta| &gt;= Delta: O(T^(1-c)) zeros, proved"),
          (Z_FACE, "7/8 face |delta| &gt;= 3/8"),
          (None, "Delta = 1/8 in the drawing is illustrative; zones by max(|delta1|, |delta2|)")]
ly = 104
for col, label in legend:
    if col:
        add(f'<rect x="{AX}" y="{ly-8}" width="14" height="10" fill="{col}" stroke="{MUTED}" stroke-width="0.5" rx="1"/>')
    add(f'<text x="{AX+20}" y="{ly}" fill="{INK}" font-size="11">{label}</text>')
    ly += 15

# oblique projection
OX, OY = 250, 372              # screen position of (0, 0, 0)
A1 = 210.0                     # px per unit delta1 (rightwards)
A2X, A2Y = 120.0 * math.cos(math.radians(35)), -120.0 * math.sin(math.radians(35))   # per unit delta2 (into the page, up-right)
CS = 42.0                      # px per unit s (upwards)
def P(d1, d2, s):
    return (OX + A1 * d1 + A2X * d2, OY + A2Y * d2 - CS * s)
def pstr(pts): return " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
def square(r, s):   # floor square |delta|_inf <= r at height s
    return [P(-r, -r, s), P(r, -r, s), P(r, r, s), P(-r, r, s)]
DELTA = 1 / 8
SB = -SMAX
# floor zones (painter's order: outer first)
add(f'<polygon points="{pstr(square(0.5, SB))}" fill="{Z_FACE}" stroke="{MUTED}" stroke-width="0.6"><title>7/8 face: max(|delta1|,|delta2|) &gt;= 3/8</title></polygon>')
add(f'<polygon points="{pstr(square(3/8, SB))}" fill="{Z_RES}" stroke="{MUTED}" stroke-width="0.6"><title>reservoir: Delta &lt;= max|delta| &lt; 3/8 (O(T^(1-c)) zeros, proved); empty for the 400 zeros here</title></polygon>')
add(f'<polygon points="{pstr(square(DELTA, SB))}" fill="{Z_BAND}" stroke="{MUTED}" stroke-width="0.6"><title>band: 0 &lt; max|delta| &lt; Delta = 1/8 (illustrative); empty under the gap hypothesis (open)</title></polygon>')
# the band as a translucent column (slab) around the s axis
for (a, b) in [((-DELTA, -DELTA), (DELTA, -DELTA)), ((DELTA, -DELTA), (DELTA, DELTA)), ((DELTA, DELTA), (-DELTA, DELTA)), ((-DELTA, DELTA), (-DELTA, -DELTA))]:
    face = [P(a[0], a[1], SB), P(b[0], b[1], SB), P(b[0], b[1], SMAX), P(a[0], a[1], SMAX)]
    add(f'<polygon points="{pstr(face)}" fill="{Z_BAND}" fill-opacity="0.18" stroke="none"/>')
add(f'<polygon points="{pstr(square(DELTA, SMAX))}" fill="none" stroke="#c9a94a" stroke-width="0.6" stroke-dasharray="3,2"/>')
for (d1, d2) in [(-DELTA, -DELTA), (DELTA, -DELTA), (DELTA, DELTA), (-DELTA, DELTA)]:
    x1, y1 = P(d1, d2, SB); x2, y2 = P(d1, d2, SMAX)
    add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="#c9a94a" stroke-width="0.6" stroke-dasharray="3,2"/>')
# top-face zone outlines (faint)
add(f'<polygon points="{pstr(square(3/8, SMAX))}" fill="none" stroke="{MUTED}" stroke-width="0.5" stroke-dasharray="2,3"/>')
# cube edges: hidden vertex (-1/2, +1/2, -3)
V = {(a, b, c): P(a, b, c) for a in (-0.5, 0.5) for b in (-0.5, 0.5) for c in (SB, SMAX)}
edges = []
for a in (-0.5, 0.5):
    for b in (-0.5, 0.5):
        edges.append(((a, b, SB), (a, b, SMAX)))
for a in (-0.5, 0.5):
    for c in (SB, SMAX):
        edges.append(((a, -0.5, c), (a, 0.5, c)))
for b in (-0.5, 0.5):
    for c in (SB, SMAX):
        edges.append(((-0.5, b, c), (0.5, b, c)))
hidden_v = (-0.5, 0.5, SB)
for u, v in edges:
    (x1, y1), (x2, y2) = V[u], V[v]
    dash = ' stroke-dasharray="4,3"' if hidden_v in (u, v) else ''
    add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{INK2}" stroke-width="1"{dash}/>')
# axes labels and ticks
x1, y1 = P(-0.5, -0.5, SB); x2, y2 = P(0.5, -0.5, SB)
for d in (-0.5, -3/8, -DELTA, 0, DELTA, 3/8, 0.5):
    tx, ty = P(d, -0.5, SB)
    add(f'<line x1="{tx:.1f}" y1="{ty:.1f}" x2="{tx:.1f}" y2="{ty+4:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    lab = {-0.5: "-1/2", -3/8: "-3/8", -DELTA: "-D", 0: "0", DELTA: "D", 3/8: "3/8", 0.5: "1/2"}[d]
    add(f'<text x="{tx:.1f}" y="{ty+15:.1f}" text-anchor="middle" fill="{INK2}" font-size="10">{lab}</text>')
mx, my = P(0, -0.5, SB)
add(f'<text x="{mx:.1f}" y="{my+30:.1f}" text-anchor="middle" fill="{INK2}">delta1 = Re rho - 1/2  (-1/2 to 1/2)</text>')
# delta2 along the right-bottom edge
for d, lab in ((-0.5, ""), (0, "0"), (0.5, "1/2")):
    tx, ty = P(0.5, d, SB)
    add(f'<line x1="{tx:.1f}" y1="{ty:.1f}" x2="{tx+4:.1f}" y2="{ty:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    if lab: add(f'<text x="{tx+9:.1f}" y="{ty+9:.1f}" fill="{INK2}" font-size="10">{lab}</text>')
tx, ty = P(0.5, 0.5, SB)
add(f'<text x="{tx+10:.1f}" y="{ty-22:.1f}" fill="{INK2}">delta2 =</text>')
add(f'<text x="{tx+10:.1f}" y="{ty-8:.1f}" fill="{INK2}">Re rho\' - 1/2</text>')
add(f'<text x="{tx+10:.1f}" y="{ty+24:.1f}" fill="{INK2}" font-size="10">(-1/2 to 1/2)</text>')
# s axis ticks on the front-left vertical edge
for s in (-3, -2, -1, 0, 1, 2, 3):
    tx, ty = P(-0.5, -0.5, s)
    add(f'<line x1="{tx-4:.1f}" y1="{ty:.1f}" x2="{tx:.1f}" y2="{ty:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    add(f'<text x="{tx-7:.1f}" y="{ty+4:.1f}" text-anchor="end" fill="{INK2}" font-size="10">{s}</text>')
tx, ty = P(-0.5, -0.5, 0)
add(f'<text transform="translate({tx-30:.1f},{ty:.1f}) rotate(-90)" text-anchor="middle" fill="{INK2}">s = (gamma - gamma\') log(gamma_min/2pi)/2pi</text>')
# the s axis (support under RH) and the density strip of ordered pairs
ax0, ay0 = P(0, 0, SB); ax1, ay1 = P(0, 0, SMAX)
add(f'<line x1="{ax0:.1f}" y1="{ay0:.1f}" x2="{ax1:.1f}" y2="{ay1:.1f}" stroke="{Z_LINE}" stroke-width="1.2"/>')
HALF = 14.0
for k in range(nb):
    lo = -SMAX + k * BIN; hi = lo + BIN
    cnt = strip[k]
    if cnt == 0: continue
    hw = HALF * cnt / strip_max
    yt = OY - CS * hi; yb = OY - CS * lo
    add(f'<rect x="{OX-hw:.1f}" y="{yt:.1f}" width="{2*hw:.1f}" height="{yb-yt:.1f}" fill="{C_ZERO}" fill-opacity="0.75">'
        f'<title>s in [{lo:.1f}, {hi:.1f}): {cnt} ordered pairs of distinct zeros ({cnt/NZ:.3f} per zero)</title></rect>')
# the atom
add(f'<circle cx="{OX:.1f}" cy="{OY:.1f}" r="5" fill="{INK}"><title>the atom at the origin: diagonal mass sum m(rho)^2 = {diag_mass} (all simple), off-diagonal (distinct zeros, equal ordinates) = {offdiag_atom}</title></circle>')
add(f'<line x1="{OX+6:.1f}" y1="{OY-3:.1f}" x2="{OX+78:.1f}" y2="{OY-40:.1f}" stroke="{INK2}" stroke-width="0.8"/>')
add(f'<text x="{OX+82:.1f}" y="{OY-44:.1f}" fill="{INK}" font-size="11">the atom: diagonal mass {diag_mass},</text>')
add(f'<text x="{OX+82:.1f}" y="{OY-31:.1f}" fill="{INK}" font-size="11">off-diagonal 0</text>')
# hole annotation
hx, hy = OX, OY - CS * smallest
add(f'<line x1="{OX+6:.1f}" y1="{OY+CS*0.12:.1f}" x2="{OX+78:.1f}" y2="{OY+30:.1f}" stroke="{INK2}" stroke-width="0.8"/>')
add(f'<text x="{OX+82:.1f}" y="{OY+34:.1f}" fill="{INK}" font-size="11">hole |s| &lt; {smallest:.3f}: no pair</text>')
add(f'<text x="{OX+82:.1f}" y="{OY+47:.1f}" fill="{INK}" font-size="11">(level repulsion)</text>')
sx, sy = P(0, 0, 2.2)
add(f'<text x="{OX+28:.1f}" y="{sy-2:.1f}" fill="{C_ZERO}" font-size="11">density strip: {2*len(pairs)} ordered</text>')
add(f'<text x="{OX+28:.1f}" y="{sy+11:.1f}" fill="{C_ZERO}" font-size="11">pairs with 0 &lt; |s| &lt;= 3, bins 0.1</text>')

# ------------------------------------------------------------- panel B ---
class Panel:
    def __init__(self, x0, y0, w, h, xmin, xmax, ymin, ymax):
        self.x0, self.y0, self.w, self.h = x0, y0, w, h
        self.xmin, self.xmax, self.ymin, self.ymax = xmin, xmax, ymin, ymax
    def X(self, x): return self.x0 + (math.log10(x) - math.log10(self.xmin)) / (math.log10(self.xmax) - math.log10(self.xmin)) * self.w
    def Y(self, y): return self.y0 + self.h - (math.log10(y) - math.log10(self.ymin)) / (math.log10(self.ymax) - math.log10(self.ymin)) * self.h
    def inside(self, x, y): return self.xmin <= x <= self.xmax and self.ymin <= y <= self.ymax
    def poly(self, pts, color, width=2, dash=None, title=None):
        pts = [(x, y) for x, y in pts if self.inside(x, y)]
        d = " ".join(f"{self.X(x):.2f},{self.Y(y):.2f}" for x, y in pts)
        dd = f' stroke-dasharray="{dash}"' if dash else ''
        t = f'<title>{title}</title>' if title else ''
        add(f'<polyline fill="none" stroke="{color}" stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"{dd} points="{d}">{t}</polyline>')

B = Panel(560, 162, 400, 338, 0.05, 3.0, 1e-4, 10.0)
add(f'<text x="{B.x0}" y="88" font-size="13" font-weight="600" fill="{INK}">B. The on-line slice: integrated pair count per zero (log-log)</text>')
add(f'<text x="{B.x0}" y="104" fill="{INK2}" font-size="11">y(x) = #{{ordered pairs of distinct zeros, 0 &lt; |s| &lt;= x}} / 400,</text>')
add(f'<text x="{B.x0}" y="118" fill="{INK2}" font-size="11">s unfolded with the density at the smaller ordinate (as in spacings.tsv).</text>')
add(f'<text x="{B.x0}" y="132" fill="{INK2}" font-size="11">The small-x cubic law is the GUE prediction for zeta, not a theorem.</text>')
lx = B.x0; lyy = 148
for col, label, dash in ((C_ZERO, "zeros", None), (C_GUE, "GUE 2 int(1 - sinc^2)", None), (C_POI, "Poisson 2x", None), (C_CUB, "(2 pi^2/9) x^3", "5,3")):
    dd = f' stroke-dasharray="{dash}"' if dash else ''
    add(f'<line x1="{lx}" y1="{lyy}" x2="{lx+16}" y2="{lyy}" stroke="{col}" stroke-width="2" stroke-linecap="round"{dd}/>')
    add(f'<text x="{lx+22}" y="{lyy+4}" fill="{INK}" font-size="11">{label}</text>')
    lx += 22 + 5.4 * len(label) + 10
# grid
for e in range(-4, 2):
    y = 10.0 ** e
    add(f'<line x1="{B.x0}" y1="{B.Y(y):.1f}" x2="{B.x0+B.w}" y2="{B.Y(y):.1f}" stroke="{GRID}" stroke-width="1"/>')
    lab = {-4: "0.0001", -3: "0.001", -2: "0.01", -1: "0.1", 0: "1", 1: "10"}[e]
    add(f'<text x="{B.x0-6}" y="{B.Y(y)+4:.1f}" text-anchor="end" fill="{INK2}">{lab}</text>')
for x in (0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1, 1.5, 2, 3):
    add(f'<line x1="{B.X(x):.1f}" y1="{B.y0}" x2="{B.X(x):.1f}" y2="{B.y0+B.h}" stroke="{GRID}" stroke-width="1"/>')
    add(f'<text x="{B.X(x):.1f}" y="{B.y0+B.h+16}" text-anchor="middle" fill="{INK2}">{fmt(x)}</text>')
add(f'<line x1="{B.x0}" y1="{B.y0+B.h}" x2="{B.x0+B.w}" y2="{B.y0+B.h}" stroke="{MUTED}" stroke-width="1"/>')
add(f'<line x1="{B.x0}" y1="{B.y0}" x2="{B.x0}" y2="{B.y0+B.h}" stroke="{MUTED}" stroke-width="1"/>')
add(f'<text x="{B.x0+B.w/2:.1f}" y="{B.y0+B.h+34}" text-anchor="middle" fill="{INK2}">distance x = |gamma - gamma\'| log(gamma_min/2pi)/2pi (mean-spacing units)</text>')
add(f'<text transform="translate({B.x0-44},{B.y0+B.h/2:.1f}) rotate(-90)" text-anchor="middle" fill="{INK2}">ordered pairs with 0 &lt; |s| &lt;= x, per zero</text>')
# curves
xs = [B.xmin * (B.xmax / B.xmin) ** (k / 300) for k in range(301)]
B.poly([(x, N_poi(x)) for x in xs], C_POI, 1.8)
B.poly([(x, N_cubic(x)) for x in xs], C_CUB, 1.6, dash="5,3")
B.poly([(x, N_gue(x)) for x in xs], C_GUE, 2)
# empirical staircase: rises at each distinct s value
stair = []
k = 0; prev_y = None
for idx, s in enumerate(svals):
    y = 2 * (idx + 1) / NZ
    if idx + 1 < len(svals) and svals[idx + 1] == s: continue
    if prev_y is not None: stair.append((s, prev_y))
    stair.append((s, y)); prev_y = y
stair.append((B.xmax, prev_y))
# riser from the bottom of the frame at the first point
x_first = stair[0][0]
add(f'<line x1="{B.X(x_first):.2f}" y1="{B.y0+B.h}" x2="{B.X(x_first):.2f}" y2="{B.Y(stair[0][1]):.2f}" stroke="{C_ZERO}" stroke-width="2" stroke-linecap="round"/>')
B.poly(stair, C_ZERO, 2)
# dots with tooltips at the table thresholds
for x, kk, e, g, p, c in table:
    if e <= 0 or not B.inside(x, e):
        if e <= 0:
            add(f'<circle cx="{B.X(x):.1f}" cy="{B.y0+B.h:.1f}" r="3.5" fill="{SURF}" stroke="{C_ZERO}" stroke-width="1.5"><title>x = {x}: 0 pairs (GUE {g:.4f}, Poisson {p:.3f} per zero)</title></circle>')
        continue
    add(f'<circle cx="{B.X(x):.1f}" cy="{B.Y(e):.1f}" r="3.5" fill="{C_ZERO}"><title>x = {x}: {2*kk} ordered pairs ({kk} unordered), {e:.4f} per zero; GUE {g:.4f}, Poisson {p:.3f}, cubic {c:.4f}</title></circle>')
# slope annotation: fitted segments on [0.25, 0.75]
def fitted_line(fn, color):
    pts = [(math.log10(x), math.log10(fn(x))) for x in FIT_X if fn(x) > 0]
    n = len(pts); mx = sum(p[0] for p in pts) / n; my = sum(p[1] for p in pts) / n
    sl = sum((p[0]-mx)*(p[1]-my) for p in pts) / sum((p[0]-mx)**2 for p in pts)
    x1, x2 = 0.25, 0.75
    y1 = 10 ** (my + sl * (math.log10(x1) - mx)); y2 = 10 ** (my + sl * (math.log10(x2) - mx))
    return sl, (x1, y1), (x2, y2)
sl_e, p1, p2 = fitted_line(N_emp, C_ZERO)
sl_g, q1, q2 = fitted_line(N_gue, C_GUE)
add(f'<rect x="{B.X(0.25):.1f}" y="{B.y0}" width="{B.X(0.75)-B.X(0.25):.1f}" height="{B.h}" fill="{INK2}" fill-opacity="0.05"/>')
add(f'<text x="{(B.X(0.25)+B.X(0.75))/2:.1f}" y="{B.y0+B.h-6}" text-anchor="middle" fill="{INK2}" font-size="10">fit window [0.25, 0.75]</text>')
tx = B.X(0.055); ty = B.Y(6.5)
add(f'<text x="{tx:.1f}" y="{ty:.1f}" fill="{INK2}" font-size="10">log-log slope on x in [0.25, 0.75] (11 points):</text>')
add(f'<text x="{tx:.1f}" y="{ty+14:.1f}" fill="{C_ZERO}" font-size="11" font-weight="600">zeros {sl_e:.2f}</text>')
add(f'<text x="{tx:.1f}" y="{ty+28:.1f}" fill="{C_GUE}" font-size="11" font-weight="600">GUE, same points {sl_g:.2f}</text>')
add(f'<text x="{tx:.1f}" y="{ty+42:.1f}" fill="{C_POI}" font-size="11">Poisson {slope_poi:.2f}</text>')
add(f'<text x="{tx:.1f}" y="{ty+56:.1f}" fill="{C_CUB}" font-size="11">cubic asymptote 3 (GUE, x -&gt; 0)</text>')
add(f'<text x="{tx:.1f}" y="{ty+70:.1f}" fill="{INK2}" font-size="10">R2 ~ (pi^2/3) u^2 is Montgomery\'s</text>')
add(f'<text x="{tx:.1f}" y="{ty+82:.1f}" fill="{INK2}" font-size="10">conjecture; GUE is already flatter here.</text>')
# empty region note
add(f'<text x="{B.X(0.27):.1f}" y="{B.Y(0.0018):.1f}" fill="{C_ZERO}" font-size="10">no pair below {smallest:.3f}; first step 2/400 = 0.005</text>')
add(f'<text x="{B.X(0.27):.1f}" y="{B.Y(0.0018)+12:.1f}" fill="{C_ZERO}" font-size="10">(the hole of panel A; no non-adjacent pair below 0.5)</text>')
# large-x check label
add(f'<text x="{B.X(0.6):.1f}" y="{B.Y(0.03):.1f}" fill="{INK2}" font-size="10">x = 2, 3: zeros {N_emp(2):.2f}, {N_emp(3):.2f}</text>')
add(f'<text x="{B.X(0.6):.1f}" y="{B.Y(0.03)+12:.1f}" fill="{INK2}" font-size="10">GUE {N_gue(2):.2f}, {N_gue(3):.2f}; 2x - 1 = 3, 5</text>')

# ------------------------------------------------------------- caption ---
cap = (f"400 zeros, {2*len(pairs)} ordered pairs; x = 0.5: {n_pairs_half} nn pairs = {2*n_pairs_half} ordered = {N_emp(0.5):.3f}/zero (GUE {N_gue(0.5):.3f}, Poisson 1); "
       f"hole {smallest:.3f}; slope on [0.25, 0.75]: zeros {sl_e:.2f}, GUE {sl_g:.2f}, Poisson {slope_poi:.0f}; atom {diag_mass} / 0.")
add(f'<text x="24" y="{H-14}" fill="{INK2}" font-size="10">{esc(cap)}</text>')
add('</svg>')
svg_path = os.path.join(HERE, "cube.svg")
with open(svg_path, "w") as fh: fh.write("\n".join(out) + "\n")
print(f"\nwrote {svg_path} ({len(out)} elements)")

# =============================================================== preview ===
# Rough rasteriser, same approach as svg_preview.py (rect/line/polyline/circle/text) plus polygon,
# fill-opacity and dashed strokes drawn solid.  For a layout check only.
def preview(src, dst):
    import xml.etree.ElementTree as ET
    from PIL import Image, ImageDraw, ImageFont
    SC = 2
    root = ET.parse(src).getroot()
    vb = [float(v) for v in root.get("viewBox").split()]
    Wp, Hp = int(vb[2] * SC), int(vb[3] * SC)
    im = Image.new("RGBA", (Wp, Hp), (255, 255, 255, 255))
    dr = ImageDraw.Draw(im)
    FONTS = {}
    def font(size, bold=False):
        key = (round(size * SC), bold)
        if key not in FONTS:
            p = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"
            try: FONTS[key] = ImageFont.truetype(p, key[0])
            except Exception: FONTS[key] = ImageFont.load_default()
        return FONTS[key]
    def tag(e): return e.tag.split("}")[-1]
    def f(v, d=0.0): return float(v) if v is not None else d
    def rgba(col, op):
        if not col or col == "none": return None
        col = col.lstrip("#"); r, g, b = int(col[0:2], 16), int(col[2:4], 16), int(col[4:6], 16)
        return (r, g, b, int(round(255 * op)))
    def fill_poly(pts, fillc, op, outline=None):
        if fillc is None and outline is None: return
        if op < 1 and fillc is not None:
            layer = Image.new("RGBA", im.size, (0, 0, 0, 0))
            ImageDraw.Draw(layer).polygon(pts, fill=fillc, outline=outline)
            im.alpha_composite(layer)
        else:
            dr.polygon(pts, fill=fillc, outline=outline)
    for e in root.iter():
        t = tag(e)
        op = f(e.get("fill-opacity"), 1.0)
        if t == "rect":
            x, y, w, h = f(e.get("x")), f(e.get("y")), f(e.get("width")), f(e.get("height"))
            fillc = rgba(e.get("fill"), op); stroke = rgba(e.get("stroke"), 1.0)
            fill_poly([(x*SC, y*SC), ((x+w)*SC, y*SC), ((x+w)*SC, (y+h)*SC), (x*SC, (y+h)*SC)], fillc, op, stroke)
        elif t == "polygon":
            pts = [tuple(float(c)*SC for c in p.split(",")) for p in e.get("points").split()]
            fill_poly(pts, rgba(e.get("fill"), op), op, rgba(e.get("stroke"), 1.0))
        elif t == "line":
            dr.line([f(e.get("x1"))*SC, f(e.get("y1"))*SC, f(e.get("x2"))*SC, f(e.get("y2"))*SC],
                    fill=rgba(e.get("stroke"), 0.5 if e.get("stroke-dasharray") else 1.0), width=max(1, round(f(e.get("stroke-width"), 1)*SC)))
        elif t == "polyline":
            pts = [tuple(float(c)*SC for c in p.split(",")) for p in e.get("points").split()]
            if len(pts) > 1:
                dr.line(pts, fill=rgba(e.get("stroke"), 1.0), width=max(1, round(f(e.get("stroke-width"), 1)*SC)), joint="curve")
        elif t == "circle":
            cx, cy, r = f(e.get("cx"))*SC, f(e.get("cy"))*SC, f(e.get("r"))*SC
            dr.ellipse([cx-r, cy-r, cx+r, cy+r], fill=rgba(e.get("fill"), 1.0), outline=rgba(e.get("stroke"), 1.0))
        elif t == "text" and e.text:
            size = f(e.get("font-size"), 12); bold = e.get("font-weight") == "600"
            fnt = font(size, bold); fillc = rgba(e.get("fill", "#000000"), 1.0)
            anchor = {"middle": "ms", "end": "rs"}.get(e.get("text-anchor"), "ls")
            tr = e.get("transform")
            if tr and "rotate(-90)" in tr:
                tx, ty = [float(v) for v in re.search(r"translate\(([-\d.]+),([-\d.]+)\)", tr).groups()]
                tw = int(dr.textlength(e.text, font=fnt)) + 4; th = int(size*SC*1.4)
                tmp = Image.new("RGBA", (tw, th), (0, 0, 0, 0)); ImageDraw.Draw(tmp).text((tw/2, th*0.75), e.text, font=fnt, fill=fillc, anchor="ms")
                rot = tmp.rotate(90, expand=True)
                im.paste(rot, (int(tx*SC - rot.width*0.75), int(ty*SC - rot.height/2)), rot)
            else:
                dr.text((f(e.get("x"))*SC, f(e.get("y"))*SC), e.text, font=fnt, fill=fillc, anchor=anchor)
    im.convert("RGB").save(dst)
    print("saved", dst, im.size)

png_path = os.path.join(HERE, "cube_preview.png")
try:
    preview(svg_path, png_path)
except ImportError as ex:
    print("preview skipped (PIL not available):", ex)
