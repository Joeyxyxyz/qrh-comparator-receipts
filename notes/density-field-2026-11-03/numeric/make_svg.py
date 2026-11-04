#!/usr/bin/env python3
"""Draw cascade.svg by hand from summary.json (no libraries)."""
import json, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
S = json.load(open(os.path.join(HERE, "summary.json")))
PI = math.pi

# palette (dataviz reference instance, light surface): series 1 blue = zeros, 2 orange = GUE, 3 aqua = Poisson
SURF, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8984", "#e6e5e0"
C_ZERO, C_GUE, C_POI = "#2a78d6", "#eb6834", "#1baf7a"
FONT = "font-family=\"Inter, -apple-system, 'Segoe UI', Helvetica, Arial, sans-serif\""

W, H = 980, 500
out = []
def add(s): out.append(s)

def G_surmise(D):
    x = 4 * D * D / PI
    return 1 - (1 + x) * math.exp(-x)
def G_poisson(D): return 1 - (1 + D) * math.exp(-D)
def p_surmise(s): return (32 / PI ** 2) * s * s * math.exp(-4 * s * s / PI)
def p_poisson(s): return math.exp(-s)
def fmt(x): return f"{x:.2f}".rstrip("0").rstrip(".") if abs(x - round(x)) > 1e-9 else f"{int(round(x))}"

class Panel:
    def __init__(self, x0, y0, w, h, xmin, xmax, ymin, ymax, logx=False, logy=False):
        self.x0, self.y0, self.w, self.h = x0, y0, w, h
        self.xmin, self.xmax, self.ymin, self.ymax = xmin, xmax, ymin, ymax
        self.logx, self.logy = logx, logy
    def X(self, x):
        if self.logx: x, a, b = math.log10(x), math.log10(self.xmin), math.log10(self.xmax)
        else: a, b = self.xmin, self.xmax
        return self.x0 + (x - a) / (b - a) * self.w
    def Y(self, y):
        if self.logy: y, a, b = math.log10(y), math.log10(self.ymin), math.log10(self.ymax)
        else: a, b = self.ymin, self.ymax
        return self.y0 + self.h - (y - a) / (b - a) * self.h
    def poly(self, pts, color, width=2):
        pts = [(x, y) for x, y in pts if self.xmin <= x <= self.xmax and self.ymin - 1e-12 <= y <= self.ymax + 1e-12]
        d = " ".join(f"{self.X(x):.2f},{self.Y(y):.2f}" for x, y in pts)
        add(f'<polyline fill="none" stroke="{color}" stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round" points="{d}"/>')

def legend_row(x, y, entries):
    """entries: (color, label, kind) drawn left to right; returns nothing."""
    cx = x
    for col, label, kind in entries:
        if kind == "bar":
            add(f'<rect x="{cx}" y="{y-5}" width="16" height="10" fill="{col}" rx="2"/>')
        else:
            add(f'<line x1="{cx}" y1="{y}" x2="{cx+16}" y2="{y}" stroke="{col}" stroke-width="2" stroke-linecap="round"/>')
        add(f'<text x="{cx+22}" y="{y+4}" fill="{INK}" font-size="11">{label}</text>')
        cx += 22 + 6.2 * len(label) + 18   # approximate advance; labels are kept short

# ------------------------------------------------------------------ frame ---
add(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" {FONT} font-size="12">')
add('<title>MNF cascade of the first 400 Riemann zeros</title>')
add(f'<rect x="0" y="0" width="{W}" height="{H}" fill="{SURF}"/>')
add(f'<text x="24" y="28" font-size="16" font-weight="600" fill="{INK}">First 400 nontrivial zeros of zeta, read through the MNF threshold cascade</text>')
add(f'<text x="24" y="47" fill="{INK2}">Normalised spacings s_n = (gamma_n+1 - gamma_n) log(gamma_n/2pi)/2pi, n = 1..399 (M = 399, mean {S["mean"]:.3f}, sd {S["sd"]:.3f}; GUE sd 0.422).</text>')
add(f'<text x="24" y="63" fill="{INK2}">Ordinates by Riemann-Siegel (C0 term), verified by Euler-Maclaurin. Panel A uses the exact GUE law, panel B the Wigner surmise.</text>')

Y0, HP = 118, 300
# ================================================================ panel A ===
A = Panel(70, Y0, 400, HP, 0.0, 2.5, 0.0, 1.0)
add(f'<text x="{A.x0}" y="{A.y0-30}" font-size="13" font-weight="600" fill="{INK}">A. Hidden (reservoir) mass below the threshold, h_D / sum s</text>')
legend_row(A.x0, A.y0 - 12, [(C_ZERO, "zeros (staircase; dots = ladder D)", "line"), (C_GUE, "GUE exact", "line"), (C_POI, "Poisson", "line")])
for yv in (0.2, 0.4, 0.6, 0.8, 1.0):
    add(f'<line x1="{A.x0}" y1="{A.Y(yv):.1f}" x2="{A.x0+A.w}" y2="{A.Y(yv):.1f}" stroke="{GRID}" stroke-width="1"/>')
    add(f'<text x="{A.x0-8}" y="{A.Y(yv)+4:.1f}" text-anchor="end" fill="{INK2}">{fmt(yv)}</text>')
add(f'<text x="{A.x0-8}" y="{A.Y(0)+4:.1f}" text-anchor="end" fill="{INK2}">0</text>')
add(f'<line x1="{A.x0}" y1="{A.Y(0):.1f}" x2="{A.x0+A.w}" y2="{A.Y(0):.1f}" stroke="{MUTED}" stroke-width="1"/>')
for xv in (0, 0.5, 1.0, 1.5, 2.0, 2.5):
    add(f'<line x1="{A.X(xv):.1f}" y1="{A.Y(0):.1f}" x2="{A.X(xv):.1f}" y2="{A.Y(0)+5:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    add(f'<text x="{A.X(xv):.1f}" y="{A.Y(0)+18:.1f}" text-anchor="middle" fill="{INK2}">{fmt(xv)}</text>')
add(f'<text x="{A.x0+A.w/2:.1f}" y="{A.Y(0)+36:.1f}" text-anchor="middle" fill="{INK2}">threshold D (units of mean spacing)</text>')
add(f'<text transform="translate({A.x0-44},{A.y0+A.h/2:.1f}) rotate(-90)" text-anchor="middle" fill="{INK2}">hidden mass fraction h_D / sum s</text>')
# curves: Poisson, GUE, then the empirical staircase on top
A.poly([(k * 0.01, G_poisson(k * 0.01)) for k in range(0, 251)], C_POI)
A.poly([(x, y) for x, y in S["gue_exact_curve"]], C_GUE)
sp = S["sorted_spacings"]; tot = S["total"]
pts = [(0.0, 0.0)]; c = 0.0
for s in sp:
    pts.append((s, c)); c += s / tot; pts.append((s, c))
pts.append((2.5, c))
A.poly(pts, C_ZERO)
for r in S["ladder"]:
    D = r["Delta"]
    if D > 2.5: continue
    cx, cy = A.X(D), A.Y(r["res_emp"])
    add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="6" fill="{SURF}"/>')
    add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="4" fill="{C_ZERO}"><title>D = {D:g}: n_below = {r["n_below"]} of {r["M"]}, h_D = {r["h"]:.3f}, h_D/sum s = {r["res_emp"]:.4f} (GUE exact {r["res_exact"]:.4f}, Poisson {r["res_poisson"]:.4f})</title></circle>')
    if D in (1.0, 1.5):   # selective direct labels, placed upper-left where nothing is drawn
        add(f'<text x="{cx-9:.1f}" y="{cy-6:.1f}" text-anchor="end" fill="{INK2}" font-size="11">n={r["n_below"]}</text>')
add(f'<text x="{A.X(2.5)-4:.1f}" y="{A.Y(G_poisson(2.5))+16:.1f}" text-anchor="end" fill="{INK2}" font-size="11">Poisson</text>')
# annotation of the empty rungs (upper-left region is empty: the curves are below 0.45 for D < 1)
ax, ay = A.X(0.08), A.Y(0.96)
for i, line in enumerate(("reservoir empty up to D = 0.243:", "0 below 0.2 (GUE 3.4, Poisson 72)",
                          "4 below 0.3 (GUE 11.0)", "29 below 0.5 (GUE 45.1)")):
    add(f'<text x="{ax:.1f}" y="{ay + 13*i:.1f}" fill="{INK2 if i else INK}" font-size="10">{line}</text>')
# ---- inset: log-log of the small-threshold region, in the empty lower-right corner --------------
bx0, bx1 = A.X(1.60), A.X(2.5)
by1 = A.Y(0) - 2; by0 = by1 - 136
add(f'<rect x="{bx0:.1f}" y="{by0:.1f}" width="{bx1-bx0:.1f}" height="{by1-by0:.1f}" fill="{SURF}" stroke="{GRID}" rx="3"/>')
f = [x for x in S["fits"] if x["label"].startswith("fine grid 0.25")][0]
hdr = ("log-log, D = 0.25..0.75:",
       f"zeros slope {f['slope_res']:.1f} [{f['boot_res_16_84'][0]:.1f}, {f['boot_res_16_84'][1]:.1f}]",
       f"GUE {f['th_res']['exact']:.1f}, Poisson {f['th_res']['poisson']:.1f} here")
for i, line in enumerate(hdr):
    add(f'<text x="{bx0+5:.1f}" y="{by0 + 11 + 10.5*i:.1f}" fill="{INK if i == 0 else INK2}" font-size="9" {"font-weight=\"600\"" if i == 0 else ""}>{line}</text>')
I = Panel(bx0 + 28, by0 + 40, bx1 - bx0 - 34, by1 - by0 - 55, 0.25, 1.0, 1e-3, 1.0, logx=True, logy=True)
for yv in (1e-3, 1e-2, 1e-1, 1.0):
    add(f'<line x1="{I.x0}" y1="{I.Y(yv):.1f}" x2="{I.x0+I.w}" y2="{I.Y(yv):.1f}" stroke="{GRID}" stroke-width="1"/>')
    lab = {1e-3: "10^-3", 1e-2: "10^-2", 1e-1: "10^-1", 1.0: "1"}[yv]
    add(f'<text x="{I.x0-3}" y="{I.Y(yv)+3:.1f}" text-anchor="end" fill="{INK2}" font-size="8">{lab}</text>')
for xv in (0.25, 0.5, 1.0):
    add(f'<line x1="{I.X(xv):.1f}" y1="{I.Y(1e-3):.1f}" x2="{I.X(xv):.1f}" y2="{I.Y(1e-3)+3:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    add(f'<text x="{I.X(xv):.1f}" y="{I.Y(1e-3)+12:.1f}" text-anchor="middle" fill="{INK2}" font-size="8">{fmt(xv)}</text>')
I.poly([(0.25 * 1.03 ** k, G_poisson(0.25 * 1.03 ** k)) for k in range(0, 48)], C_POI, width=1.5)
I.poly([(x, y) for x, y in S["gue_exact_curve"] if 0.24 <= x <= 1.0 and y > 1e-3], C_GUE, width=1.5)
for D in [0.25 + 0.05 * k for k in range(11)] + [1.0]:
    below = [s for s in sp if s < D]
    if not below: continue
    v = sum(below) / tot
    if v < 1e-3: continue
    add(f'<circle cx="{I.X(D):.1f}" cy="{I.Y(v):.1f}" r="3.5" fill="{SURF}"/>')
    add(f'<circle cx="{I.X(D):.1f}" cy="{I.Y(v):.1f}" r="2.2" fill="{C_ZERO}"><title>D = {D:.2f}: {len(below)} spacings below, h/sum = {v:.4f}</title></circle>')

# ================================================================ panel B ===
B = Panel(560, Y0, 390, HP, 0.0, 3.2, 0.0, 1.2)
add(f'<text x="{B.x0}" y="{B.y0-30}" font-size="13" font-weight="600" fill="{INK}">B. Spacing histogram (bin 0.2) vs the surmise</text>')
legend_row(B.x0, B.y0 - 12, [(C_ZERO, "zeros, 399 spacings", "bar"), (C_GUE, "GUE surmise", "line"), (C_POI, "Poisson e^-s", "line")])
for yv in (0.2, 0.4, 0.6, 0.8, 1.0, 1.2):
    add(f'<line x1="{B.x0}" y1="{B.Y(yv):.1f}" x2="{B.x0+B.w}" y2="{B.Y(yv):.1f}" stroke="{GRID}" stroke-width="1"/>')
    add(f'<text x="{B.x0-8}" y="{B.Y(yv)+4:.1f}" text-anchor="end" fill="{INK2}">{fmt(yv)}</text>')
add(f'<text x="{B.x0-8}" y="{B.Y(0)+4:.1f}" text-anchor="end" fill="{INK2}">0</text>')
for xv in (0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0):
    add(f'<line x1="{B.X(xv):.1f}" y1="{B.Y(0):.1f}" x2="{B.X(xv):.1f}" y2="{B.Y(0)+5:.1f}" stroke="{MUTED}" stroke-width="1"/>')
    add(f'<text x="{B.X(xv):.1f}" y="{B.Y(0)+18:.1f}" text-anchor="middle" fill="{INK2}">{fmt(xv)}</text>')
add(f'<text x="{B.x0+B.w/2:.1f}" y="{B.Y(0)+36:.1f}" text-anchor="middle" fill="{INK2}">normalised spacing s</text>')
add(f'<text transform="translate({B.x0-44},{B.y0+B.h/2:.1f}) rotate(-90)" text-anchor="middle" fill="{INK2}">density  n / (M x 0.2)</text>')
bw = S["hist_bw"]
slot = B.X(bw) - B.X(0)
thick = min(24.0, slot - 2.0)
for r in S["hist"]:
    if r["n"] == 0: continue
    xl = B.X(r["a"]) + (slot - thick) / 2
    yt, yb = B.Y(r["density"]), B.Y(0)
    rr = min(4.0, (yb - yt) / 2)
    path = (f'M{xl:.1f},{yb:.1f} V{yt+rr:.1f} a{rr},{rr} 0 0 1 {rr},-{rr} H{xl+thick-rr:.1f} '
            f'a{rr},{rr} 0 0 1 {rr},{rr} V{yb:.1f} Z')
    add(f'<path d="{path}" fill="{C_ZERO}"><title>[{r["a"]:.1f}, {r["b"]:.1f}): n = {r["n"]} of {S["M"]}, density {r["density"]:.3f}; GUE surmise {r["surmise"]:.3f} (expects {r["surmise"]*S["M"]*bw:.1f}), Poisson {r["poisson"]:.3f}</title></path>')
add(f'<line x1="{B.x0}" y1="{B.Y(0):.1f}" x2="{B.x0+B.w}" y2="{B.Y(0):.1f}" stroke="{MUTED}" stroke-width="1"/>')
B.poly([(k * 0.02, p_poisson(k * 0.02)) for k in range(0, 161)], C_POI)
B.poly([(k * 0.02, p_surmise(k * 0.02)) for k in range(0, 161)], C_GUE)
for r in S["hist"]:   # direct labels on the two peak bins only
    if r["n"] >= 80:
        add(f'<text x="{B.X(r["a"])+slot/2:.1f}" y="{B.Y(r["density"])-6:.1f}" text-anchor="middle" fill="{INK2}" font-size="11">{r["n"]}</text>')
# annotation in the empty upper-right region (s > 2, density 0.5-0.8)
rx, ry = B.X(3.2), B.Y(0.80)
for i, line in enumerate(("0 of 399 spacings below 0.2", "(GUE expects 3.3, Poisson 72);", f"smallest s = {S['min_spacing']:.3f} (n = {S['min_index']}),", f"largest s = {S['max_spacing']:.3f} (n = {S['max_index']})")):
    add(f'<text x="{rx:.1f}" y="{ry + 13*i:.1f}" text-anchor="end" fill="{INK2}" font-size="10">{line}</text>')
# footer
ks = S["ks"]
add(f'<text x="24" y="{H-28}" fill="{INK2}" font-size="11">KS distance of the spacing CDF: GUE exact {ks["GUE exact"][0]:.3f} (p ~ {ks["GUE exact"][1]:.2f}), surmise {ks["GUE surmise"][0]:.3f} (p ~ {ks["GUE surmise"][1]:.2f}), Poisson {ks["Poisson"][0]:.3f} (p ~ {ks["Poisson"][1]:.0e}). Trace delta* = max s = {S["max_spacing"]:.3f}.</text>')
add(f'<text x="24" y="{H-12}" fill="{MUTED}" font-size="11">gamma_1 = {S["gamma_first"]:.4f} to gamma_400 = {S["gamma_last"]:.4f}; local-density unfolding log(gamma/2pi)/2pi. Hover the dots and bars for the counts.</text>')
add('</svg>')
path = os.path.join(HERE, "cascade.svg")
open(path, "w").write("\n".join(out) + "\n")
print("wrote", path, len("\n".join(out)), "bytes")
