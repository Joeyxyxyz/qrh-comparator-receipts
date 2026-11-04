#!/usr/bin/env python3
"""
MNF reading of the first 400 zeta zeros.

Reads zeros.tsv (column chosen by env ZCOL, default gamma_EM = the Euler-Maclaurin-
verified ordinate; gamma_RS_C0 gives the raw C0-only Riemann-Siegel ordinate).
Writes spacings.tsv, paircorr.tsv, mnf_tables.md, summary.json.

Vocabulary (MNF):  for a threshold Delta on the normalised spacings s_n,
    nullified reading   nu_Delta = sum_{s >= Delta} s
    hidden / reservoir  h_Delta  = sum_{s <  Delta} s
    trace               delta*   = sup{Delta : nu_Delta > 0} = max spacing
"""
import math, json, os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gue_exact import count_fraction as F_exact, reservoir_fraction as G_exact, p_exact
from rs_zeros import theta

PI = math.pi
TWO_PI = 2.0 * PI
COL = os.environ.get("ZCOL", "gamma_EM")
OUT = os.environ.get("OUTDIR", HERE)
os.makedirs(OUT, exist_ok=True)
LADDER = [0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0, 1.5, 2.0]

# ---------------------------------------------------------------- theory ----
def p_surmise(s):   return (32.0 / PI ** 2) * s * s * math.exp(-4.0 * s * s / PI)
def F_surmise(D):   return math.erf(2.0 * D / math.sqrt(PI)) - (4.0 * D / PI) * math.exp(-4.0 * D * D / PI)
def G_surmise(D):
    x = 4.0 * D * D / PI
    return 1.0 - (1.0 + x) * math.exp(-x)
def p_poisson(s):   return math.exp(-s)
def F_poisson(D):   return 1.0 - math.exp(-D)
def G_poisson(D):   return 1.0 - (1.0 + D) * math.exp(-D)
def R2_gue(u):
    if u == 0.0: return 0.0
    x = PI * u
    return 1.0 - (math.sin(x) / x) ** 2

def simpson(f, a, b, n=2000):
    if n % 2: n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4.0 if i % 2 else 2.0) * f(a + i * h)
    return s * h / 3.0

def lsq_slope(xs, ys):
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    a = my - b * mx
    return a, b

def ks_pvalue(D, n):
    """Asymptotic Kolmogorov distribution with the usual finite-n correction."""
    lam = (math.sqrt(n) + 0.12 + 0.11 / math.sqrt(n)) * D
    s = 0.0
    for k in range(1, 200):
        s += (-1) ** (k - 1) * math.exp(-2.0 * k * k * lam * lam)
    return max(0.0, min(1.0, 2.0 * s))

# ------------------------------------------------------------------ data ----
lines = open(os.path.join(HERE, "zeros.tsv")).read().strip().split("\n")
hdr = lines[0].split("\t")
ci = hdr.index(COL)
zs = [float(l.split("\t")[ci]) for l in lines[1:]]
N = len(zs)

sp = [(zs[i + 1] - zs[i]) * math.log(zs[i] / TWO_PI) / TWO_PI for i in range(N - 1)]
M = len(sp)
total = sum(sp)
mean = total / M
var = sum((s - mean) ** 2 for s in sp) / (M - 1)
sorted_sp = sorted(sp)
imin = min(range(M), key=lambda i: sp[i]); imax = max(range(M), key=lambda i: sp[i])

out = []
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s); out.append(s)

P(f"# MNF reading of the first {N} zeros  (ordinates: column {COL})")
P(f"zeros: gamma_1 = {zs[0]:.6f}, gamma_{N} = {zs[-1]:.6f}")
P(f"spacings: M = {M}, sum = {total:.4f}, mean = {mean:.5f}, sd = {math.sqrt(var):.4f} "
  f"(GUE surmise sd = {math.sqrt(3*PI/8 - 1):.4f}, exact GUE sd ~ 0.4221, Poisson sd = 1)")
P(f"min spacing s_{imin+1} = {sp[imin]:.4f} (between gamma_{imin+1} = {zs[imin]:.4f} and gamma_{imin+2} = {zs[imin+1]:.4f})")
P(f"max spacing (trace delta*) s_{imax+1} = {sp[imax]:.4f} (between gamma_{imax+1} = {zs[imax]:.4f} and gamma_{imax+2} = {zs[imax+1]:.4f})")
five_small = sorted(range(M), key=lambda i: sp[i])[:5]
P("five smallest spacings (n, s_n, gamma_n, gamma_n+1): " +
  "; ".join(f"n={i+1}: s={sp[i]:.4f} [{zs[i]:.3f}, {zs[i+1]:.3f}]" for i in five_small))

with open(os.path.join(OUT, "spacings.tsv"), "w") as fh:
    fh.write("n\tgamma_n\tgamma_n+1\ts_n\n")
    for i in range(M):
        fh.write(f"{i+1}\t{zs[i]:.9f}\t{zs[i+1]:.9f}\t{sp[i]:.6f}\n")

# --------------------------------------------------------- threshold ladder --
P("")
P("## Threshold ladder (reservoir / hidden mass)")
P("")
P("| Delta | n_below = #{s<Delta} | n_above = #{s>=Delta} | M | h_Delta = sum_{s<Delta} s | nu_Delta = sum_{s>=Delta} s | h_Delta/sum s (empirical) | GUE surmise | GUE exact | Poisson |")
P("|---|---|---|---|---|---|---|---|---|---|")
ladder_rows = []
for D in LADDER:
    below = [s for s in sp if s < D]
    nb = len(below); na = M - nb
    h = sum(below); nu = total - h
    gs = G_surmise(D); gs_num = simpson(lambda s: s * p_surmise(s), 0.0, D)
    assert abs(gs - gs_num) < 1e-8, (D, gs, gs_num)
    ge = G_exact(D); gp = G_poisson(D)
    fs = F_surmise(D); fs_num = simpson(p_surmise, 0.0, D)
    assert abs(fs - fs_num) < 1e-8
    fe = F_exact(D); fp = F_poisson(D)
    ladder_rows.append(dict(Delta=D, n_below=nb, n_above=na, M=M, h=h, nu=nu,
                            res_emp=h / total, res_surmise=gs, res_exact=ge, res_poisson=gp,
                            cnt_emp=nb / M, cnt_surmise=fs, cnt_exact=fe, cnt_poisson=fp,
                            exp_n_surmise=M * fs, exp_n_exact=M * fe, exp_n_poisson=M * fp))
    P(f"| {D:g} | {nb} | {na} | {M} | {h:.4f} | {nu:.4f} | {h/total:.5f} | {gs:.5f} | {ge:.5f} | {gp:.5f} |")
P("")
P("## Threshold ladder (count fraction), with the expected counts under each law")
P("")
P("| Delta | n_below | M | #{s<Delta}/M (empirical) | GUE surmise | GUE exact | Poisson | expected n_below: GUE surmise | GUE exact | Poisson |")
P("|---|---|---|---|---|---|---|---|---|---|")
for r in ladder_rows:
    P(f"| {r['Delta']:g} | {r['n_below']} | {M} | {r['cnt_emp']:.5f} | {r['cnt_surmise']:.5f} | {r['cnt_exact']:.5f} | {r['cnt_poisson']:.5f} "
      f"| {r['exp_n_surmise']:.1f} | {r['exp_n_exact']:.1f} | {r['exp_n_poisson']:.1f} |")
P("")
P(f"trace delta* = max spacing = {sp[imax]:.4f}; nu_Delta = 0 for Delta > delta*, and nu_Delta = sum s = {total:.4f} for Delta <= min s = {sp[imin]:.4f}")

# ------------------------------------------------------- KS distances --------
def ks(F):
    d = 0.0
    for i, s in enumerate(sorted_sp):
        d = max(d, (i + 1) / M - F(s), F(s) - i / M)
    return d
P("")
P("## Kolmogorov-Smirnov distance of the empirical spacing CDF (M = %d)" % M)
P("")
P("| law | D_M | approx p-value |")
P("|---|---|---|")
ksres = {}
for name, F in (("GUE surmise", F_surmise), ("GUE exact", F_exact), ("Poisson", F_poisson)):
    d = ks(F); pv = ks_pvalue(d, M); ksres[name] = (d, pv)
    P(f"| {name} | {d:.4f} | {pv:.3g} |")

# -------------------------------------------------- exponent (log-log fit) ---
P("")
P("## Small-threshold exponent of the reservoir mass h_Delta / sum s")
P("")
P("Leading behaviour: GUE  h/sum ~ (8/pi^2) Delta^4 (surmise; exact (pi^2/12) Delta^4), count ~ (32/3pi^2) Delta^3 (exact (pi^2/9) Delta^3);")
P("                   Poisson  h/sum ~ Delta^2/2, count ~ Delta.")
P("")
def fit_report(label, Ds, sample, theory=True):
    tot = sum(sample)
    xs, ys, ycnt = [], [], []
    for D in Ds:
        below = [s for s in sample if s < D]
        if not below:
            continue
        xs.append(math.log(D)); ys.append(math.log(sum(below) / tot)); ycnt.append(math.log(len(below) / len(sample)))
    if len(xs) < 2:
        return None
    _, b = lsq_slope(xs, ys)
    _, bc = lsq_slope(xs, ycnt)
    if not theory:
        return dict(label=label, Ds=Ds, used=len(xs), slope_res=b, slope_cnt=bc)
    _, bs = lsq_slope([math.log(D) for D in Ds], [math.log(G_surmise(D)) for D in Ds])
    _, be = lsq_slope([math.log(D) for D in Ds], [math.log(G_exact(D)) for D in Ds])
    _, bp = lsq_slope([math.log(D) for D in Ds], [math.log(G_poisson(D)) for D in Ds])
    _, bcs = lsq_slope([math.log(D) for D in Ds], [math.log(F_surmise(D)) for D in Ds])
    _, bce = lsq_slope([math.log(D) for D in Ds], [math.log(F_exact(D)) for D in Ds])
    _, bcp = lsq_slope([math.log(D) for D in Ds], [math.log(F_poisson(D)) for D in Ds])
    return dict(label=label, Ds=Ds, used=len(xs), slope_res=b, slope_cnt=bc,
                th_res=dict(surmise=bs, exact=be, poisson=bp), th_cnt=dict(surmise=bcs, exact=bce, poisson=bcp))

random.seed(20261103)
fits = []
for label, Ds in (("ladder points 0.2, 0.3, 0.5", [0.2, 0.3, 0.5]),
                  ("ladder points 0.2, 0.3, 0.5, 0.75", [0.2, 0.3, 0.5, 0.75]),
                  ("fine grid 0.20..0.60 step 0.05", [0.20 + 0.05 * k for k in range(9)]),
                  ("fine grid 0.25..0.75 step 0.05", [0.25 + 0.05 * k for k in range(11)])):
    f = fit_report(label, Ds, sp)
    # bootstrap over spacings (resample with replacement), on the thresholds that are
    # non-empty in the actual sample; resamples that empty one of them are skipped
    Ds_used = [D for D in Ds if any(s < D for s in sp)]
    f["Ds_used"] = Ds_used
    bs_res, bs_cnt = [], []
    skipped = 0
    for _ in range(2000):
        samp = [sp[random.randrange(M)] for _ in range(M)]
        g = fit_report(label, Ds_used, samp, theory=False)
        if g and g["used"] == len(Ds_used):
            bs_res.append(g["slope_res"]); bs_cnt.append(g["slope_cnt"])
        else:
            skipped += 1
    f["boot_skipped"] = skipped
    bs_res.sort(); bs_cnt.sort()
    def ci(v):
        return (v[int(0.16 * len(v))], v[int(0.84 * len(v))]) if v else (float('nan'),) * 2
    f["boot_res_16_84"] = ci(bs_res); f["boot_cnt_16_84"] = ci(bs_cnt)
    f["boot_res_sd"] = math.sqrt(sum((x - sum(bs_res)/len(bs_res))**2 for x in bs_res)/(len(bs_res)-1)) if len(bs_res) > 1 else float('nan')
    f["boot_cnt_sd"] = math.sqrt(sum((x - sum(bs_cnt)/len(bs_cnt))**2 for x in bs_cnt)/(len(bs_cnt)-1)) if len(bs_cnt) > 1 else float('nan')
    f["boot_n"] = len(bs_res)
    fits.append(f)
P("| thresholds used | n_below at each threshold | fitted exponent of h/sum s | bootstrap 16-84 % | same fit applied to GUE surmise / exact / Poisson | fitted exponent of count fraction | bootstrap 16-84 % | GUE surmise / exact / Poisson |")
P("|---|---|---|---|---|---|---|---|")
for f in fits:
    nbs = [sum(1 for s in sp if s < D) for D in f["Ds"]]
    P(f"| {f['label']} (fit uses the {f['used']} non-empty) | {', '.join(str(x) for x in nbs)} | {f['slope_res']:.2f} | [{f['boot_res_16_84'][0]:.2f}, {f['boot_res_16_84'][1]:.2f}] ({f['boot_n']} resamples) "
      f"| {f['th_res']['surmise']:.2f} / {f['th_res']['exact']:.2f} / {f['th_res']['poisson']:.2f} "
      f"| {f['slope_cnt']:.2f} | [{f['boot_cnt_16_84'][0]:.2f}, {f['boot_cnt_16_84'][1]:.2f}] "
      f"| {f['th_cnt']['surmise']:.2f} / {f['th_cnt']['exact']:.2f} / {f['th_cnt']['poisson']:.2f} |")
P("")
P("(The theoretical columns are the same least-squares log-log slope evaluated on the exact laws at the same thresholds: "
  "the Delta^4 / Delta^2 asymptotics are only reached as Delta -> 0, and at Delta ~ 0.5 the local GUE slope is already below 4.)")

# ------------------------------------------------------- pair correlation ---
P("")
P("## Pair correlation at small distance (unfolded coordinates x_n = theta(gamma_n)/pi + 1)")
P("")
unf = [theta(g) / PI + 1.0 for g in zs]
L = unf[-1] - unf[0]
BW = 0.1
nb = int(round(2.0 / BW))
counts = [0] * nb
for i in range(N):
    for j in range(i + 1, N):
        d = unf[j] - unf[i]
        if d >= 2.0:
            break
        counts[int(d / BW)] += 1
P(f"window length L = x_{N} - x_1 = {L:.3f}; pairs with distance < 2: {sum(counts)}; "
  f"empirical R2 = count / ((L - u_mid) * {BW}); error bar = sqrt(count) on the same scale")
P("")
P("| bin u | pair count n | empirical R2 | +- (Poisson sqrt n) | GUE 1-(sin pi u/pi u)^2 (bin average) | Poisson | expected n (GUE) | expected n (Poisson) |")
P("|---|---|---|---|---|---|---|---|")
pc_rows = []
for k in range(nb):
    a, b = k * BW, (k + 1) * BW
    um = 0.5 * (a + b)
    norm = (L - um) * BW
    r2 = counts[k] / norm
    err = math.sqrt(counts[k]) / norm if counts[k] > 0 else 1.0 / norm
    g = simpson(R2_gue, a, b, 200) / BW
    pc_rows.append(dict(a=a, b=b, n=counts[k], R2=r2, err=err, gue=g, poisson=1.0, exp_gue=g * norm, exp_poisson=norm))
    P(f"| [{a:.1f}, {b:.1f}) | {counts[k]} | {r2:.3f} | {err:.3f} | {g:.3f} | 1.000 | {g*norm:.1f} | {norm:.1f} |")
with open(os.path.join(OUT, "paircorr.tsv"), "w") as fh:
    fh.write("u_lo\tu_hi\tpairs\tR2_emp\tR2_err\tR2_GUE_binavg\tR2_Poisson\n")
    for r in pc_rows:
        fh.write(f"{r['a']:.1f}\t{r['b']:.1f}\t{r['n']}\t{r['R2']:.4f}\t{r['err']:.4f}\t{r['gue']:.4f}\t1.0\n")
# aggregate statistics on (0,1) and (1,2)
for lo, hi in ((0.0, 0.5), (0.0, 1.0), (1.0, 2.0)):
    sel = [r for r in pc_rows if r['a'] >= lo - 1e-9 and r['b'] <= hi + 1e-9]
    n = sum(r['n'] for r in sel); eg = sum(r['exp_gue'] for r in sel); ep = sum(r['exp_poisson'] for r in sel)
    P(f"pairs with u in [{lo},{hi}): n = {n}, GUE expects {eg:.1f} (+-{math.sqrt(eg):.1f}), Poisson expects {ep:.1f}")

# ------------------------------------------------------ histogram for SVG ---
HB = 0.2
hb_n = int(round(3.2 / HB))
hist = [0] * hb_n
for s in sp:
    k = int(s / HB)
    if k < hb_n:
        hist[k] += 1
hist_rows = [dict(a=k * HB, b=(k + 1) * HB, n=hist[k], density=hist[k] / (M * HB),
                  surmise=simpson(p_surmise, k * HB, (k + 1) * HB, 100) / HB,
                  exact=simpson(p_exact, k * HB, (k + 1) * HB, 40) / HB,
                  poisson=simpson(p_poisson, k * HB, (k + 1) * HB, 100) / HB) for k in range(hb_n)]
P("")
P("## Spacing histogram (bin 0.2), density = n / (M * 0.2)")
P("")
P("| bin | n | empirical density | GUE surmise (bin avg) | GUE exact | Poisson | expected n GUE / Poisson |")
P("|---|---|---|---|---|---|---|")
for r in hist_rows:
    P(f"| [{r['a']:.1f}, {r['b']:.1f}) | {r['n']} | {r['density']:.3f} | {r['surmise']:.3f} | {r['exact']:.3f} | {r['poisson']:.3f} | {r['surmise']*M*HB:.1f} / {r['poisson']*M*HB:.1f} |")
P(f"spacings >= 3.2: {sum(1 for s in sp if s >= 3.2)}")

# ------------------------------------------------------------- outputs ------
with open(os.path.join(OUT, "mnf_tables.md"), "w") as fh:
    fh.write("\n".join(out) + "\n")
summary = dict(column=COL, N=N, M=M, total=total, mean=mean, sd=math.sqrt(var),
               min_spacing=sp[imin], min_index=imin + 1, max_spacing=sp[imax], max_index=imax + 1,
               gamma_first=zs[0], gamma_last=zs[-1], ladder=ladder_rows, ks=ksres, fits=fits,
               paircorr=pc_rows, hist=hist_rows, hist_bw=HB, sorted_spacings=sorted_sp,
               gue_exact_curve=[(0.02 * k, G_exact(0.02 * k)) for k in range(0, 151)],
               gue_exact_pdf=[(0.02 * k, p_exact(0.02 * k)) for k in range(0, 161)])
with open(os.path.join(OUT, "summary.json"), "w") as fh:
    json.dump(summary, fh, indent=1)
print("wrote spacings.tsv, paircorr.tsv, mnf_tables.md, summary.json")
