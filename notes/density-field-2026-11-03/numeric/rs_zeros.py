#!/usr/bin/env python3
"""
Riemann-Siegel Z(t) in pure Python and the first ~400 nontrivial zeros.

  Z(t) = e^{i theta(t)} zeta(1/2 + i t)   (real for real t)

  Riemann-Siegel:
    Z(t) = 2 sum_{n<=N} n^{-1/2} cos(theta(t) - t log n)
           + (-1)^{N-1} (t/2pi)^{-1/4} [ C0(p) + C1(p) (t/2pi)^{-1/2} + ... ]
    N = floor(sqrt(t/2pi)),  p = sqrt(t/2pi) - N,
    C0(p) = Psi(p) = cos(2pi(p^2 - p - 1/16)) / cos(2pi p).

  theta(t) by the Stirling series.

Zeros are located by sign changes of Z on a grid paced by Gram points, then
bisection.  Two independent checks are run on every zero:
  (a) the Riemann-Siegel formula with four correction terms C0..C4 (derivatives
      of Psi obtained by truncated-Taylor-series arithmetic, no finite differences);
  (b) Euler-Maclaurin summation of zeta(1/2+it) with N ~ t terms, which is
      accurate to ~1e-13 in this range and is formula-independent.

Writes zeros.tsv next to this script.
"""
import math, cmath, sys, os, time
from fractions import Fraction

PI = math.pi
TWO_PI = 2.0 * math.pi
HERE = os.path.dirname(os.path.abspath(__file__))

# ----------------------------------------------------------------------------
# theta(t)  (Stirling series; terms through t^-9, error ~1e-13 for t > 10)
# ----------------------------------------------------------------------------
def theta(t):
    x = t / TWO_PI
    th = 0.5 * t * math.log(x) - 0.5 * t - PI / 8.0
    t2 = t * t
    th += (1.0 / (48.0 * t)
           + 7.0 / (5760.0 * t * t2)
           + 31.0 / (80640.0 * t * t2 * t2)
           + 127.0 / (430080.0 * t * t2 ** 3)
           + 511.0 / (1216512.0 * t * t2 ** 4))
    return th

def theta_prime(t):
    t2 = t * t
    return (0.5 * math.log(t / TWO_PI)
            - 1.0 / (48.0 * t2)
            - 21.0 / (5760.0 * t2 * t2)
            - 155.0 / (80640.0 * t2 ** 3))

# Independent check of theta: Im log Gamma(1/4 + i t/2) - (t/2) log pi,
# via complex Stirling with upward recurrence (mod 2pi only).
BERN2 = [Fraction(1, 6), Fraction(-1, 30), Fraction(1, 42), Fraction(-1, 30),
         Fraction(5, 66), Fraction(-691, 2730), Fraction(7, 6), Fraction(-3617, 510),
         Fraction(43867, 798), Fraction(-174611, 330)]  # B2, B4, ..., B20

def lgamma_complex(z, shift=25):
    acc = 0j
    w = z
    for _ in range(shift):
        acc += cmath.log(w)
        w += 1
    val = (w - 0.5) * cmath.log(w) - w + 0.5 * math.log(TWO_PI)
    wp = w
    for k, b in enumerate(BERN2, start=1):
        val += float(b) / ((2 * k) * (2 * k - 1)) / wp
        wp *= w * w
    return val - acc

def theta_check(t):
    """theta(t) mod 2pi from log Gamma, for comparison with the Stirling series."""
    v = lgamma_complex(complex(0.25, 0.5 * t)).imag - 0.5 * t * math.log(PI)
    return v

# ----------------------------------------------------------------------------
# Psi and its derivatives.  Psi is entire (the zeros of cos(2 pi p) at p = 1/4, 3/4
# are removable), so Taylor coefficients at p are obtained from the Cauchy integral
# on a circle |z - p| = r by the trapezoidal rule, which converges geometrically for
# entire functions and never divides by a small cos(2 pi p).  (A series-division
# scheme was tried first and loses all accuracy within ~0.05 of p = 1/4, 3/4.)
# ----------------------------------------------------------------------------
def psi_complex(z):
    return cmath.cos(TWO_PI * (z * z - z - 1.0 / 16.0)) / cmath.cos(TWO_PI * z)

_CAUCHY_M = 128
_CAUCHY_R = 0.5
_CAUCHY_W = [cmath.exp(2j * PI * j / _CAUCHY_M) for j in range(_CAUCHY_M)]

def psi_derivs(p, M=12):
    """[Psi(p), Psi'(p), ..., Psi^(M)(p)] by Cauchy integrals (radius 0.5, 128 nodes)."""
    r = _CAUCHY_R
    # guard: no node may sit on a removable singularity 1/4 + k/2 of the quotient
    for _ in range(8):
        if min(abs(cmath.cos(TWO_PI * (p + r * w))) for w in _CAUCHY_W) > 1e-7:
            break
        r *= 1.03
    f = [psi_complex(p + r * w) for w in _CAUCHY_W]
    out = []
    for k in range(M + 1):
        acc = 0j
        for j in range(_CAUCHY_M):
            acc += f[j] * _CAUCHY_W[(-k * j) % _CAUCHY_M]
        out.append(math.factorial(k) * (acc / (_CAUCHY_M * r ** k)).real)
    return out

def psi(p):
    d = math.cos(TWO_PI * p)
    if abs(d) < 1e-9:  # within 1e-9 of a removable singularity: use the Cauchy value
        return psi_derivs(p, 0)[0]
    return math.cos(TWO_PI * (p * p - p - 1.0 / 16.0)) / d

def rs_C_terms(p, K):
    """C0..CK (K <= 4), Edwards/Haselgrove coefficients."""
    if K == 0:
        return [psi(p)]
    d = psi_derivs(p, 12)
    C = [d[0]]
    if K >= 1:
        C.append(-d[3] / (96.0 * PI ** 2))
    if K >= 2:
        C.append(d[2] / (64.0 * PI ** 2) + d[6] / (18432.0 * PI ** 4))
    if K >= 3:
        C.append(-d[1] / (64.0 * PI ** 2) - d[5] / (3840.0 * PI ** 4)
                 - d[9] / (5308416.0 * PI ** 6))
    if K >= 4:
        C.append(d[0] / (128.0 * PI ** 2) + 19.0 * d[4] / (24576.0 * PI ** 4)
                 + 11.0 * d[8] / (5898240.0 * PI ** 6)
                 + d[12] / (2038431744.0 * PI ** 8))
    return C

# ----------------------------------------------------------------------------
# Riemann-Siegel Z(t)
# ----------------------------------------------------------------------------
_LOGN = [0.0] + [math.log(n) for n in range(1, 64)]
_RSQ = [0.0] + [1.0 / math.sqrt(n) for n in range(1, 64)]

def Z_rs(t, K=0):
    x = t / TWO_PI
    sq = math.sqrt(x)
    N = int(sq)
    p = sq - N
    th = theta(t)
    s = 0.0
    for n in range(1, N + 1):
        s += math.cos(th - t * _LOGN[n]) * _RSQ[n]
    s *= 2.0
    C = rs_C_terms(p, K)
    corr = 0.0
    xk = 1.0
    xh = 1.0 / sq
    for c in C:
        corr += c * xk
        xk *= xh
    sign = 1.0 if (N - 1) % 2 == 0 else -1.0
    return s + sign * x ** (-0.25) * corr

# ----------------------------------------------------------------------------
# Euler-Maclaurin zeta(s) and Z(t)  (independent of Riemann-Siegel)
# ----------------------------------------------------------------------------
_BERN_OVER_FACT = [float(b) / math.factorial(2 * k) for k, b in enumerate(BERN2, start=1)]

def zeta_em(s, N=None, m=10):
    if N is None:
        N = int(abs(s.imag)) + 30
    tot = 0j
    for n in range(1, N):
        tot += cmath.exp(-s * math.log(n))
    lnN = math.log(N)
    tot += cmath.exp((1 - s) * lnN) / (s - 1) + 0.5 * cmath.exp(-s * lnN)
    prod = s  # s (s+1) ... (s+2k-2)
    for k in range(1, m + 1):
        if k > 1:
            prod *= (s + 2 * k - 3) * (s + 2 * k - 2)
        tot += _BERN_OVER_FACT[k - 1] * prod * cmath.exp((-s - 2 * k + 1) * lnN)
    return tot

def Z_em(t):
    """Returns (Re, Im) of e^{i theta} zeta(1/2 + it); Im should be ~0."""
    z = cmath.exp(1j * theta(t)) * zeta_em(complex(0.5, t))
    return z.real, z.imag

# ----------------------------------------------------------------------------
# Gram points
# ----------------------------------------------------------------------------
def gram_points(tmax):
    out = []
    n = -1
    t = 9.67
    while True:
        for _ in range(60):
            dt = (theta(t) - n * PI) / theta_prime(t)
            t -= dt
            if abs(dt) < 1e-13:
                break
        out.append((n, t))
        if t > tmax:
            break
        n += 1
        t = t + PI / theta_prime(t)
    return out

# ----------------------------------------------------------------------------
# Root finding
# ----------------------------------------------------------------------------
def bisect(f, a, b, fa, fb, tol=1e-12, maxit=80):
    for _ in range(maxit):
        m = 0.5 * (a + b)
        fm = f(m)
        if fm == 0.0:
            return m
        if (fa < 0) == (fm < 0):
            a, fa = m, fm
        else:
            b, fb = m, fm
        if b - a < tol:
            break
    return 0.5 * (a + b)

def secant_refine(f, x0, h=1e-6, maxit=30, tol=1e-13):
    """Secant iteration started from x0 (f real-valued)."""
    x1 = x0 + h
    f0, f1 = f(x0), f(x1)
    for _ in range(maxit):
        if f1 == f0:
            break
        x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
        x0, f0, x1, f1 = x1, f1, x2, f(x2)
        if abs(x1 - x0) < tol:
            break
    return x1

def scan_zeros(tmin, tmax, subdiv=48, near_miss_tol=0.08, verbose=True):
    """Sign-change scan of Z_rs (C0 only) on a Gram-paced grid, then bisection."""
    gp = gram_points(tmax + 5.0)
    grid = []
    for (n, g), (n2, g2) in zip(gp[:-1], gp[1:]):
        if g2 < tmin:
            continue
        for k in range(subdiv):
            tt = g + (g2 - g) * k / subdiv
            if tmin <= tt <= tmax:
                grid.append(tt)
    grid.sort()
    vals = [Z_rs(t) for t in grid]
    zeros = []
    for i in range(len(grid) - 1):
        a, b = grid[i], grid[i + 1]
        fa, fb = vals[i], vals[i + 1]
        if fa == 0.0:
            zeros.append(a)
        elif (fa < 0) != (fb < 0):
            zeros.append(bisect(Z_rs, a, b, fa, fb))
    # near-miss check: local minima of |Z| without sign change
    near = []
    for i in range(1, len(grid) - 1):
        if (abs(vals[i]) < abs(vals[i - 1]) and abs(vals[i]) <= abs(vals[i + 1])
                and (vals[i - 1] < 0) == (vals[i] < 0) == (vals[i + 1] < 0)
                and abs(vals[i]) < near_miss_tol):
            # refine on a 400-point sub-grid over the two neighbouring cells
            a, b = grid[i - 1], grid[i + 1]
            sub = [a + (b - a) * k / 400 for k in range(401)]
            sv = [Z_rs(t) for t in sub]
            found = []
            for j in range(400):
                if (sv[j] < 0) != (sv[j + 1] < 0):
                    found.append(bisect(Z_rs, sub[j], sub[j + 1], sv[j], sv[j + 1]))
            near.append((grid[i], vals[i], found))
            zeros.extend(found)
    zeros.sort()
    if verbose:
        print(f"grid points: {len(grid)}, spacing at end ~{grid[-1]-grid[-2]:.4f}; "
              f"sign-change zeros: {len(zeros) - sum(len(f) for _,_,f in near)}; "
              f"near-miss refinements: {len(near)} (added {sum(len(f) for _,_,f in near)})")
        for g, v, f in near:
            print(f"  near miss at t={g:.4f}, Z={v:+.4f}, zeros found in refinement: {f}")
    return zeros, gp

# ----------------------------------------------------------------------------
def main():
    t0 = time.time()
    TMIN, TMAX = 12.0, 700.0
    NZ = 400

    # --- accuracy checks of the building blocks ------------------------------
    print("== theta(t): Stirling series vs Im log Gamma (difference mod 2pi) ==")
    for t in (14.0, 30.0, 100.0, 300.0, 700.0):
        d = (theta(t) - theta_check(t)) % TWO_PI
        d = min(d, TWO_PI - d)
        print(f"  t={t:6.1f}  |theta_stirling - theta_lgamma| mod 2pi = {d:.2e}")

    print("== Z(t): Riemann-Siegel (C0 only / C0..C4) vs Euler-Maclaurin ==")
    print("   t       Z_RS(C0)        Z_RS(C0..C4)     Z_EM            Im(e^{i th} zeta)  |RS0-EM|   |RS4-EM|")
    worst0 = worst4 = 0.0
    for t in (14.0, 17.5, 21.0, 25.0, 30.0, 40.0, 60.0, 100.0, 150.0, 250.0, 400.0, 550.0, 700.0):
        z0 = Z_rs(t, 0); z4 = Z_rs(t, 4); ze, zi = Z_em(t)
        worst0 = max(worst0, abs(z0 - ze)); worst4 = max(worst4, abs(z4 - ze))
        print(f"  {t:6.1f}  {z0:+.10f}  {z4:+.10f}  {ze:+.10f}  {zi:+.1e}   {abs(z0-ze):.1e}   {abs(z4-ze):.1e}")

    # --- scan ----------------------------------------------------------------
    print(f"== scanning Z_RS(C0) for sign changes on [{TMIN}, {TMAX}] ==")
    zeros, gp = scan_zeros(TMIN, TMAX)
    print(f"  zeros found below {TMAX}: {len(zeros)};  elapsed {time.time()-t0:.1f}s")

    # Riemann-von Mangoldt count check  N(T) = theta(T)/pi + 1 + S(T)
    for T in (100.0, 200.0, 300.0, 400.0, 500.0, 600.0, 700.0):
        cnt = sum(1 for z in zeros if z < T)
        rvm = theta(T) / PI + 1.0
        print(f"  N({T:5.0f}) found = {cnt:4d}   theta(T)/pi + 1 = {rvm:9.3f}   S(T) implied = {cnt - rvm:+.3f}")
    # Gram's law bookkeeping: count of zeros below g_n should be n+1 when the law holds
    viol = 0
    for n, g in gp:
        if g > TMAX or n < 0:
            continue
        cnt = sum(1 for z in zeros if z < g)
        if cnt != n + 1:
            viol += 1
    print(f"  Gram points below {TMAX}: {sum(1 for n,g in gp if 0 <= n and g <= TMAX)}; "
          f"with count(zeros < g_n) != n+1: {viol}  (Gram-law failures, expected a few dozen)")

    zeros = zeros[:NZ]
    # --- refine each zero with the two independent evaluators -----------------
    print("== refining each zero with RS(C0..C4) and Euler-Maclaurin ==")
    rows = []
    maxd4 = maxde = 0.0
    for i, g in enumerate(zeros, start=1):
        g4 = secant_refine(lambda t: Z_rs(t, 4), g, h=1e-5)
        ge = secant_refine(lambda t: Z_em(t)[0], g, h=1e-5)
        maxd4 = max(maxd4, abs(g4 - g)); maxde = max(maxde, abs(ge - g))
        # derivative of Z at the zero (for error propagation): finite difference of EM
        dz = (Z_em(ge + 1e-4)[0] - Z_em(ge - 1e-4)[0]) / 2e-4
        rows.append((i, g, g4, ge, dz))
    print(f"  max |gamma_RS(C0) - gamma_RS(C0..C4)| = {maxd4:.2e}")
    print(f"  max |gamma_RS(C0) - gamma_EM|        = {maxde:.2e}")
    worst = sorted(rows, key=lambda r: -abs(r[3] - r[1]))[:5]
    print("  five largest C0-vs-EM discrepancies (n, gamma, diff):")
    for r in worst:
        print(f"    n={r[0]:3d}  gamma={r[1]:.6f}  diff={r[3]-r[1]:+.2e}   Z'(gamma)={r[4]:+.3f}")
    # Minimum |Z'| over the zeros (how 'flat' the worst crossing is)
    mind = min(abs(r[4]) for r in rows)
    print(f"  min |Z'(gamma)| over the {NZ} zeros = {mind:.3f}")

    # --- self-check against known values ------------------------------------
    known = [(1, 14.134725142), (2, 21.022039639), (3, 25.010857580), (4, 30.424876126),
             (5, 32.935061588), (6, 37.586178159), (7, 40.918719012), (8, 43.327073281),
             (9, 48.005150881), (10, 49.773832478), (100, 236.524229666)]
    print("== self-check against tabulated zeros (LMFDB/Odlyzko values as recalled) ==")
    print("     n   gamma_RS(C0)      gamma_EM          tabulated        RS-tab      EM-tab")
    for n, kv in known:
        r = rows[n - 1]
        print(f"  {n:4d}   {r[1]:.9f}   {r[3]:.9f}   {kv:.9f}   {r[1]-kv:+.2e}   {r[3]-kv:+.2e}")

    # --- write ---------------------------------------------------------------
    path = os.path.join(HERE, "zeros.tsv")
    with open(path, "w") as fh:
        fh.write("n\tgamma_RS_C0\tgamma_RS_C0to4\tgamma_EM\tdiff_C0_minus_EM\tZprime_EM\n")
        for i, g, g4, ge, dz in rows:
            fh.write(f"{i}\t{g:.12f}\t{g4:.12f}\t{ge:.12f}\t{g-ge:+.3e}\t{dz:+.6f}\n")
    print(f"wrote {path}  ({len(rows)} zeros, gamma_1={rows[0][1]:.6f} ... gamma_{len(rows)}={rows[-1][1]:.6f})")
    print(f"total elapsed {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
