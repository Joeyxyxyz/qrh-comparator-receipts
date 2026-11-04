#!/usr/bin/env python3
"""
Exact GUE (beta = 2) nearest-neighbour spacing law, pure Python.

E(s) = det(I - K_s), K_s the sine kernel sin(pi(x-y))/(pi(x-y)) on [0, s]
(unfolded to unit mean spacing).  Then
    p(s)        = E''(s)                       (spacing density)
    F(D)        = int_0^D p      = 1 + E'(D)   (count fraction below D)
    G(D)        = int_0^D s p ds = 1 - E(D) + D E'(D)   (reservoir fraction)
The determinant is discretised with Gauss-Legendre nodes (Bornemann 2010),
which converges geometrically for this analytic kernel.
Small-s expansion for checks:  E(s) = 1 - s + pi^2 s^4/36 - pi^4 s^6/675 + ...
"""
import math
PI = math.pi

def gauss_legendre(m):
    xs, ws = [], []
    for i in range(1, m + 1):
        x = math.cos(PI * (i - 0.25) / (m + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, x
            for k in range(2, m + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = m * (x * p1 - p0) / (x * x - 1.0)
            dx = p1 / dp
            x -= dx
            if abs(dx) < 1e-15:
                break
        xs.append(x)
        ws.append(2.0 / ((1.0 - x * x) * dp * dp))
    return xs, ws

def det(A):
    n = len(A)
    A = [row[:] for row in A]
    d = 1.0
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(A[r][i]))
        if A[piv][i] == 0.0:
            return 0.0
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            d = -d
        d *= A[i][i]
        rowi = A[i]
        for r in range(i + 1, n):
            f = A[r][i] / rowi[i]
            if f != 0.0:
                rowr = A[r]
                for c in range(i + 1, n):
                    rowr[c] -= f * rowi[c]
    return d

_GL = {}
def E2(s, m=40):
    """Gap probability E_2(0; s) for the sine process."""
    if s <= 0.0:
        return 1.0
    if m not in _GL:
        _GL[m] = gauss_legendre(m)
    xs, ws = _GL[m]
    pts = [0.5 * s * (x + 1.0) for x in xs]
    sw = [math.sqrt(0.5 * s * w) for w in ws]
    A = []
    for i in range(m):
        row = []
        for j in range(m):
            if i == j:
                row.append(1.0 - sw[i] * sw[j])
            else:
                d = PI * (pts[i] - pts[j])
                row.append(-sw[i] * sw[j] * math.sin(d) / d)
        A.append(row)
    return det(A)

def E2_prime(s, h=1e-4, m=40):
    if s < h:
        return -1.0 + (PI ** 2 / 9.0) * s ** 3
    return (E2(s + h, m) - E2(s - h, m)) / (2.0 * h)

def E2_second(s, h=1e-3, m=40):
    if s < 2 * h:
        return (PI ** 2 / 3.0) * s * s - (2.0 * PI ** 4 / 45.0) * s ** 4
    return (E2(s + h, m) - 2.0 * E2(s, m) + E2(s - h, m)) / (h * h)

def p_exact(s):
    return E2_second(s)

def count_fraction(D):
    return 1.0 + E2_prime(D)

def reservoir_fraction(D):
    return 1.0 - E2(D) + D * E2_prime(D)

if __name__ == "__main__":
    print("convergence in m at s=3:", [f"{E2(3.0, m):.12e}" for m in (20, 30, 40, 50)])
    for s in (0.1, 0.2, 0.3):
        ser = 1 - s + PI**2 * s**4 / 36 - PI**4 * s**6 / 675
        print(f"E2({s}) = {E2(s):.10f}   small-s series = {ser:.10f}   diff = {E2(s)-ser:+.2e}")
    print("E2(1) =", E2(1.0), " E2(2) =", E2(2.0), " E2(4) =", E2(4.0))
    # normalisation checks: int p = 1 + E'(inf) -> 1 ; mean = 1 - E(inf) + inf E'(inf) -> 1
    print("count_fraction(5) =", count_fraction(5.0), "  reservoir_fraction(5) =", reservoir_fraction(5.0))
    # compare with Wigner surmise
    print("   s     p_exact     p_surmise   ratio")
    for s in (0.1, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0):
        ps = (32 / PI**2) * s * s * math.exp(-4 * s * s / PI)
        pe = p_exact(s)
        print(f"  {s:4.2f}   {pe:.6f}   {ps:.6f}   {pe/ps:.4f}")
    print("small-s coefficient of p: exact pi^2/3 =", PI**2/3, " surmise 32/pi^2 =", 32/PI**2)
