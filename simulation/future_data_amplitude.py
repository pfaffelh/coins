"""Future-data formula for the amplitude A_1(M).

The true sequence w also has a product-formula representation with the
*infinite* data  x_j^inf = sup_{m>=j} w_m  and  r_n^inf = w_n - sum_{j<n}
omega_{n,j} x_j^inf  (both from the Bellman equation).  Since w converges,
its profile is constant and all A_m(inf) = 0 (m != 0).  The data of the
continuation from a magic number M coincide with the infinite data for
indices <= M, so by linearity

   A_1(M) = A_1(M) - A_1(inf) = -(1/L) Mellin[ Pi * T_M ](2 pi i / L),

   T_M(u) = (1-e^{-pu}) e^{-qu} sum_{j>M} g_j (qu)^j/j!  +  e^{-u} sum_{n>M} r_n u^n/n!,
   g_j := x_j^inf - w_j >= 0 (gap to the next record),  r_n := r_n^inf <= 0.

This script evaluates the future-data formula with the data restricted
to a window (M, J] and compares with A_1(M) from continuation_amplitude.py.
If a short window (up to the next record, or up to M/q) reproduces A_1(M),
the amplitude is generated locally, right after the birth.

Usage: python3 future_data_amplitude.py p M [J ...]
"""
import sys, os
import mpmath as mp
from magic_numbers import run

ps = sys.argv[1]
M = int(sys.argv[2])
Js = [int(a) for a in sys.argv[3:]]
N = 700
mp.mp.dps = int(os.environ.get('DPS', 110))
MAXDEG = int(os.environ.get('MAXDEG', 5))

p = mp.mpf(ps); q = 1 - p; L = mp.log(1 / q)
w, b, _ = run(ps, N)

# infinite data (sup over m >= j, using N = 700 as horizon)
xinf = [mp.mpf(1)] + [None] * N
cur = None
for j in range(N, 0, -1):
    cur = w[j] if cur is None else max(cur, w[j])
    xinf[j] = cur
g = [xinf[j] - w[j] for j in range(N + 1)]


def r_inf(n):
    """r_n = sum_{j<n} omega_{n,j} (K_j^{(n)} - x_j^inf)."""
    K = [None] * n; cur = None
    for j in range(n - 1, 0, -1):
        cur = w[j] if cur is None else max(cur, w[j]); K[j] = cur
    t = p ** n; s = mp.mpf(0)
    for j in range(1, n):
        t = t * (n - j + 1) / j * q / p
        s += t * (K[j] - xinf[j])
    return s


def Pi(u):
    out = mp.mpf(1); a = p * u / q
    while a < 400:
        out *= (1 - mp.exp(-a)); a /= q
    return out


def horner(c, u):
    out = mp.mpf(0)
    for a in reversed(c):
        out = out * u + a
    return out


def amplitude(J, m=1):
    cP = [mp.mpf(0)] * (J + 1); cR = [mp.mpf(0)] * (J + 1)
    for j in range(M + 1, J + 1):
        cP[j] = g[j] * q ** j / mp.factorial(j)
        cR[j] = r_inf(j) / mp.factorial(j)
    T = lambda u: (1 - mp.exp(-p * u)) * mp.exp(-q * u) * horner(cP, u) + mp.exp(-u) * horner(cR, u)
    om = 2 * mp.pi * m / L
    f = lambda tau: Pi(mp.exp(tau)) * T(mp.exp(tau)) * mp.exp(-1j * om * tau)
    tmin = mp.log(M) - 3; tmax = mp.log(40 * J + 3000 / q)
    pts = mp.linspace(tmin, tmax, int((tmax - tmin) * 2) + 2)
    return -mp.quad(f, pts, maxdegree=MAXDEG) / L


print(f"p = {ps}, M = {M}: future-data amplitude with window (M, J]")
for J in Js:
    A1 = amplitude(J)
    print(f"  J = {J:4d}: |A1^fut| = {mp.nstr(abs(A1), 6)},  |A1^fut|/q^M = {mp.nstr(abs(A1)/q**M, 6)}")
