"""Log-periodic amplitude of the greedy continuation of the optimal value.

Fix p < 1/2, q = 1-p, L = log(1/q).  For a magic number M consider the
*forced greedy continuation* z = z^{(M)}: z_n = w_n for n <= M and, for
n > M,

    z_n = sum_{j=0}^{n-1} omega_{n,j} x_j,   x_0 = 1,
    x_j = K_j := max_{j<=m<=M} w_m (1 <= j <= M),   x_j = z_j (j > M).

(This is what w would be if it were non-increasing from M on; Conjecture B
says this never happens, i.e. z^{(M)} is not eventually non-increasing.)

Poissonising, Z(t) := E[z_{Po(t)}] satisfies the exact functional equation

    Z(t) = (1 - e^{-pt}) Z(qt) + S(t),
    S(t) = (1 - e^{-pt}) e^{-qt} P(qt) + e^{-t} R(t),
    P(u) = sum_{j<=M} (x_j - w_j) u^j/j!,
    R(u) = sum_{n<=M} r_n u^n/n!,  r_n = w_n - sum_{j<n} omega_{n,j} x_j,

hence  Z(t) = sum_{k>=0} prod_{i<k}(1 - e^{-p q^i t}) S(q^k t),  and for
t -> oo  Z(t) = Phi(log t) + O(e^{-ct}) with the L-periodic profile
Phi(tau) = sum_{k in Z} f(q^k e^tau),  f(u) = Pi(u) S(u),
Pi(u) = prod_{j>=1} (1 - e^{-p u / q^j}).  Its Fourier coefficients are

    A_m = (1/L) * Mellin[f](2 pi i m / L) = (1/L) int_0^oo u^{s-1} f(u) du.

A_0 is the mean (the limit if Phi is constant), A_1 the amplitude of the
first harmonic; Phi is non-constant iff some A_m (m != 0) is non-zero,
and then z^{(M)} is not eventually monotone (de-Poissonisation as in
Paper 2).  The pure greedy value b corresponds to M = 0 (P = 0, R = 1).

Usage: python3 continuation_amplitude.py p M1 [M2 ...]   (M = 0: greedy)
"""
import sys, os
import mpmath as mp
from magic_numbers import run

ps = sys.argv[1]
Ms = [int(a) for a in sys.argv[2:]] or [0]
N = 700
mp.mp.dps = int(os.environ.get('DPS', 110))
MAXDEG = int(os.environ.get('MAXDEG', 5))

p = mp.mpf(ps)
q = 1 - p
L = mp.log(1 / q)
w, b, _ = run(ps, N)


def Pi(u):
    """prod_{j>=1} (1 - exp(-p u / q^j))."""
    out = mp.mpf(1)
    a = p * u / q
    while a < 400:
        out *= (1 - mp.exp(-a))
        a /= q
    return out


def data(M):
    """Polynomial coefficients of P and R for the continuation from M."""
    x = [mp.mpf(1)] + [max(w[m] for m in range(j, M + 1)) for j in range(1, M + 1)]
    c = [x[j] - w[j] for j in range(M + 1)]          # P coefficients
    r = []
    for n in range(M + 1):
        t = p ** n
        s = t * x[0] if n >= 1 else mp.mpf(0)   # empty sum at n = 0
        for j in range(1, n):
            t = t * (n - j + 1) / j * q / p
            s += t * x[j]
        r.append(w[n] - s)                           # R coefficients
    return c, r


def horner(coeffs, u):
    out = mp.mpf(0)
    for a in reversed(coeffs):
        out = out * u + a
    return out


def make_f(M):
    c, r = data(M)
    cP = [c[j] * q ** j / mp.factorial(j) for j in range(M + 1)]   # P(qu) = sum cP[j] u^j
    cR = [r[n] / mp.factorial(n) for n in range(M + 1)]

    def S(u):
        return (1 - mp.exp(-p * u)) * mp.exp(-q * u) * horner(cP, u) + mp.exp(-u) * horner(cR, u)

    return lambda u: Pi(u) * S(u)


def fourier(f, m, tmin, tmax):
    om = 2 * mp.pi * m / L
    g = lambda tau: f(mp.exp(tau)) * mp.exp(-1j * om * tau)
    pts = mp.linspace(tmin, tmax, int((tmax - tmin) * 2) + 2)
    return mp.quad(g, pts, maxdegree=MAXDEG) / L


print(f"p = {ps}, q = {mp.nstr(q,4)}, L = {mp.nstr(L,6)}, omega = 2pi/L = {mp.nstr(2*mp.pi/L,6)}")
for M in Ms:
    f = make_f(M)
    tmax = mp.log(40 * max(M, 1) + 3000 / q)
    A0 = fourier(f, 0, -12, tmax)
    A1 = fourier(f, 1, -12, tmax)
    A2 = fourier(f, 2, -12, tmax)
    if M == 0:
        seg = b[350:701]
        print(f"greedy (M=0): A0 = {mp.nstr(A0.real, 12)}  vs mean b on [350,700] = {mp.nstr(sum(seg)/len(seg), 12)}")
        print(f"   |A1| = {mp.nstr(abs(A1), 6)},  2|A1| = {mp.nstr(2*abs(A1), 6)}  vs (max-min) b on [350,700] = {mp.nstr(max(seg)-min(seg), 6)};  |A2| = {mp.nstr(abs(A2), 4)}")
    else:
        gam = w[M] - w[N]
        print(f"M = {M:4d}: A0 = {mp.nstr(A0.real, 15)}  (w_N = {mp.nstr(w[N], 15)})")
        print(f"   |A1| = {mp.nstr(abs(A1), 6)},  |A2| = {mp.nstr(abs(A2), 6)},  gamma_M = w_M - w_N = {mp.nstr(gam, 6)},  |A1|/gamma_M = {mp.nstr(abs(A1)/gam, 6)}")
