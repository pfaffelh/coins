"""Psi_p(m): the model amplitude as a function of the marginality m.

Leading-order model of one cycle after a birth at M with previous magic
number Mprev (see phase1_model_amplitude.py), with the older-record term
taken as the explicit binomial tail

   s_n = m q^{M+1} W  P(Bin(n,q) <= Mprev) / P(Bin(M+1,q) <= Mprev).

Free parameters: (p, W, M, Mprev, m).  The birth condition forces
m in [rho/q, 1) with rho = s_{M+2}/s_{M+1}.  We tabulate the complex
number A_1/q^M over a grid of m to see whether it can vanish.

Usage: python3 psi_of_m.py p M Mprev
"""
import sys, os
import mpmath as mp
from magic_numbers import run

ps = sys.argv[1]; M = int(sys.argv[2]); Mprev = int(sys.argv[3])
mp.mp.dps = int(os.environ.get('DPS', 90))
MAXDEG = int(os.environ.get('MAXDEG', 5))
p = mp.mpf(ps); q = 1 - p; L = mp.log(1 / q)
w, b, _ = run(ps, 700)
W = w[700]


def binom_cdf(n, K):
    t = p ** n; s = t
    for j in range(1, K + 1):
        t = t * (n - j + 1) / j * q / p; s += t
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


nmax = int(3 * M / q); J = int(2 * M / q)
tailM = [binom_cdf(n, M) for n in range(nmax + 1)]
tailP = [binom_cdf(n, Mprev) for n in range(nmax + 1)]
rho = tailP[M + 2] / tailP[M + 1]
print(f"p={ps}, M={M}, Mprev={Mprev}: rho = s_(M+2)/s_(M+1) = {mp.nstr(rho,5)}, admissible m in [rho/q, 1) = [{mp.nstr(rho/q,4)}, 1)")


def amplitude_of_m(m):
    gam = {M + 1: mp.mpf(0)}
    for n in range(M + 1, nmax):
        sn = m * q ** (M + 1) * W * tailP[n] / tailP[M + 1]
        gam[n + 1] = (1 - tailM[n]) * gam[n] + q ** n * W - sn - p ** n * (1 - W)
    ginf = gam[nmax]
    g = {j: gam[j + 1] - ginf for j in range(M + 1, nmax)}
    cP = [mp.mpf(0)] * (J + 1); cR = [mp.mpf(0)] * (J + 1)
    for j in range(M + 1, J + 1):
        cP[j] = g[j] * q ** j / mp.factorial(j)
        if j >= M + 2:
            cR[j] = -g[j - 1] * (1 - tailM[j] - q ** j) / mp.factorial(j)
    T = lambda u: (1 - mp.exp(-p * u)) * mp.exp(-q * u) * horner(cP, u) + mp.exp(-u) * horner(cR, u)
    om = 2 * mp.pi / L
    f = lambda tau: Pi(mp.exp(tau)) * T(mp.exp(tau)) * mp.exp(-1j * om * tau)
    tmin = mp.log(M) - 3; tmax = mp.log(40 * J + 3000 / q)
    pts = mp.linspace(tmin, tmax, int((tmax - tmin) * 2) + 2)
    return -mp.quad(f, pts, maxdegree=MAXDEG) / L / q ** M


print("   m      |Psi|        arg(Psi)/pi     Re Psi        Im Psi")
for m in [mp.mpf(x) for x in ['0.80', '0.85', '0.90', '0.93', '0.95', '0.97', '0.99', '1.00']]:
    A = amplitude_of_m(m)
    print(f"  {mp.nstr(m,3):>4}   {mp.nstr(abs(A),5):>10}   {mp.nstr(mp.arg(A)/mp.pi,5):>10}   {mp.nstr(A.real,5):>10}   {mp.nstr(A.imag,5):>10}")
