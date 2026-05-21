"""Numerical validation of the renormalisation route of
``Manuscript/infMaxMin.tex``, Section 8.

Section 8 predicts: for a bounded solution (x_n) of the strategy-ALL
recursion -- here x = b, strategy ALL itself -- the local fundamental
coefficient

    A(t) = (1/L) \\int y(s) e^{-i w s} chi((s - t)/L) ds,   y(log n) = b_n,

with L = log(1/q), q = 1 - p, w = 2 pi / L, converges along the
geometric subsequence t_k = t_0 + k L to a limit A_infty, and
A_infty != 0 iff b_n oscillates (Theorem 8.5).

This script checks the three predictions:
  (I)   A(t_0 + k L) converges as k grows;
  (II)  the limit A_infty is non-zero -- the base case of Section 8;
  (III) the propagation factor of Proposition 8.4,
            kappa(n) = E[(J_n/(qn))^{i w}],   J_n ~ Bin(n, q),
        satisfies |kappa - 1| = O(1/n); precisely
            n |kappa(n) - 1|  ->  p w^2 / (2 q).
  kappa is computed *directly* from the binomial law, independently of
  A, so (III) is a genuine test of the propagation estimate.

The window chi has chi-hat(2 pi) = 0 exactly, so it annihilates the
large mean level gamma_0 and isolates the fundamental oscillation.
A is computed in mpmath: the amplitude is 10^-7 .. 10^-11 here, far
below what double precision survives after cancellation.

Reuses b_sequence() from b_asymptotics.py.

Run from the repository root:
    .venv/bin/python simulation/renorm_validation.py
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import ceil, floor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from b_asymptotics import b_sequence  # noqa: E402

import matplotlib  # noqa: E402
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from mpmath import mp, mpf, mpc, exp, log, pi  # noqa: E402

DPS = 50
mp.dps = DPS

HALF_WIDTH = mpf(3) / 2   # window half-width, in periods
N_LO = 8                  # window never reaches below this index
N_TARGET = 1900           # tunes n_max; more periods for smaller p


def bump(x):
    """C-infinity bump exp(-1/(1-x^2)) on (-1, 1), zero outside."""
    if x <= -1 or x >= 1:
        return mpf(0)
    return exp(-1 / (1 - x * x))


def chi(u):
    """Window with chi-hat(2 pi) = 0 exactly: phi(u) + phi(u - 1/2),
    phi(u) = bump(u / HALF_WIDTH).  The half-period shift gives the
    factor (1 + e^{-i pi}) = 0 at the fundamental frequency, so the
    constant (mean) component is killed."""
    return bump(u / HALF_WIDTH) + bump((u - mpf(1) / 2) / HALF_WIDTH)


def local_coefficient(b, log_m, inv_m, t, L, omega, n_max):
    """Normalised local fundamental coefficient A(t)."""
    m_lo = max(1, floor(float(exp(t - HALF_WIDTH * L))))
    m_hi = min(n_max, ceil(float(exp(t + (HALF_WIDTH + mpf(1) / 2) * L))))
    num, den = mpc(0), mpf(0)
    for m in range(m_lo, m_hi + 1):
        w = chi((log_m[m] - t) / L)
        if w == 0:
            continue
        wm = w * inv_m[m]
        num += b[m] * exp(mpc(0, -omega * log_m[m])) * wm
        den += wm
    return num / den


def aitken(a0, a1, a2):
    """Aitken Delta^2 extrapolation of a (complex) geometric sequence."""
    denom = a2 - 2 * a1 + a0
    if denom == 0:
        return a2
    return a0 - (a1 - a0) ** 2 / denom


def kappa_direct(n, p, q, omega):
    """Propagation factor of Prop. 8.4, computed directly from the
    binomial law: kappa(n) = E[(J_n/(qn))^{i omega}], J_n ~ Bin(n, q).
    The j = 0 term (weight p^n) is omitted -- negligible."""
    qn = q * n
    qp = q / p
    weight = p ** n            # C(n,0) q^0 p^n
    s = mpc(0)
    for j in range(1, n + 1):
        weight = weight * (n - j + 1) / j * qp
        s += weight * exp(mpc(0, omega * log(mpf(j) / qn)))
    return s


def validate(p_frac: Fraction):
    p = mpf(p_frac.numerator) / mpf(p_frac.denominator)
    q = mpf(1) - p
    L = log(1 / q)
    omega = 2 * pi / L
    periods = int(floor(float(log(mpf(N_TARGET) / N_LO) / L)))
    n_max = int(ceil(N_LO * float(1 / q) ** periods * 1.05))

    print(f"\n{'='*74}\n p = {p_frac} = {float(p):.4f}   q = {float(q):.4f}"
          f"   L = {float(L):.5f}   ({periods} periods, n_max = {n_max})\n"
          f"{'='*74}")
    b = b_sequence(n_max, p)
    log_m = [mpf(0)] + [log(m) for m in range(1, n_max + 1)]
    inv_m = [mpf(0)] + [mpf(1) / m for m in range(1, n_max + 1)]

    # ---- (I)/(II): convergence of A(t_0 + k L) -------------------------
    t_min = log(mpf(N_LO)) + HALF_WIDTH * L
    t_max = log(mpf(n_max)) - (HALF_WIDTH + mpf(1) / 2) * L
    K = int(floor(float((t_max - t_min) / L)))
    ts = [t_min + k * L for k in range(K + 1)]
    A = [local_coefficient(b, log_m, inv_m, t, L, omega, n_max) for t in ts]

    print(f"\n (I)/(II)  A(t_0 + k L)  along  n_k = e^(t_0 + k L):\n")
    print(f"   {'k':>2} {'n_k':>8}   {'|A_k|':>13} {'|A_k-A_(k-1)|':>15}")
    for k, a in enumerate(A):
        diff = "" if k == 0 else f"{float(abs(a - A[k-1])):>15.3e}"
        print(f"   {k:>2} {float(exp(ts[k])):>8.1f}   "
              f"{float(abs(a)):>13.5e} {diff:>15}")
    A_inf = aitken(A[-3], A[-2], A[-1]) if len(A) >= 3 else A[-1]
    print(f"\n   last A_k              = {complex(A[-1]):.6e}")
    print(f"   Aitken-extrapolated   A_infty = {complex(A_inf):.6e}")
    print(f"   |A_infty|             = {float(abs(A_inf)):.6e}")

    # ---- (III): direct propagation factor kappa(n) --------------------
    c_pred = float(p * omega ** 2 / (2 * q))
    print(f"\n (III)  kappa(n) = E[(J_n/qn)^(i w)] from the binomial law;"
          f"\n        Prop. 8.4: n|kappa-1| -> p w^2/(2q) = {c_pred:.3f}\n")
    print(f"   {'n':>6}   {'|kappa(n)-1|':>15} {'n*|kappa(n)-1|':>16}")
    kn = N_LO
    while kn <= n_max:
        kap = kappa_direct(kn, p, q, omega)
        dev = float(abs(kap - 1))
        print(f"   {kn:>6}   {dev:>15.4e} {kn*dev:>16.3f}")
        kn *= 2

    # ---- cross-check against the Flajolet-Sedgewick amplitude ---------
    tail = sorted(float(b[n]) for n in range(n_max // 2, n_max + 1))
    gamma0 = tail[len(tail) // 2]
    fs = float(exp(-pi ** 2 / L))
    print(f"\n   cross-check:  gamma_0                = {gamma0:.6f}")
    print(f"                 |A_infty|/(gamma_0 FS) = "
          f"{float(abs(A_inf))/(gamma0*fs):.3f}   "
          f"(manuscript span/FS ~ 5.1, i.e. ~2.5 for |gamma_1|)")
    return p_frac, ts, A, omega, L, n_max


def plot_A(result, out_path: Path):
    p_frac, ts, A_geo, omega, L, n_max = result
    p = mpf(p_frac.numerator) / mpf(p_frac.denominator)
    b = b_sequence(n_max, p)
    log_m = [mpf(0)] + [log(m) for m in range(1, n_max + 1)]
    inv_m = [mpf(0)] + [mpf(1) / m for m in range(1, n_max + 1)]
    t_min = log(mpf(N_LO)) + HALF_WIDTH * L
    t_max = log(mpf(n_max)) - (HALF_WIDTH + mpf(1) / 2) * L
    grid = [t_min + (t_max - t_min) * i / 120 for i in range(121)]
    Ag = [local_coefficient(b, log_m, inv_m, t, L, omega, n_max)
          for t in grid]
    xg = [float(t) for t in grid]
    fig, ax = plt.subplots(figsize=(7, 4))
    ax.plot(xg, [float(a.real) for a in Ag], "tab:blue", lw=1.0,
            label=r"$\mathrm{Re}\,A(t)$")
    ax.plot(xg, [float(a.imag) for a in Ag], "tab:red", lw=1.0,
            label=r"$\mathrm{Im}\,A(t)$")
    ax.plot(xg, [float(abs(a)) for a in Ag], "k--", lw=1.0,
            label=r"$|A(t)|$")
    ax.scatter([float(t) for t in ts], [float(a.real) for a in A_geo],
               color="tab:blue", s=18, zorder=5)
    ax.axhline(0, color="gray", lw=0.4)
    ax.set_xlabel(r"$t=\log n$")
    ax.set_ylabel(r"$A(t)$")
    ax.set_title(fr"Local fundamental coefficient, $p={p_frac.numerator}"
                 fr"/{p_frac.denominator}$ (dots: $t_0+kL$)")
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(out_path, dpi=140)
    print(f"\nwrote {out_path}")


def main() -> None:
    print(f"mpmath working precision: {mp.dps} decimal digits")
    print("Renormalisation-route validation (infMaxMin.tex, Section 8)")
    results = []
    for p_frac in [Fraction(9, 20), Fraction(21, 50),
                   Fraction(2, 5), Fraction(7, 20)]:
        results.append(validate(p_frac))
    plot_A(results[1], Path(__file__).parent / "renorm_validation_A.pdf")
    print(f"\n{'='*74}\n Reading the output:")
    print(" (I)   |A_k - A_(k-1)| shrinking  =>  A(t_0+kL) converges;")
    print(" (II)  |A_infty| far above the dps floor (~1e-48)  =>  the")
    print("       base case A_infty != 0 holds: b_n genuinely oscillates;")
    print(" (III) n*|kappa(n)-1| -> p w^2/(2q)  =>  |kappa-1| = O(1/n),")
    print("       confirming the propagation estimate of Prop. 8.4.")
    print(f"{'='*74}")


if __name__ == "__main__":
    main()
