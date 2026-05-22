"""D1 (perturbative) --- does the first-order perturbation of strategy
ALL at p = 1/2 oscillate?

With p = 1/2 - eps one has b_n(1/2) = 1/2 (n >= 1) and the first-order
term beta_n := d b_n/dp |_{p=1/2} satisfies

    beta_0 = 0,
    beta_n = n * 2^{1-n} + 2^{-n} * sum_{j<n} C(n,j) beta_j,

equivalently the EGF B1(z) = sum beta_n z^n/n! solves
    B1(z) = z e^{z/2} + (e^{z/2} - 1) B1(z/2).

If beta_n oscillates (log-periodically, period log 2) then Phi_p is
non-constant already to first order in eps -- D1 holds near p = 1/2
by perturbation. If beta_n converges, the oscillation of b is
non-perturbative and this route to D1 is dead.

This script computes beta_n and its windowed fundamental coefficient
A_inf(beta) at p = 1/2 (L = log 2).

Run from the repository root:
    .venv/bin/python simulation/d1_perturbation.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from renorm_validation import (  # noqa: E402
    chi, local_coefficient, aitken, HALF_WIDTH,
)
from mpmath import mp, mpf, log, pi, floor  # noqa: E402

mp.dps = 40


def beta_sequence(n_max):
    """First-order perturbation beta_n of strategy ALL at p = 1/2."""
    beta = [mpf(0)] * (n_max + 1)
    pow2 = [mpf(2) ** (-n) for n in range(n_max + 1)]
    for n in range(1, n_max + 1):
        total = mpf(0)
        binom = 1
        for j in range(0, n):
            total += binom * beta[j]
            binom = binom * (n - j) // (j + 1)
        beta[n] = n * 2 * pow2[n] + pow2[n] * total
    return beta


def main():
    n_max = 2000
    print(f"D1 perturbative test: beta_n up to n = {n_max} "
          f"at {mp.dps} dps ...")
    beta = beta_sequence(n_max)
    print(" beta_n at n = 1,2,3,5,10,50,200,1000,2000:")
    print("  ", [float(beta[n]) for n in (1, 2, 3, 5, 10, 50, 200,
                                          1000, 2000)])

    L = log(2)
    omega = 2 * pi / L
    log_m = [mpf(0)] + [log(m) for m in range(1, n_max + 1)]
    inv_m = [mpf(0)] + [mpf(1) / m for m in range(1, n_max + 1)]
    t_min = log(mpf(8)) + HALF_WIDTH * L
    t_max = log(mpf(n_max)) - (HALF_WIDTH + mpf(1) / 2) * L
    K = int(floor(float((t_max - t_min) / L)))
    A = [local_coefficient(beta, log_m, inv_m, t_min + k * L, L, omega,
                           n_max) for k in range(K + 1)]

    print(f"\n windowed fundamental coefficient A(t_0 + kL), "
          f"{K + 1} windows (L = log 2):")
    for k, a in enumerate(A):
        print(f"   k = {k:2d}   |A| = {float(abs(a)):.6e}   "
              f"A = {complex(a):+.4e}")
    A_inf = aitken(A[-3], A[-2], A[-1]) if len(A) >= 3 else A[-1]
    print(f"\n A_inf(beta)  (Aitken) = {complex(A_inf):+.6e}")
    print(f" |A_inf(beta)|         = {float(abs(A_inf)):.6e}")

    print()
    if float(abs(A_inf)) > 1e-11 and \
            float(abs(A[-1])) > 0.3 * float(abs(A[-3]) + 1e-300):
        print(" => beta_n OSCILLATES: the first-order perturbation is")
        print("    log-periodic -- the perturbative route to D1 is alive,")
        print("    and D1 holds near p = 1/2 by perturbation theory.")
    else:
        print(" => beta_n appears to CONVERGE (A(t_0+kL) -> 0): the")
        print("    oscillation of b is non-perturbative; the perturbative")
        print("    route to D1 fails and D1 needs the Mellin route.")


if __name__ == "__main__":
    main()
