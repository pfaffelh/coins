"""Numerical study of the log-periodic asymptotics predicted in
``Manuscript/strategy_all_asymptotics.tex``.

Prediction: for 0 < p < 1, p != 1/2, the winning probability b(p, n)
under strategy ALL is asymptotic to a continuous positive function
Phi_p periodic in log n with period log(1/(1-p)).  Equivalently,
b(p, n) ~ Phi_p(log(pn)), where Phi_p is (log(1/q))-periodic.

For p = 1/2 the sequence is the exact constant 1/2 (Theorem 2.1).
For p > 1/2 the sequence is monotone with finite limit W(p) (Thm 3.3),
which forces Phi_p to collapse to the constant W(p).
For p < 1/2 the Mellin analysis predicts a non-trivial Phi_p and hence
log-periodic oscillations that never settle to a single limit.

We verify the prediction numerically using mpmath at 50 dps and
plot the result.

Run from the repository root:
    .venv/bin/python simulation/b_asymptotics.py
"""

from __future__ import annotations

from fractions import Fraction
from math import log
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf


DPS = 50
mp.dps = DPS


def b_sequence(n_max: int, p):
    """Return [b_0, b_1, ..., b_{n_max}] at the precision of p."""
    one = mpf(1) if isinstance(p, (int, float, mpf)) else Fraction(1)
    q = one - p
    p_pow = [one]
    q_pow = [one]
    for _ in range(n_max):
        p_pow.append(p_pow[-1] * p)
        q_pow.append(q_pow[-1] * q)
    b = [one]  # b_0 = 1
    for n in range(1, n_max + 1):
        total = one - one  # zero
        binom = 1
        for j in range(0, n):
            # C(n, j) * p^(n-j) * q^j * b_j
            total = total + binom * p_pow[n - j] * q_pow[j] * b[j]
            binom = binom * (n - j) // (j + 1)
        b.append(total)
    return b


def check_half_exact(n_max: int = 200) -> None:
    """b(1/2, n) should equal 1/2 exactly for n >= 1."""
    b = b_sequence(n_max, mpf(1) / 2)
    bad = [n for n in range(1, n_max + 1) if abs(b[n] - mpf("0.5")) > mpf(10) ** (-DPS + 5)]
    print(f"[p = 1/2] b_n differs from 1/2 at n in: {bad[:10]}")
    assert not bad, f"unexpected deviation at n={bad}"


def geometric_progression_test(p_frac: Fraction, n_seeds, max_k: int) -> None:
    """At p = p_frac, compute b_n along n_k = round(n_0 * (1/q)^k) and
    check that the limit is approached as k grows.
    """
    p = mpf(p_frac.numerator) / mpf(p_frac.denominator)
    q = mpf(1) - p
    inv_q = mpf(1) / q

    # max n we need
    n_max = max(round(n0 * float(inv_q) ** max_k) for n0 in n_seeds) + 1
    print(f"\n[p = {p_frac}] computing b_n up to n = {n_max} at {DPS} dps ...")
    b = b_sequence(n_max, p)

    print(f"\nGeometric progression test: n_k = round(n_0 * (1/q)^k), q = 1-p = {float(q):.6f}")
    print(f"(period in log n: log(1/q) = {float(mp.log(inv_q)):.6f})\n")
    header = "      n_0 " + "".join(f"{'k=' + str(k):>14}" for k in range(max_k + 1))
    print(header)
    for n0 in n_seeds:
        row = f"{n0:>9} "
        for k in range(max_k + 1):
            n_k = round(n0 * float(inv_q) ** k)
            val = b[n_k]
            row += f"{float(val):>14.8f}"
        print(row)

    # Also print the "phase" = {log(p*n)/log(1/q)} of each n_k; they should
    # all agree modulo 1 (up to rounding error from integer n_k).
    print("\n(fractional phase log(p*n)/log(1/q) mod 1, should be ~constant across k for fixed n_0)")
    for n0 in n_seeds:
        row = f"{n0:>9} "
        for k in range(max_k + 1):
            n_k = round(n0 * float(inv_q) ** k)
            phase = (log(float(p) * n_k) / log(float(inv_q))) % 1.0
            row += f"{phase:>14.6f}"
        print(row)


def amplitude_summary(ps, n_max: int) -> None:
    """For each p, compute b_n up to n_max, then report:
      - the apparent mean gamma_0(p) (median of the second half),
      - the observed span max-min over the second half,
      - the Flajolet-Sedgewick prediction exp(-pi^2 / log(1/q))
        for the ratio of the first Fourier coefficient |gamma_1| to |gamma_0|.
    """
    print(f"\n{'p':>8}  {'log(1/q)':>10}  {'gamma_0 (median)':>22}  "
          f"{'obs span':>12}  {'FS predict':>12}  {'ratio':>8}")
    print("-" * 80)
    for p_frac in ps:
        p = mpf(p_frac.numerator) / mpf(p_frac.denominator)
        q = mpf(1) - p
        log_inv_q = float(mp.log(mpf(1) / q))
        b = b_sequence(n_max, p)
        tail = np.array([float(b[n]) for n in range(n_max // 2, n_max + 1)])
        gamma0 = float(np.median(tail))
        span = float(tail.max() - tail.min())
        fs_predict = float(mp.exp(-mp.pi ** 2 / mp.mpf(log_inv_q)))
        ratio = span / fs_predict if fs_predict > 0 else float("nan")
        print(f"{str(p_frac):>8}  {log_inv_q:>10.4f}  "
              f"{gamma0:>22.15f}  {span:>12.2e}  {fs_predict:>12.2e}  {ratio:>8.2f}")


def oscillation_plot(p_frac: Fraction, n_max: int, out_path: Path) -> None:
    """For a p where the log-periodic oscillation is visible, plot
    b_n - gamma_0 vs log n.  Log-periodicity means the plot shows a
    periodic wave of period log(1/q).
    """
    p = mpf(p_frac.numerator) / mpf(p_frac.denominator)
    q = mpf(1) - p
    log_inv_q = float(mp.log(mpf(1) / q))
    print(f"\n[p = {p_frac}] computing b_n up to n = {n_max} ...")
    b = b_sequence(n_max, p)
    ns = np.arange(1, n_max + 1)
    vals = np.array([float(b[n]) for n in ns])
    gamma0 = float(np.median(vals[n_max // 2:]))
    log_n = np.log(ns)

    fig, axes = plt.subplots(2, 1, figsize=(7, 5), sharex=True)
    axes[0].plot(log_n, vals, color="tab:blue", lw=0.6)
    axes[0].axhline(gamma0, color="k", lw=0.6, ls="--", label=fr"$\gamma_0 \approx {gamma0:.5f}$")
    axes[0].set_ylabel(r"$b(p,n)$")
    axes[0].set_title(
        fr"$p = {p_frac.numerator}/{p_frac.denominator}$,  "
        fr"period $\log(1/q) = {log_inv_q:.3f}$"
    )
    axes[0].legend(loc="upper right", fontsize=9)
    axes[0].grid(True, alpha=0.3)

    axes[1].plot(log_n, vals - gamma0, color="tab:red", lw=0.6)
    axes[1].axhline(0, color="k", lw=0.4)
    # Vertical period lines
    log_min = float(log_n[0])
    log_max = float(log_n[-1])
    k = int((log_max - log_min) / log_inv_q) + 2
    for i in range(-1, k):
        x = log_min + i * log_inv_q
        if log_min <= x <= log_max:
            axes[1].axvline(x, color="gray", lw=0.3, ls=":")
    axes[1].set_xlabel(r"$\log n$")
    axes[1].set_ylabel(r"$b(p,n) - \gamma_0$")
    axes[1].grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(out_path, dpi=140)
    print(f"wrote {out_path}")


def main() -> None:
    out_dir = Path(__file__).parent.parent / "Manuscript" / "figures"
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"mpmath working precision: {mp.dps} decimal digits\n")
    print("=" * 70)
    print("Sanity check: p = 1/2 gives b_n = 1/2 exactly")
    print("=" * 70)
    check_half_exact(n_max=200)

    print("\n" + "=" * 70)
    print("Geometric progression test at p = 1/3 (so 1/q = 3/2)")
    print("=" * 70)
    geometric_progression_test(Fraction(1, 3), n_seeds=[10, 17, 29], max_k=9)

    print("\n" + "=" * 70)
    print("Geometric progression test at p = 2/3 (so 1/q = 3)")
    print("=" * 70)
    geometric_progression_test(Fraction(2, 3), n_seeds=[4, 7, 11], max_k=6)

    print("\n" + "=" * 70)
    print("Amplitude summary across several p values")
    print("(FS predict = exp(-pi^2 / log(1/q)), the Flajolet-Sedgewick")
    print(" damping bound on |gamma_1| / |gamma_0|)")
    print("=" * 70)
    amplitude_summary(
        [Fraction(1, 4), Fraction(1, 3), Fraction(2, 5),
         Fraction(3, 5), Fraction(2, 3), Fraction(3, 4), Fraction(4, 5)],
        n_max=800,
    )

    print("\n" + "=" * 70)
    print("Oscillation plot at p = 3/4 (large amplitude)")
    print("=" * 70)
    oscillation_plot(Fraction(3, 4), n_max=1500, out_path=out_dir / "b_oscillation_p075.pdf")

    print("\n" + "=" * 70)
    print("Oscillation plot at p = 2/3")
    print("=" * 70)
    oscillation_plot(Fraction(2, 3), n_max=1500, out_path=out_dir / "b_oscillation_p066.pdf")


if __name__ == "__main__":
    main()
