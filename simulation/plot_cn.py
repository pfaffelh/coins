"""Plot the sequence n -> c_n for the first-order coefficient.

Computes c_n via the Bellman-like recursion of Proposition 4.4,
in arbitrary-precision rational arithmetic via mpmath, and plots
n vs c_n for 1 <= n <= n_max, with the limit L marked.

Output:
    Manuscript/figures/cn_sequence.pdf
"""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
from mpmath import mp, mpf


def compute_c(n_max: int, dps: int = 80) -> list[mpf]:
    """c[0] = 0 (unused); c[1..n_max] computed via Prop 4.4 recursion."""
    mp.dps = dps
    c = [mpf(0)] * (n_max + 1)
    c[1] = mpf(1)
    for n in range(2, n_max + 1):
        # n / 2^(n-1)
        first = mpf(n) / mpf(2) ** (n - 1)
        # Σ_{j=1}^{n-1} C(n,j) * min_{j <= m <= n-1} c_m
        binom = 1
        suffix_min = [mpf(0)] * (n + 1)
        suffix_min[n - 1] = c[n - 1]
        for j in range(n - 2, 0, -1):
            suffix_min[j] = min(c[j], suffix_min[j + 1])
        rest = mpf(0)
        for j in range(1, n):
            binom = binom * (n - j + 1) // j
            rest = rest + mpf(binom) * suffix_min[j]
        c[n] = first + rest / mpf(2) ** n
    return c


def plot_cn(c: list[mpf], n_max: int, L: float, out: Path) -> None:
    fig, ax = plt.subplots(figsize=(6.0, 3.8))
    xs = list(range(1, n_max + 1))
    ys = [float(c[n]) for n in xs]
    ax.plot(xs, ys, marker="o", color="#1f77b4", markersize=5, linewidth=1.2,
            label=r"$c_n$")
    ax.axhline(L, color="#d62728", linewidth=0.9, linestyle="--",
               label=fr"$L = \lim c_n \approx {L:.5f}$")
    ax.axhline(27/16, color="gray", linewidth=0.6, linestyle=":",
               label=r"$\frac{27}{16}=1.6875$ (lower bound)")
    # Mark the maximum at n = 5.
    ax.plot(5, ys[5 - 1], marker="*", color="black", markersize=12, zorder=5)
    ax.annotate(r"max at $n=5$", xy=(5, ys[5 - 1]),
                xytext=(7.5, ys[5 - 1] + 0.005),
                fontsize=9,
                arrowprops=dict(arrowstyle="-", color="black", lw=0.5))
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"$c_n$")
    ax.set_xticks(range(1, n_max + 1, 2))
    ax.grid(True, alpha=0.3)
    ax.legend(loc="lower right", frameon=True, fontsize=9)
    fig.tight_layout()
    fig.savefig(out)
    plt.close(fig)


def main() -> None:
    here = Path(__file__).resolve().parent
    figdir = here.parent / "Manuscript" / "figures"
    figdir.mkdir(parents=True, exist_ok=True)

    n_max = 25
    c = compute_c(n_max=n_max, dps=80)
    L = float(c[n_max])  # very close to the limit at n = 25

    print(f"{'n':>3}  {'c_n':>14}")
    for n in range(1, n_max + 1):
        print(f"{n:>3}  {float(c[n]):.10f}")
    print(f"\nLimit L ≈ c_{n_max} = {L:.10f}")

    plot_cn(c, n_max=n_max, L=L, out=figdir / "cn_sequence.pdf")


if __name__ == "__main__":
    main()
