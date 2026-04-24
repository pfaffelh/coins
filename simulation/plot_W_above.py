"""Plot W(p) = lim_{n -> infty} w_{n,p} for p in (0.5, 1).

Uses the linear recursion
    w_{n,p} = p^n + (1 - p^n - q^n) w_{n-1,p},   w_0 = 1,
valid for p > 1/2 (Corollary 3.4 of the manuscript).  Iterates to
large enough n so that the truncation error is below 10^(-10).

Output:
    Manuscript/figures/W_above.pdf
"""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
from mpmath import mp, mpf


def compute_W(p_str: str, dps: int = 80, n_max: int = 400) -> mpf:
    """Compute W(p) by iterating the linear recursion until convergence."""
    mp.dps = dps
    p = mpf(p_str)
    q = mpf(1) - p
    w = mpf(1)  # w_0
    for n in range(1, n_max + 1):
        pn = p ** n
        qn = q ** n
        w = pn + (mpf(1) - pn - qn) * w
    return w


def main() -> None:
    here = Path(__file__).resolve().parent
    figdir = here.parent / "Manuscript" / "figures"
    figdir.mkdir(parents=True, exist_ok=True)

    mp.dps = 80

    # Dense grid for the curve.
    n_grid = 200
    ps = [mpf(50 + i) / 100 for i in range(1, n_grid)]  # 0.51 ... 0.99
    ws = [float(compute_W(str(p), dps=80, n_max=300)) for p in ps]
    xs = [float(p) for p in ps]

    # Selected tabulated values.
    marks_p = [0.55, 0.6, 0.7, 0.9]
    marks_W = [float(compute_W(str(p), dps=80, n_max=400)) for p in marks_p]

    fig, ax = plt.subplots(figsize=(6.0, 4.0))
    ax.plot(xs, ws, color="#1f77b4", linewidth=1.4, label=r"$W(p)$")
    ax.plot(marks_p, marks_W, marker="o", linestyle="none",
            color="#d62728", markersize=6, zorder=5)
    # Annotate each marker.
    offsets = [(0.006, -0.04), (0.006, -0.04),
               (0.006, -0.04), (-0.08, -0.04)]
    for (pv, wv, (dx, dy)) in zip(marks_p, marks_W, offsets):
        ax.annotate(fr"$W({pv:.2f})\approx {wv:.4f}$",
                    xy=(pv, wv),
                    xytext=(pv + dx, wv + dy),
                    fontsize=9,
                    arrowprops=dict(arrowstyle="-", color="black", lw=0.4))
    # Reference lines.
    ax.axhline(0.5, color="gray", linewidth=0.6, linestyle=":")
    ax.axhline(1.0, color="gray", linewidth=0.6, linestyle=":")
    ax.axvline(0.5, color="gray", linewidth=0.6, linestyle=":")
    ax.set_xlabel(r"$p$")
    ax.set_ylabel(r"$W(p)$")
    ax.set_xlim(0.5, 1.0)
    ax.set_ylim(0.45, 1.05)
    ax.set_xticks([0.5, 0.6, 0.7, 0.8, 0.9, 1.0])
    ax.set_yticks([0.5, 0.6, 0.7, 0.8, 0.9, 1.0])
    ax.grid(True, alpha=0.3)
    ax.legend(loc="lower right", frameon=True, fontsize=9)
    fig.tight_layout()
    fig.savefig(figdir / "W_above.pdf")
    plt.close(fig)

    # Print the tabulated values for sanity.
    for pv, wv in zip(marks_p, marks_W):
        print(f"W({pv}) = {wv:.10f}")


if __name__ == "__main__":
    main()
