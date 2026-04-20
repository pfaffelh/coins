"""Generate figures and tables for the simulation section of the manuscript.

Produces:
    Manuscript/figures/w_vs_n.pdf       — w_{n,p} vs n for several p < 1/2.
    Manuscript/figures/gap_vs_n.pdf     — w_{n,p} - w_{n-1,p} vs n (gap plot).
    stdout                              — numerical tables.

The figures show, in particular, the appearance of local maxima for p bounded
away from 1/2 (e.g., at n = 9 for p = 0.42), which are invisible in the
first-order expansion (Corollary 4.11(iii)).
"""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
from mpmath import mp, mpf

from compare_B_vs_optimal import optimal_sequence


def compute_w_table(p_values: list[str], n_max: int, dps: int = 60):
    mp.dps = dps
    data = {}
    data_exact = {}
    for p_str in p_values:
        p = mpf(p_str)
        w, _ = optimal_sequence(n_max, p)
        data[p_str] = [float(wn) for wn in w]  # index 0..n_max
        data_exact[p_str] = w  # keep mpf values for extrema detection
    return data, data_exact


def find_extrema_exact(w, n_min: int, n_max: int):
    mins, maxs = [], []
    for n in range(n_min, n_max):
        if w[n] < w[n - 1] and w[n] < w[n + 1]:
            mins.append(n)
        if w[n] > w[n - 1] and w[n] > w[n + 1]:
            maxs.append(n)
    return mins, maxs


def plot_w_vs_n(data, n_min: int, n_max: int, out: Path) -> None:
    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    markers = ["o", "s", "D", "^", "v"]
    colors = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]
    for idx, (p_str, w) in enumerate(data.items()):
        xs = list(range(n_min, n_max + 1))
        ys = [w[n] for n in xs]
        ax.plot(
            xs, ys,
            marker=markers[idx % len(markers)],
            color=colors[idx % len(colors)],
            markersize=5,
            linewidth=1.2,
            label=f"$p={p_str}$",
        )
    ax.set_xlabel("$n$ (number of coins)")
    ax.set_ylabel("$w_{n,p}$ (optimal winning probability)")
    ax.set_xticks(range(n_min, n_max + 1, 2))
    ax.grid(True, alpha=0.3)
    ax.legend(loc="best", frameon=True)
    fig.tight_layout()
    fig.savefig(out)
    plt.close(fig)


def plot_detail_p042(data, n_min: int, n_max: int, out: Path) -> None:
    """Zoomed-in plot for p ∈ {0.42, 0.45} showing the local maximum."""
    fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.8))
    for ax, p_str in zip(axes, ["0.42", "0.45"]):
        w = data[p_str]
        xs = list(range(n_min, n_max + 1))
        ys = [w[n] for n in xs]
        ax.plot(xs, ys, marker="o", color="#d62728", markersize=5, linewidth=1.2)
        # Highlight extrema.
        from mpmath import mpf
        for n in range(n_min + 1, n_max):
            if (w[n] > w[n - 1] and w[n] > w[n + 1]):
                ax.plot(n, w[n], marker="*", color="black", markersize=12,
                        label=f"local max at $n={n}$")
            if (w[n] < w[n - 1] and w[n] < w[n + 1]):
                ax.plot(n, w[n], marker="v", color="black", markersize=10,
                        label=f"local min at $n={n}$")
        ax.set_xlabel("$n$")
        ax.set_ylabel("$w_{n,p}$")
        ax.set_title(f"$p={p_str}$")
        ax.set_xticks(range(n_min, n_max + 1, 2))
        ax.grid(True, alpha=0.3)
        ax.legend(loc="best", frameon=True, fontsize=8)
    fig.tight_layout()
    fig.savefig(out)
    plt.close(fig)


def plot_gap(data, n_min: int, n_max: int, out: Path) -> None:
    """Plot w_{n,p} - w_{n-1,p} to highlight monotonicity structure."""
    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    markers = ["o", "s", "D", "^", "v"]
    colors = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]
    for idx, (p_str, w) in enumerate(data.items()):
        xs = list(range(n_min, n_max + 1))
        ys = [w[n] - w[n - 1] for n in xs]
        ax.plot(
            xs, ys,
            marker=markers[idx % len(markers)],
            color=colors[idx % len(colors)],
            markersize=5,
            linewidth=1.2,
            label=f"$p={p_str}$",
        )
    ax.axhline(0.0, color="black", linewidth=0.6, linestyle="--")
    ax.set_xlabel("$n$")
    ax.set_ylabel("$w_{n,p} - w_{n-1,p}$")
    ax.set_xticks(range(n_min, n_max + 1, 2))
    ax.grid(True, alpha=0.3)
    ax.legend(loc="best", frameon=True)
    fig.tight_layout()
    fig.savefig(out)
    plt.close(fig)


def find_extrema(w: list[float], n_min: int, n_max: int):
    """Return lists of local minima and local maxima in [n_min, n_max-1]."""
    mins, maxs = [], []
    for n in range(n_min, n_max):
        if w[n] < w[n - 1] and w[n] < w[n + 1]:
            mins.append(n)
        if w[n] > w[n - 1] and w[n] > w[n + 1]:
            maxs.append(n)
    return mins, maxs


def print_table(data, data_exact, n_max: int) -> None:
    print(f"{'n':>3}", end="")
    for p_str in data:
        print(f"  w(n, {p_str})", end="")
    print()
    for n in range(1, n_max + 1):
        print(f"{n:>3}", end="")
        for p_str, w in data.items():
            print(f"  {w[n]:.10f}", end="")
        print()
    print()
    for p_str, w in data_exact.items():
        mins, maxs = find_extrema_exact(w, 2, n_max - 1)
        print(f"p = {p_str}:  local minima at n ∈ {mins},  local maxima at n ∈ {maxs}")


def main() -> None:
    here = Path(__file__).resolve().parent
    figdir = here.parent / "Manuscript" / "figures"
    figdir.mkdir(parents=True, exist_ok=True)

    p_values = ["0.49", "0.45", "0.42", "0.35", "0.25"]
    n_max = 20
    data, data_exact = compute_w_table(p_values, n_max=n_max, dps=80)

    plot_w_vs_n(data, n_min=1, n_max=n_max, out=figdir / "w_vs_n.pdf")
    plot_gap(data, n_min=2, n_max=n_max, out=figdir / "gap_vs_n.pdf")
    plot_detail_p042(data, n_min=5, n_max=n_max, out=figdir / "local_max_detail.pdf")

    print_table(data, data_exact, n_max=n_max)


if __name__ == "__main__":
    main()
