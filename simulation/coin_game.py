"""Simulation of the coin game from vibe.md.

Game: start with n coins, each lands heads with probability p. In every round
all remaining coins are tossed and at least one coin must be set aside (it is
never tossed again). You win iff every coin set aside shows heads.

Two strategies:
    (A) If at least one head and not all heads: set aside exactly one head.
        If all heads: set aside all (and win). If zero heads: forced to set
        aside a tails -> lose.
    (B) If at least one head: set aside every head. If zero heads: forced
        to set aside a tails -> lose.

Exact functions are polymorphic on the numeric type of p: pass a float for
fast double-precision, a fractions.Fraction for exact rational arithmetic,
or an mpmath.mpf for arbitrary-precision decimals. Set mpmath.mp.dps before
passing an mpf to control the precision.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any

import numpy as np
from mpmath import mp, mpf


def _one_like(p: Any) -> Any:
    if isinstance(p, mpf):
        return mpf(1)
    if isinstance(p, Fraction):
        return Fraction(1)
    return type(p)(1)


def simulate_strategy_A(n: int, p: float, trials: int, rng: np.random.Generator) -> float:
    wins = 0
    for _ in range(trials):
        remaining = n
        alive = True
        while remaining > 0:
            heads = int(rng.binomial(remaining, p))
            if heads == 0:
                alive = False
                break
            if heads == remaining:
                break
            remaining -= 1
        if alive:
            wins += 1
    return wins / trials


def simulate_strategy_B(n: int, p: float, trials: int, rng: np.random.Generator) -> float:
    wins = 0
    for _ in range(trials):
        remaining = n
        alive = True
        while remaining > 0:
            heads = int(rng.binomial(remaining, p))
            if heads == 0:
                alive = False
                break
            remaining -= heads
        if alive:
            wins += 1
    return wins / trials


def exact_A(n: int, p: Any) -> Any:
    """Probability of winning with strategy (A).

    Recursion: p_n = p^n + (1 - p^n - (1-p)^n) * p_{n-1}, p_0 = 1.
    """
    one = _one_like(p)
    q = one
    for k in range(1, n + 1):
        pk = p ** k
        qk = (one - p) ** k
        q = pk + (one - pk - qk) * q
    return q


def exact_B(n: int, p: Any) -> Any:
    """Probability of winning with strategy (B).

    Recursion (see manuscript): p_n = sum_{k=0}^{n-1} C(n,k) (1-p)^k p^{n-k} p_k.
    """
    one = _one_like(p)
    probs = [one]
    for m in range(1, n + 1):
        total = _one_like(p) - _one_like(p)  # zero of same type
        binom = 1
        for k in range(0, m):
            total = total + binom * (one - p) ** k * p ** (m - k) * probs[k]
            binom = binom * (m - k) // (k + 1)
        probs.append(total)
    return probs[n]


def exact_optimal(n: int, p: Any) -> Any:
    """Optimal win probability via Bellman recursion over w_{k,p}, k=1..n.

    w_{m,p} = p^m + sum_{j=1}^{m-1} C(m,j) p^{m-j} (1-p)^j * max_{j <= i <= m-1} w_{i,p},
    where j is the number of tails in the round.
    """
    one = _one_like(p)
    zero = one - one
    w = [zero] * (n + 1)
    w[1] = p
    for m in range(2, n + 1):
        suffix_max = [zero] * (m + 1)
        suffix_max[m - 1] = w[m - 1]
        for j in range(m - 2, 0, -1):
            suffix_max[j] = max(w[j], suffix_max[j + 1])
        total = p ** m
        binom = 1
        for j in range(1, m):
            binom = binom * (m - j + 1) // j
            total = total + binom * p ** (m - j) * (one - p) ** j * suffix_max[j]
        w[m] = total
    return w[n]


def _fmt(x: Any, digits: int) -> str:
    if isinstance(x, Fraction):
        return _fmt(mpf(x.numerator) / mpf(x.denominator), digits)
    if isinstance(x, mpf):
        return mp.nstr(x, digits, strip_zeros=False)
    return f"{float(x):.{digits}f}"


def compare(
    n_values,
    p_values,
    trials: int = 100_000,
    seed: int = 0,
    dps: int = 15,
    digits: int | None = None,
) -> None:
    """Print a table comparing simulated and exact win probabilities.

    Parameters
    ----------
    n_values, p_values : iterables of n and p values (p may be str, float,
        Fraction, or mpf). Strings are parsed to mpf at the current precision.
    trials : Monte-Carlo trials per (n, p) cell.
    seed : RNG seed.
    dps : decimal digits of working precision for mpmath (ignored for
        Fraction/float inputs).
    digits : number of digits printed (default: dps - 2).
    """
    mp.dps = dps
    if digits is None:
        digits = max(4, dps - 2)
    rng = np.random.default_rng(seed)
    width = max(digits + 3, 9)
    cols = ["n", "p", "A_sim", "A_exact", "B_sim", "B_exact", "opt"]
    row_fmt = (
        f"{{:>3}} {{:>{width}}} {{:>{width}}} {{:>{width}}} "
        f"{{:>{width}}} {{:>{width}}} {{:>{width}}}"
    )
    header = row_fmt.format(*cols)
    print(header)
    print("-" * len(header))
    for n in n_values:
        for p in p_values:
            p_exact = mpf(p) if isinstance(p, str) else p
            p_float = float(p_exact) if not isinstance(p_exact, float) else p_exact
            a_s = simulate_strategy_A(n, p_float, trials, rng)
            b_s = simulate_strategy_B(n, p_float, trials, rng)
            a_e = exact_A(n, p_exact)
            b_e = exact_B(n, p_exact)
            opt = exact_optimal(n, p_exact)
            print(
                row_fmt.format(
                    n,
                    _fmt(p_exact, digits),
                    _fmt(mpf(a_s), digits),
                    _fmt(a_e, digits),
                    _fmt(mpf(b_s), digits),
                    _fmt(b_e, digits),
                    _fmt(opt, digits),
                )
            )


if __name__ == "__main__":
    print("=== Double-precision floats (default) ===")
    compare(
        n_values=[2, 3, 5, 8, 15],
        p_values=[0.2, 0.35, 0.5, 0.65, 0.8],
        trials=100_000,
        dps=15,
    )

    print("\n=== Arbitrary precision: 40 decimal digits ===")
    compare(
        n_values=[5, 10, 20],
        p_values=["0.2", "0.5495021777642", "0.65"],
        trials=50_000,
        dps=40,
    )

    print("\n=== Exact rational arithmetic (Fraction) ===")
    mp.dps = 60
    for n in [3, 5, 10]:
        p = Fraction(1, 3)
        q = exact_optimal(n, p)
        assert isinstance(q, Fraction)
        print(f"n={n:>3}, p=1/3  opt = {q}  ≈ {mpf(q.numerator)/mpf(q.denominator)}")
