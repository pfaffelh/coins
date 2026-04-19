"""Numerical comparison of the optimal strategy vs strategy (B) for p < 1/2.

Recall the Bellman recursion for w_{n,p} (probability of winning under optimal
play) of the all-heads-wins game:

    w_{n,p} = p^n + sum_{j=1}^{n-1} C(n,j) p^{n-j} (1-p)^j
                                  * max_{j <= k <= n-1} w_{k,p},

where j is the number of tails this round and k = n - i is the remaining number
of coins after setting aside i heads (1 <= i <= n-j).

Strategy (B) picks i = n-j, i.e. sets aside every head, leaving k = j.
(B) is therefore optimal at step n iff

    w_{j,p} = max_{j <= k <= n-1} w_{k,p}    for every j = 1, ..., n-1,

which is equivalent to k -> w_{k,p} being monotonically non-increasing on
[1, n-1]. Hence (B) is optimal for all n iff k -> w_{k,p} is non-increasing
on all of N.

This script computes w_{k,p} with arbitrary precision, checks monotonicity
up to some N, and prints opt - B_exact.
"""

from __future__ import annotations

from mpmath import mp, mpf

from coin_game import exact_B


def optimal_sequence(n_max: int, p):
    """Return (w[0..n_max], first_k_with_w_k >= w_{k-1}, or None)."""
    one = mpf(1) if isinstance(p, mpf) else 1
    zero = one - one
    w = [zero] * (n_max + 1)
    w[1] = p
    increase_at = None
    for m in range(2, n_max + 1):
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
        if w[m] >= w[m - 1] and increase_at is None:
            increase_at = m
    return w, increase_at


def table(p_values, n_list, n_max, dps=60, digits=20):
    mp.dps = dps
    header = (
        f"{'p':>14} {'n':>5} {'B':>{digits+3}} {'opt':>{digits+3}} "
        f"{'opt - B':>{digits+3}}  monotone?"
    )
    print(header)
    print("-" * len(header))
    for p_str in p_values:
        p = mpf(p_str)
        w, bad = optimal_sequence(n_max, p)
        monotone_str = "yes (up to n_max)" if bad is None else f"no, fails at k={bad}"
        for n in n_list:
            if n > n_max:
                continue
            B = exact_B(n, p)
            opt = w[n]
            diff = opt - B
            print(
                f"{p_str:>14} {n:>5} "
                f"{mp.nstr(B, digits, strip_zeros=False):>{digits+3}} "
                f"{mp.nstr(opt, digits, strip_zeros=False):>{digits+3}} "
                f"{mp.nstr(diff, 3):>{digits+3}}  {monotone_str}"
            )
        print()


def monotonicity_scan(p_values, n_max, dps=60):
    """For each p, report the first k (if any) at which w_k >= w_{k-1}."""
    mp.dps = dps
    print(f"Monotonicity of k -> w_{{k,p}} up to n = {n_max} (mpmath dps={dps}):")
    print(f"{'p':>14}  {'first k with w_k >= w_{k-1}':>30}")
    print("-" * 48)
    for p_str in p_values:
        p = mpf(p_str)
        _, bad = optimal_sequence(n_max, p)
        print(f"{p_str:>14}  {('never' if bad is None else str(bad)):>30}")


if __name__ == "__main__":
    small_p = ["0.05", "0.1", "0.2", "0.3", "0.4", "0.45", "0.49", "0.499", "0.4999"]

    print("=== opt vs B for p < 1/2, small n ===\n")
    table(
        p_values=small_p,
        n_list=[2, 3, 5, 10, 20, 40],
        n_max=40,
        dps=60,
        digits=18,
    )

    print("\n=== Monotonicity scan: does w_{k,p} ever increase up to n_max=200? ===\n")
    monotonicity_scan(
        p_values=small_p + ["0.4999999", "0.49999999"],
        n_max=200,
        dps=80,
    )
