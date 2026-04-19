"""Print the optimal policy i*(n, k) for given p.

Given n coins remaining in a round and k of them landing heads (so n - k tails),
we may set aside i heads with 1 <= i <= k. The remaining n - i coins are then
re-tossed. The optimal choice is

    i*(n, k) = argmax_{1 <= i <= k} w_{n-i, p},

with ties broken by the smallest i (equivalent strategies prefer keeping more
coins in play).

Degenerate cases:
    k = 0 -> forced to set aside a tails -> lose (reported as "-").
    k = n -> set aside all (win immediately); reported as n.
"""

from __future__ import annotations

from mpmath import mp, mpf

from compare_B_vs_optimal import optimal_sequence


def optimal_policy(n_max: int, p) -> list[list[int | str]]:
    """policy[n][k] = optimal i for n = 1..n_max, k = 0..n."""
    w, _ = optimal_sequence(n_max, p)
    policy: list[list[int | str]] = [[] for _ in range(n_max + 1)]
    for n in range(1, n_max + 1):
        row: list[int | str] = ["-"]  # k = 0
        for k in range(1, n):
            best_i = 1
            best_val = w[n - 1]
            for i in range(2, k + 1):
                if w[n - i] > best_val:
                    best_val = w[n - i]
                    best_i = i
            row.append(best_i)
        row.append(n)  # k = n: take all
        policy[n] = row
    return policy


def print_policy(policy: list[list[int | str]], n_max: int, title: str = "") -> None:
    if title:
        print(title)
    header = f"{'n\\k':>4} " + " ".join(f"{k:>3}" for k in range(n_max + 1))
    print(header)
    print("-" * len(header))
    for n in range(1, n_max + 1):
        cells = " ".join(f"{str(x):>3}" for x in policy[n])
        padding = "    " * (n_max - n)
        print(f"{n:>4} {cells}")


if __name__ == "__main__":
    mp.dps = 60
    p = mpf("0.45")
    n_max = 15
    policy = optimal_policy(n_max, p)
    print_policy(
        policy,
        n_max,
        title=f"Optimal number of heads to set aside for p = 0.45 (n rows, k columns):",
    )
