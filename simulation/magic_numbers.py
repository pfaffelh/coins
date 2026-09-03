"""Magic numbers and convergence of the optimal value w_{n,p} for p < 1/2.

For each p on a grid this script computes, in high-precision arithmetic,
  * w_n  (optimal value, Bellman recursion with suffix maximum),
  * b_n  (strategy ALL / greedy, linear recursion),
  * the *magic numbers*: suffix-maximum records of (w_n), i.e. the states
    m with w_m > w_k for all m < k <= N  (these are exactly the states an
    optimal player reduces to),
  * the *dips*: indices n with w_n < w_{n-1},
  * the relative oscillation of w and of b over the window [N/2, N],
  * the gap w_N - b_N.

Usage:  python3 simulation/magic_numbers.py [N] [dps]
"""
import sys
import mpmath as mp

P_GRID = ['0.05', '0.10', '0.15', '0.20', '0.25', '0.30', '0.35',
          '0.40', '0.42', '0.45', '0.47', '0.49']


def run(p, N):
    """Return lists w[0..N], b[0..N] and the policy at n = N."""
    p = mp.mpf(p)
    q = 1 - p
    r = q / p
    w = [mp.mpf(1)]
    b = [mp.mpf(1)]
    pol = None
    for n in range(1, N + 1):
        t = p ** n                      # weight C(n,0) p^n q^0
        sw = t
        sb = t
        sm = [None] * n                 # suffix max of w over [j, n-1]
        am = [None] * n                 # its argmax
        cur, ca = None, None
        for j in range(n - 1, 0, -1):
            if cur is None or w[j] > cur:
                cur, ca = w[j], j
            sm[j], am[j] = cur, ca
        for j in range(1, n):
            t = t * (n - j + 1) / j * r  # C(n,j) p^{n-j} q^j
            sw += t * sm[j]
            sb += t * b[j]
        w.append(sw)
        b.append(sb)
        if n == N:
            pol = am
    return w, b, pol


def records(w, N):
    """Suffix-maximum records (magic numbers) of w on [1, N]."""
    rec, cur = [], None
    for n in range(N, 0, -1):
        if cur is None or w[n] > cur:
            rec.append(n)
            cur = w[n]
    return sorted(rec)


def compress(rec):
    """Print an initial run 1..k as '1..k'."""
    k = 0
    while k < len(rec) and rec[k] == k + 1:
        k += 1
    head = [f"1..{k}"] if k > 1 else [str(x) for x in rec[:k]]
    return head + [str(x) for x in rec[k:]]


def relosc(x, lo, hi):
    seg = x[lo:hi + 1]
    return (max(seg) - min(seg)) / max(seg)


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 700
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 220
    print(f"N = {N}, dps = {mp.mp.dps}")
    print(f"{'p':>5} | {'magic numbers (records on [1,N])':<45} | "
          f"{'dips n (w_n<w_n-1), n>=10':<28} | {'relosc w':>9} | "
          f"{'relosc b':>9} | {'w_N - b_N':>10} | {'d_N':>9}")
    for ps in P_GRID:
        w, b, pol = run(ps, N)
        rec = records(w, N)
        dips = [n for n in range(10, N + 1) if w[n] < w[n - 1]]
        # compress consecutive dips
        groups, start = [], None
        for n in dips:
            if start is None:
                start = prev = n
            elif n == prev + 1:
                prev = n
            else:
                groups.append((start, prev)); start = prev = n
        if start is not None:
            groups.append((start, prev))
        dstr = ','.join(f"{a}" if a == c else f"{a}-{c}" for a, c in groups)
        print(f"{ps:>5} | {' '.join(compress(rec)):<45} | {dstr:<28} | "
              f"{mp.nstr(relosc(w, N // 2, N), 3):>9} | "
              f"{mp.nstr(relosc(b, N // 2, N), 3):>9} | "
              f"{mp.nstr(w[N] - b[N], 4):>10} | {mp.nstr(w[N] - w[N-1], 3):>9}")
