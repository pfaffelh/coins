"""Exact increment identity, convergence, and the birth of magic numbers.

Write wt_j := C(n,j) p^{n-j} q^j and K_j^{(n)} := max_{j<=m<=n-1} w_m.
Subtracting  w_{n-1} * 1 = w_{n-1} (p^n + q^n + sum_j wt_j)  from the
Bellman equation gives the EXACT identity, valid for every n >= 1:

   d_n := w_n - w_{n-1}
        = p^n (1 - w_{n-1}) - q^n w_{n-1}
          + sum_{j=1}^{n-1} wt_j ( K_j^{(n)} - w_{n-1} ),                (E)

in which the first and the last term are >= 0.  Consequences:

 (C1) d_n >= -q^n w_{n-1} >= -q^n.  Hence sum_n (d_n)^- <= q/p < oo, the
      sequence (w_n) has bounded variation, and  w_n -> W(p)  converges
      for EVERY p in (0,1).  (New for p < 1/2.)
 (C2) A dip (w_n < w_{n-1}, i.e. the birth of a new magic number n-1)
      occurs iff   q^n w_{n-1} > p^n (1-w_{n-1}) + sum_j wt_j (K_j - w_{n-1}).
 (C3) Grouping the sum by magic numbers m_1 < ... < m_K (records of w
      before n): K_j = w_{m(j)} with m(j) the smallest record >= j, so
      the sum equals  sum_k P(m_{k-1} < Bin(n,q) <= m_k) (w_{m_k} - w_{n-1})
      plus the contribution of the non-record range above m_K.
      After the recovery phase following a birth, the next birth is at
      the first n with
          sum_k P(m_{k-1} < Bin(n,q) <= m_k) gamma_k  <  q^n W(p),
      gamma_k := w_{m_k} - W(p).  The last (largest) record dominates.

This script checks (E) exactly, verifies (C1), and compares the
prediction (C3) -- evaluated with gamma_k = w_{m_k} - w_N -- with the
observed births.

Usage: python3 simulation/magic_birth.py p [N] [dps]
"""
import sys
import mpmath as mp
from magic_numbers import run, records

ps = sys.argv[1] if len(sys.argv) > 1 else '0.45'
N = int(sys.argv[2]) if len(sys.argv) > 2 else 700
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 220

p = mp.mpf(ps)
q = 1 - p
w, b, _ = run(ps, N)
rec = [m for m in records(w, N) if m < N]   # magic numbers (drop trivial N)
w_inf = w[N]                                 # proxy for W(p)


def binom_cdf(n, M):
    """P(Bin(n,q) <= M) in high precision."""
    t = p ** n
    s = t
    for j in range(1, M + 1):
        t = t * (n - j + 1) / j * q / p
        s += t
    return s


# ---- (E) exact check over all n --------------------------------------
err = mp.mpf(0)
for n in range(2, N + 1):
    K = w[n - 1]
    rhs = p ** n * (1 - w[n - 1]) - q ** n * w[n - 1]
    t = p ** n
    Ks = [None] * n
    cur = None
    for j in range(n - 1, 0, -1):
        cur = w[j] if cur is None else max(cur, w[j])
        Ks[j] = cur
    for j in range(1, n):
        t = t * (n - j + 1) / j * q / p
        rhs += t * (Ks[j] - w[n - 1])
    err = max(err, abs(rhs - (w[n] - w[n - 1])))
print(f"p = {ps}, N = {N}: max_n |(E) - d_n| = {mp.nstr(err, 3)}")

# ---- (C1) ---------------------------------------------------------------
neg = sum(max(w[n - 1] - w[n], 0) for n in range(1, N + 1))
worst = max((w[n - 1] - w[n]) / q ** n for n in range(1, N + 1))
print(f"sum of negative increments = {mp.nstr(neg, 5)}  (bound q/p = {mp.nstr(q/p, 5)}); "
      f"max_n (-d_n)/q^n = {mp.nstr(worst, 4)}  (must be <= 1)")

# ---- (C3) predicted vs observed births ----------------------------------
print(f"magic numbers: {rec}")
print("births after each record (observed = next dip; predicted from (C3)):")
def predict(k, lo, hi):
    """First n in (lo, hi] with sum_{i<=k} P(m_{i-1}<Bin<=m_i) gamma_i < q^n w_inf."""
    for n in range(lo + 1, hi + 1):
        s = mp.mpf(0)
        prev = 0
        for i in range(k + 1):
            m = rec[i]
            s += (binom_cdf(n, m) - binom_cdf(n, prev)) * (w[m] - w_inf)
            prev = m
        if s < q ** n * w_inf:
            return n
    return None

dips = [n for n in range(2, N + 1) if w[n] < w[n - 1]]
for k, M in enumerate(rec):
    if M < 4:
        continue
    obs = next((n for n in dips if n > M + 1 and n - 1 > M and w[n-1] >= w[M] - (w[M]-w_inf)*0 and n > M + 2), None)
    # observed birth of the NEXT record: first dip n with n-1 > M and w_{n-1} > all later values,
    # i.e. n-1 is the next magic number
    nxt = rec[k + 1] if k + 1 < len(rec) else None
    obs = nxt + 1 if nxt is not None else None
    pred = predict(k, M + 1, 20 * N)
    gam = w[M] - w_inf
    tag = "" if nxt is not None else "   (gamma_M only an upper bound -> prediction is an upper bound)"
    print(f"  record M={M:4d}  gamma_M={mp.nstr(gam, 3):>9}  observed birth n={obs}  predicted n={pred}{tag}")
