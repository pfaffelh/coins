"""Check of Theorem (one cycle), items (iii)/(v) and hypothesis (H1),
on the exact trajectories: n_0, the ratio (w_M - W)/q^{n_0}, the proved
constant a_inf/(4e^2), and (M+1)(1-2p)/(q M').
Usage: python3 freeze_lower_check.py p
"""
import sys
import mpmath as mp
from magic_numbers import run, records
ps = sys.argv[1]; N = 700
mp.mp.dps = 220
p = mp.mpf(ps); q = 1 - p
w, b, _ = run(ps, N); W = w[N]
rec = [m for m in records(w, N) if m < N]
# a_inf = sum_k p^k prod_{j>k} (1 - p^j - q^j)
a_inf = mp.fsum(p**k * mp.fprod([1 - p**j - q**j for j in range(k+1, 400)]) for k in range(1, 400))
def cdf(n, K):
    t = p**n; s = t
    for j in range(1, K+1):
        t = t*(n-j+1)/j*q/p; s += t
    return s
print(f"p={ps}: a_inf={mp.nstr(a_inf,6)}, proved constant a_inf/(4e^2)={mp.nstr(a_inf/(4*mp.e**2),4)}, q/(1-2p)={mp.nstr(q/(1-2*p),4)}")
for k in range(1, len(rec)):
    Mp, M = rec[k-1], rec[k]
    if M - Mp < 3: continue
    x = [None] + [max(w[m] for m in range(j, M+1)) for j in range(1, M+1)]
    def sigma(n):
        t = p**n; s = mp.mpf(0)
        for j in range(1, Mp+1):
            t = t*(n-j+1)/j*q/p; s += t*(x[j]-w[n-1])
        return s/(q**n*w[n-1])
    # run end / recovery
    l1 = next(n for n in range(M+2, N) if all(w[n-1] >= w[j] for j in range(M+1, n)))
    tail = {n: cdf(n, M) for n in range(M+1, min(N, int(3*M/q)))}
    def tailsum(n): return sum(v for i, v in tail.items() if i > n)
    n0 = next(n for n in range(l1, N) if tailsum(n) <= 1 and sigma(n) <= mp.mpf(1)/2 and (p/q)**n <= a_inf/4)
    print(f"  M'={Mp:4d} M={M:4d}: (H1) (M+1)(1-2p)/(qM')={mp.nstr((M+1)*(1-2*p)/(q*Mp),4)}; recovery at n={l1}; n_0={n0} (M/q={mp.nstr(M/q,5)}); "
          f"(w_M-W)/q^n0 = {mp.nstr((w[M]-W)/q**n0,4)}  [W proxy w_700; lower bound {mp.nstr(a_inf/(4*mp.e**2),4)}]")
