"""Numerical check of the rigorous cycle lemmas (paper3, Section 5)
on the exact trajectories: Lemma (exact cycle identity, two-sided
bounds), theta = 0 after recovery, Lemma (older-record ratio bounds),
Proposition (freeze bound), Proposition (ratio at a birth).

Usage: python3 cycle_lemmas_check.py p [N]
"""
import sys
import mpmath as mp
from magic_numbers import run, records

ps = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 700
mp.mp.dps = 220
p = mp.mpf(ps); q = 1 - p
w, b, _ = run(ps, N)
rec = [m for m in records(w, N) if m < N]
W = w[N]


def weights(n):
    t = p ** n; out = [t]
    for j in range(1, n + 1):
        t = t * (n - j + 1) / j * q / p; out.append(t)
    return out


ok = True
for k in range(1, len(rec)):
    Mp, M = rec[k - 1], rec[k]
    Mnext = rec[k + 1] if k + 1 < len(rec) else N
    if M - Mp < 3:
        continue                        # skip consecutive-record runs
    x = [None] + [max(w[m] for m in range(j, M + 1)) for j in range(1, M + 1)]
    viol = []
    freeze_ok = None
    for n in range(M + 1, min(Mnext + 1, N)):
        om = weights(n)
        U = sum(om[:Mp + 1]); V = sum(om[M + 1:])
        s_n = sum(om[j] * (x[j] - w[n - 1]) for j in range(1, Mp + 1))
        gam_n = w[M] - w[n - 1]; gam_n1 = w[M] - w[n]
        core = q ** n * w[n - 1] - p ** n * (1 - w[n - 1]) - s_n
        lo = (U + q ** n) * gam_n; hi = (U + V) * gam_n
        diff = gam_n1 - core
        if not (lo - mp.mpf(10) ** -200 <= diff <= hi + mp.mpf(10) ** -200):
            viol.append(('cycle-bounds', n))
        # theta = 0 when w_{n-1} >= w_j on (M, n)
        if n > M + 1 and all(w[n - 1] >= w[j] for j in range(M + 1, n)):
            if abs(diff - hi) > mp.mpf(10) ** -200:
                viol.append(('theta0', n))
        # older-record ratio bounds
        if n + 1 <= N:
            om1 = weights(n + 1)
            s_n1 = sum(om1[j] * (x[j] - w[n]) for j in range(1, Mp + 1))
            d_n = w[n] - w[n - 1]; Up = U - p ** n
            rho = p * (n + 1) / (n + 1 - Mp)
            base = s_n - d_n * Up
            if not (p * base - mp.mpf(10) ** -200 <= s_n1 <= rho * base + mp.mpf(10) ** -200):
                viol.append(('older-ratio', n))
        # freeze bound with C_q q^{n-1} while U+V <= 1/2
        if U + V <= mp.mpf(1) / 2 and freeze_ok is None:
            if gam_n > 2 * q / (2 * q - 1) * q ** (n - 1):
                viol.append(('freeze', n))
        elif freeze_ok is None:
            freeze_ok = n
    # ratio proposition at the birth of M (needs complete recovery before M)
    om = weights(M); omp = weights(M + 1)
    sM = sum(om[j] * (x[j] - w[M - 1]) for j in range(1, Mp + 1))
    sM1 = sum(omp[j] * (x[j] - w[M]) for j in range(1, Mp + 1))
    rec_ok = all(w[M - 1] >= w[j] for j in range(Mp + 1, M))
    prop = (sM >= q ** M * w[M - 1] - p ** M * (1 - w[M - 1])) and (sM1 < q ** (M + 1) * w[M])
    m_marg = sM1 / (q ** (M + 1) * w[M])
    print(f"p={ps} cycle M'={Mp:4d} -> M={M:4d}: violations={viol[:3] if viol else 'none'}; "
          f"recovery-before-birth={rec_ok}; ratio-prop={prop}; s_(M+1)/s_M={mp.nstr(sM1/sM,4)} (q={mp.nstr(q,3)}); "
          f"marginality m={mp.nstr(m_marg,4)}; freeze bound holds up to n={freeze_ok}, "
          f"w_M-W={mp.nstr(w[M]-W,3)} vs C q^(n1)={mp.nstr(2*q/(2*q-1)*q**((freeze_ok or M)-1),3)}")
    ok = ok and not viol
print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
