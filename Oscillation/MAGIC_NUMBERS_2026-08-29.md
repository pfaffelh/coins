# The optimal value for p < 1/2: convergence, magic numbers, birth law

Working notes, 2026-08-29.  Scripts: `simulation/magic_numbers.py`
(grid scan), `simulation/magic_birth.py` (exact identity, convergence
bound, birth predictions).  All numerics in mpmath with 220–320 digits.

Notation as in Paper 1: `w_n = w_{n,p}` optimal value, `b_n` greedy (ALL),
`q = 1 − p`, `wt_j := C(n,j) p^{n−j} q^j`, `K_j^{(n)} := max_{j≤m≤n−1} w_m`.

## 1. An exact increment identity, and convergence for every p

Subtracting `w_{n−1}·1 = w_{n−1}(p^n + q^n + Σ_j wt_j)` from the Bellman
equation gives, for every n ≥ 1 and every p ∈ (0,1),

    d_n := w_n − w_{n−1}
         = p^n (1 − w_{n−1}) − q^n w_{n−1} + Σ_{j=1}^{n−1} wt_j (K_j^{(n)} − w_{n−1}).   (E)

The first and the last term are ≥ 0 (since `w ≤ 1` and `n−1 ∈ [j, n−1]`).
Checked numerically to 1e-220 for all n ≤ 700 and p ∈ {0.15, …, 0.45}.

**Theorem A (convergence).** For every p ∈ (0,1), `w_{n,p}` converges.
*Proof.* By (E), `d_n ≥ −q^n w_{n−1} ≥ −q^n`, so
`Σ_n (d_n)^− ≤ Σ q^n = q/p < ∞`.  Since `w_n ∈ [0,1]`,
`Σ_{n≤N} (d_n)^+ = w_N − w_0 + Σ_{n≤N} (d_n)^− ≤ 1 + q/p`, so
`Σ |d_n| < ∞` and `(w_n)` converges. ∎

For p > 1/2 this is Theorem 3.3 of Paper 1 (monotone).  For p < 1/2 it
is new; write `W(p) := lim w_{n,p}`.  Then `0 < a_∞(p) ≤ W(p) < 1/2`
(lower bound from strategy ONE, upper bound from Prop. 4.2(i)).

**Corollary.** Every decrease is tiny: `w_{n−1} − w_n ≤ q^n w_{n−1}`.
The sequence is *not* eventually monotone (Paper 3, Step A: if it were
eventually non-decreasing, (E) with `K_j = w_{n−1}` for j > M gives
`d_n ≤ p^n + P(Bin(n,q) ≤ M) − q^n W(p) < 0` for large n), so it has
infinitely many local extrema — but the oscillation amplitude is
summable, i.e. `w` converges.  **This contradicts the non-convergence
route of Paper 3 (Gap D(ii), `A_∞(w) ≠ 0`): in fact `A_∞(w) = 0`.**
The greedy value `b_n` genuinely oscillates (Paper 2); the optimal
player cancels that oscillation exactly.

## 2. Magic numbers: the structure of the optimal policy

Call m a *magic number* if `w_m > w_k` for all k > m (a suffix-maximum
record).  Since the Bellman equation picks `argmax_{j≤m≤n−1} w_m`, the
optimal policy is:

> with j tails, keep the **smallest magic number ≥ j**; if there is none
> in [j, n−1], play ONE (keep n−1).

By Theorem A, `W(p) = inf_m w_m` over magic numbers, and there are
infinitely many of them.  Grid scan (N = 700, 220 digits;
`relosc` = (max−min)/max over n ∈ [350, 700]):

| p    | magic numbers on [1,700]                    | dips (w_n < w_{n−1}), n ≥ 10                                  | relosc w | relosc b | w_700 − b_700 |
|------|---------------------------------------------|---------------------------------------------------------------|----------|----------|---------------|
| 0.05 | 1..700 (still decreasing)                   | all                                                           | 9.3e-9 (=b) | 9.3e-9 | 0 |
| 0.10 | 1..682                                      | 10–690                                                        | 1.3e-18 (=b) | 1.3e-18 | 9e-56 |
| 0.15 | 1..271, 313, 378, 457, 554, 673, 674        | 10–286, 314–325, 379–386, 458–465, 555–562, 674–681           | 1.8e-25  | 4.1e-23  | 1.2e-25 |
| 0.20 | 1..126, 148, 197, 265, 359, 489, 671        | 10–133, 149–160, 198–203, 266–270, 360–363, 490–494, 672–676  | 1.3e-34  | 3.3e-17  | 2.0e-18 |
| 0.25 | 1..66, 77, 78, 79, 118, 184, 292, 471       | 10–69, 78–88, 119–122, 185–188, 293–296, 472–474              | 1.9e-44  | 1.4e-13  | 5.9e-14 |
| 0.30 | 1..38, 54, 102, 201, 408                    | 10–42, 55–60, 103–105, 202–204, 409–411                       | 3.9e-52  | 5.4e-11  | 7.5e-11 |
| 0.35 | 1..20, 27, 28, 68, 187, 538                 | 10–22, 28–33, 69–71, 188–190, 539–541                         | 9.9e-61  | 3.0e-9   | 1.2e-8 |
| 0.40 | 1..11, 24, 104, 504                         | 10–14, 25–27, 105–107, 505–506                                | 5.3e-70  | 7.2e-8   | 1.3e-6 |
| 0.42 | 1..6, 9, 10, 43, 273                        | 10–13, 44–45, 274–275                                         | 1.6e-83  | 2.6e-7   | 5.8e-6 |
| 0.45 | 1..4, 15, 167                               | 16–17, 168–169                                                | 1.2e-83  | 9.3e-7   | 1.5e-4 |
| 0.47 | 1..3, 27, 657                               | 28–29, 658–659                                                | 9.2e-89  | 1.4e-6   | 2.3e-4 |
| 0.49 | 1..3, 152                                   | 153–154                                                       | 2.1e-92  | 1.0e-6   | 1.8e-4 |

Observations: (i) `w` converges super-fast while `b` oscillates —
the columns `relosc w` vs `relosc b` differ by 10–80 orders of magnitude;
(ii) for small p greedy is optimal for a long initial stretch (`w = b`
exactly up to the first isolated magic number); (iii) dips come in
short runs right after a birth; (iv) the gaps between magic numbers
grow geometrically with a p-dependent ratio.

## 3. Birth of a magic number: mechanism and criterion

Group the sum in (E) by magic numbers `m_1 < … < m_K` (records before n)
and write `γ_k(n) := w_{m_k} − w_{n−1} ≥ 0`:

    d_n = p^n(1−w_{n−1}) − q^n w_{n−1} + Σ_k P(m_{k−1} < Bin(n,q) ≤ m_k) γ_k(n)
          + [terms from non-record states above m_K; zero while w increases].

**Exact birth criterion.** `w_n < w_{n−1}` (i.e. n−1 becomes a magic
number) iff

    q^n w_{n−1} > p^n(1 − w_{n−1}) + Σ_k P(m_{k−1} < Bin(n,q) ≤ m_k) γ_k(n).

The last record `M = m_K` dominates.  Its gap obeys the recursion
(ignoring older records)

    γ_M(n+1) = P(Bin(n,q) > M) γ_M(n) + q^n w_{n−1} − p^n(1 − w_{n−1}),

which yields a two-phase picture:

* **Phase 1, M < n ≲ M/q.**  `P(Bin(n,q) > M)` is small, so
  `γ_M(n) ≈ q^n w`: the value sits just below the record,
  `w_n ≈ w_M − q^n W(p)`, and increases geometrically fast.  (The 2–3
  consecutive dips right after a birth are the transient of this phase:
  the birth is marginal, so `γ_M(M+1) = |d_{M+1}| ≪ q^{M+1}w` and one or
  two more dips are needed before `γ_M(n) ≈ q^n w` is reached.)
* **Freeze, n ≈ M/q.**  Once `P(Bin(n,q) > M) → 1` the gap stops
  shrinking: `γ_M(∞) ≈ c · q^{M/q}`.  (Observed: p = 0.45, M = 15:
  γ = 7.8e-9 vs q^{27} = 1e-7; p = 0.42, M = 43: 1.9e-19 vs q^{74} = 3e-18.)
* **Phase 2, n > M/q.**  `d_n ≈ C(n,M)(p/q)^{n−M} q^n γ_M(∞) − q^n W`,
  so the next birth happens at the first n with

        C(n, M) (p/q)^{n−M} γ_M(∞) < W(p).

  With `n = rM`, `log C(rM, M) ≈ rM·H(1/r)` and `log γ_M ≈ (M/q) log q`
  this gives the **asymptotic ratio law**

        M_{k+1}/M_k → r(p),  the root r > 1/q of
        (r − 1) log(q/p) − r H(1/r) + (1/q) log(1/q) = 0,
        H(x) = −x log x − (1−x) log(1−x).

  (The left-hand side vanishes identically at r = 1/q — the freeze
  point — and the relevant root is the larger one.)  r(p) → 1 as p → 0
  and r(p) → ∞ as p → 1/2 (there `(r−1)ε ≈ log r − log 2 + …`,
  ε = log(q/p)).

Check against the observed ratios (they increase towards r(p) from below,
as expected for a leading-order law):

| p    | r(p)  | observed M_{k+1}/M_k               |
|------|-------|------------------------------------|
| 0.15 | 1.26  | 1.15, 1.21, 1.21, 1.21, 1.21       |
| 0.20 | 1.43  | 1.17, 1.33, 1.35, 1.35, 1.36, 1.37 |
| 0.25 | 1.70  | 1.49, 1.56, 1.59, 1.61             |
| 0.30 | 2.16  | 1.42, 1.89, 1.97, 2.03             |
| 0.35 | 3.04  | 2.43, 2.75, 2.88                   |
| 0.40 | 5.16  | 4.33, 4.85                         |
| 0.42 | 6.97  | 6.35                               |
| 0.45 | 13.3  | 11.1                               |
| 0.47 | 26.5  | 24.3                               |

Extrapolated next births (upper bounds, from γ_M = w_M − w_700):
p = 0.45: n ≲ 2140; p = 0.42: n ≲ 1843.

## 4. Consequences for the p < 1/2 programme

Rigorous now: Theorem A (convergence, three lines from (E)), the dip
bound `w_{n−1} − w_n ≤ q^n`, Step A (infinitely many magic numbers), the
policy description in §2, and the exact birth criterion in §3.
Heuristic, numerically confirmed: the freeze estimate `γ_M ≈ q^{M/q}` and
the ratio law `M_{k+1}/M_k → r(p)`.

Paper 3 should be re-planned around this: replace "log-periodic
oscillation of w" (false) by "convergence + geometric magic-number
structure".  Candidate theorems: (A) as above [Lean-friendly];
(B) `W(p) = inf_m w_m` over records, `W(p) − lim inf b_n > 0` for p near
1/2 (greedy is not asymptotically optimal; gap 1.5e-4 at p = 0.45);
(C) magic numbers grow at least geometrically (`M_{k+1} ≥ M_k/q` from
phase 1 — provable from (E)?), and the ratio law as a theorem with
error terms; (D) for small p, greedy is optimal up to a threshold
`n_0(p) → ∞` (p = 0.25: n_0 = 66; p = 0.15: 271; p = 0.10: 682).

## 5. The amplitude functional for Conjecture B (added later the same day)

Forced greedy continuation z^{(M)} from a magic number M; Poissonised
functional equation Z(t) = (1−e^{−pt})Z(qt) + S(t), product formula,
log-periodic profile with Fourier coefficients
A_m(M) = (1/L)·Mellin[Π·S](2πim/L)  (see paper3.tex, §6, and
`simulation/continuation_amplitude.py`).  B ⇔ A_1(M) ≠ 0 for all magic M.

Validated: greedy mean/amplitude; direct simulation of z^{(15)} at
p=0.45 (mean 0.411292054 = A_0, peak-to-peak 3.34e-8 vs 4|A_1| = 3.24e-8,
11 direction changes on [100,3000]).

Results: A_1(M) ≠ 0 at all magic numbers tested (p=0.45: 15, 167;
p=0.25: 79, 118, 184, 292, 471), |A_1| ≫ |A_2|, stable under dps/quadrature
changes.  Scaling |A_1(M)|/q^M → ≈ 3.3e-4 (p=0.25), ≈ 6e-4 (p=0.45, two
points): the amplitude lives on the scale q^M, not γ_M.  Programme for a
proof: Ψ_p := lim A_1(M)/q^M from the self-similar limit; Ψ_p ≠ 0 by
interval arithmetic; error control for large M.

## 6. Proof architecture for Conjecture B (2026-08-30)

Future-data formula: A_1(M) = −(1/L)·Mellin[Π·T_M](2πi/L) with T_M built
from the gaps g_j = x_j^∞ − w_j and r_n^∞ for indices > M (uses
A_1(∞) = 0 from convergence).  Verified: reproduces A_1(M) exactly; the
window (M, M/q] suffices → amplitude generated in Phase 1
(`simulation/future_data_amplitude.py`).

One-dimensional model: gap recursion γ(n+1) = (1−P_n)γ(n) + qⁿW − s_n −
pⁿ(1−W), g_j = γ(j+1) − γ(∞), r_n = −g_{n−1}(1−P_n−qⁿ).  With exact s_n
it reproduces A_1(M) to 5–6 digits; with s_n = m q^{M+1} W ·
P(Bin(n,q)≤M')/P(Bin(M+1,q)≤M') the only free parameter is the
marginality m ∈ [ρ/q, 1) (`simulation/phase1_model_amplitude.py`).

Ψ_p(m) := A_1^model/q^M is affine in m; over m ∈ [0.8, 1]:
|Ψ| ∈ [3.0e-4, 4.6e-4] (p=0.25), [3.7e-4, 5.9e-4] (p=0.35),
[3.9e-4, 1.0e-3] (p=0.45), phase moves < 0.04π (`simulation/psi_of_m.py`).
No zero anywhere near the admissible range.

Remaining rigorous work (paper3 §6, items i–vi): rate of convergence
w_n → W (for A_1(∞)=0); cycle theory with o(1) relative errors (the big
one); interval-arithmetic non-vanishing; de-Poissonisation relative to
the oscillation; finitely many small M by computation.

## 7. Spacing of magic numbers (2026-08-30)

Proved: infinitely many magic numbers, M_{k+1} < m_1(M_k), m_1(M)/M → C(p)
= root of (r−1)log(q/p) = rH(1/r) (running-maximum argument).
Conjectured law: M_{k+1}/M_k → r(p), larger root of g_p; identical to
the A-recursion characterisation J(p,x_b)=I(p) (checked numerically for
all p). Conditional lower bound q/(1−2p). Data to n=2000
(`spacing_*.txt` in the session scratchpad; recompute with
magic_numbers.run at dps 360): p=0.15: 313,378,457,554,673,820,1001,
1225,1503,1848 (ratios 1.208→1.230, bound 1.214, r=1.255); p=0.2:
148,…,671,927,1287,1795 (1.331→1.395, r=1.426); p=0.3: 54,102,201,408,
845,1774 (1.889→2.099, r=2.155); p=0.4: 24,104,504 (4.33,4.85, r=5.155).
Table in paper3 §4.2.
