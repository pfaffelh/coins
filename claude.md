# Conversation log

## Session 1

### Prompt 1
> Read vibe.md.

Read [vibe.md](vibe.md). It describes a coin-game research task:
- Game from [Manuscript/20231006_p.tex](Manuscript/20231006_p.tex): start with n coins, each heads w.p. p; each round set aside ≥1 coin; win iff all coins eventually show heads.
- Two strategies: (A) set aside one head (or all if all heads); (B) set aside every head.
- Goals: (1) insights into optimal strategy for p < 1/2, (2) bounds on p where (B) is optimal, (3) closed form for (B)'s win probability.
- Reference [2406.14700v2.pdf](2406.14700v2.pdf) is a different (expected-heads) version.

### Prompt 2
> Read teh two references.

Read both PDFs/LaTeX files. Key findings:
- **Manuscript**: Lemma proves (A) optimal for p > 1/2. For p < 1/2, partial result: if w_{n-1} is the running max then w_n < w_{n-1}. Provides multinomial expression for (B). Has continuous-time variant with closed form. Note: file contains an unrelated Fleming-Viot document after line ~1018.
- **van Doorn (2406.14700v2)**: Studies the expected-heads game. Main theorem: for 1/2 ≤ p < 1, optimal strategy is (A) except possibly at j=n-1 heads, with three regimes around φ = (√5−1)/2 ≈ 0.618 and p₀ ≈ 0.5495021777642. Section 9 and Lemma 15 cover p < 1/2: optimal strategy appears "infinitely complex". Section 10 credits Peter with the non-recursive formula v_{n,p} = n − Σ (1−p)^k Π (1−p^j) for p ≥ φ, and with the all-heads-wins variant.

### Prompt 3
> Write a simulation program in python for the game as described in vibe.md. Put it in a new folder simulation.

Created [simulation/coin_game.py](simulation/coin_game.py) containing:
- `simulate_strategy_A` / `simulate_strategy_B`: Monte-Carlo simulation using `numpy`.
- `exact_A(n, p)`: recursion p_n = p^n + (1 − p^n − (1−p)^n) · p_{n−1}.
- `exact_B(n, p)`: recursion p_n = Σ C(n,k) (1−p)^k p^{n−k} p_k.
- `exact_optimal(n, p)`: Bellman recursion for w_{n,p} with max over suffix w_{j,p},…,w_{n−1,p} (j = number of tails in the round).
- `compare(...)`: prints a table of simulated vs exact values for n ∈ {2,3,5,8,15} and p ∈ {0.2, 0.35, 0.5, 0.65, 0.8}.

First run revealed a bug in `exact_optimal` (reported values below A/B). Root cause: I had misparsed the Bellman recursion's index j as "heads" instead of "tails", which inverted the suffix-max range. Fixed in a second edit by precomputing `suffix_max[j] = max(w[j],…,w[m−1])` and using `binom * p^{m−j} * (1−p)^j`.

Verified output:
- `opt ≥ max(A_exact, B_exact)` everywhere.
- For p > 0.5, `opt = A_exact`. For p < 0.5 (within tested range), `opt = B_exact`. For p = 0.5, all equal 1/2.

### Prompt 4
> Start a claude.md file describing all what I prompt and what you do.

Created this file.

### Prompt 5
> Extend the simulation program such that the reported probabilities can have arbitrary precision.

Refactored [simulation/coin_game.py](simulation/coin_game.py) so the exact
functions are polymorphic on the numeric type of `p`:
- `float` — fast ~15-digit arithmetic.
- `mpmath.mpf` — arbitrary-precision decimals; precision controlled by
  `mp.dps` or `compare(..., dps=N)`. Strings like `"0.5495021777642"` are
  parsed at full precision.
- `fractions.Fraction` — exact rational closed forms (e.g.
  `exact_optimal(10, Fraction(1,3)) = 427422486024463181450147/2153693963075557766310747`).

Monte-Carlo functions stay in `float` (their precision is bounded by
√(p(1−p)/N)). Sanity-checked that all three backends agree to 12 digits at
p = 7/23.

### Prompt 6
> Let us compare numerically (i) the optimal strategy with strategy (B) for p < 1/2. Can you do this?

Created [simulation/compare_B_vs_optimal.py](simulation/compare_B_vs_optimal.py)
computing w_{k,p} at 80-decimal precision. Noted that "(B) optimal for all
steps" ⇔ "k ↦ w_{k,p} is non-increasing". Reported table of opt − B plus a
monotonicity scan. Initial scan (n_max = 200): for p ≤ 0.1 no monotonicity
failure; for p ≥ 0.2 failure occurs at small k that shrinks rapidly as p
approaches 1/2.

### Prompt 7
> Please make a note about this finding in a new file journal.md. (Also add the date of this finding in this md file)

Created [journal.md](journal.md) dated 2026-04-16 with the observation that
(B) is not optimal for all p < 1/2 and a tentative conjecture that there
exists some p* ∈ (0.1, 0.2) below which (B) is always optimal.

### Prompt 8
> Please increase n_max for numerical simulations for p < 0.2, and add the results to the journal.

Scanned n_max = 2000 for p ∈ [0.08, 0.19] and n_max = 5000 for p ∈ {0.05, 0.06, 0.07}.
Crucial finding: the earlier "never" entries were artifacts. Even at p = 0.05
monotonicity fails at k = 3150. The failure threshold scales roughly like
n_fail(p) ~ C·p^(−2.2). Updated [journal.md](journal.md) with the revised
table and the stronger conjecture: (B) is likely *not* optimal for all n
for *any* p ∈ (0, 1/2), consistent with van Doorn's "infinitely complex"
remark.

### Prompt 9
> Let us focus on p = 0.45. Please add a table to journal saying -- given n coins and k coming up heads -- how many of the ehads should be left aside.

Created [simulation/optimal_policy_table.py](simulation/optimal_policy_table.py)
computing i*(n, k) = argmax over i ∈ {1,…,k} of w_{n−i, p}. At p = 0.45
with n ≤ 15: for n ≤ 7 the policy is pure (B); for n ≥ 8 it is strictly
bimodal (i = 1 for k ≤ n − 7, i = k for k ≥ n − 6). Added the table and
observations to [journal.md](journal.md).

### Prompt 10
> Please check this finding also at p = 0.4 and p = 0.3!

Ran the policy table at p = 0.4 (n_max = 20) and p = 0.3 (n_max = 50). In
both cases the policy remains strictly bimodal (i ∈ {1, k}) once m exceeds
the monotonicity-failure threshold (N(0.4) = 15, N(0.3) = 43). Unlike
p = 0.45 (where the best-retain count stays at 6), the best-retain count
drifts as n grows — 12 → 11 at p = 0.4, 41 → 40 → 39 → 38 at p = 0.3.
Added both tables plus a summary to [journal.md](journal.md).

### Prompt 11
> Ok, let us take this as a conjecture (please write down in the journal): For every p there is n such that: if there are k <=n coins left, strategy B is best. If k>n, strategy A is best. This is compatible with your findings so far, right?

Checked compatibility. **The conjecture as stated is not compatible.** At
p = 0.45, m = 8 the optimal flips between A and B depending on k (A for
k ∈ {2, 3}, B for k ∈ {4, …, 8}), so the optimal action at a given m is
not a single strategy. Recorded the original conjecture, the
counter-example, and a refined compatible version (for m > N(p) the
optimal is bimodal in k, always between "keep m − 1" and "keep m − k") in
[journal.md](journal.md).

### Prompt 12
> Ok, thanks. Please update claude.md on what we did.

Extended this log with prompts 5–12.

### Prompt 13
> Ok, this seems like a provable conjecture: For all p and n either w_{n, p} ≥ w_{n-1,p} or w_{n, p} ≥ w_{n+1,p}. This would imply that intermediate values are never optimal, right?

Checked. The conjecture as stated ("no strict interior local **min**") is
false at p = 0.45: direct computation of w_m gives w_5 ≈ 0.411078 >
w_6 ≈ 0.411041 < w_7 ≈ 0.411116. Also explained that the *correct*
implication "intermediate never optimal" requires "no strict interior
local **max**" (quasi-convexity), which also fails: w_14 < w_15 > w_16 at
p = 0.45. Extended the p = 0.45 policy table to n = 25, exposing that my
earlier "bimodal at p = 0.45" claim was a horizon artifact: at n = 17 the
optimal is i = 2 for every k ∈ {2, …, 12} (aiming at the strict local max
w_15). Added a correction block to [journal.md](journal.md).

### Prompt 14
> Aha, I see. For n=17, k=3 there seems to be the first instance that the optimal strategy is neither A nor B, right?

Confirmed: for p = 0.45, (n, k) = (17, 3) is the earliest pair with an
intermediate optimal (i* = 2, i.e. keep 15 coins). Rows 1–7 are pure (B),
rows 8–16 are bimodal (always i ∈ {1, k}), and row 17, column k = 3 is the
first cell with 1 < i < k.

### Prompt 15
> Could you please explor p = 0.49? Maybe the first instance of neither A nor B appears earlier...

Counter-intuitive result: p = 0.49 pushes the first intermediate much
later, not earlier. Scanned p ∈ {0.30, …, 0.49} and found the earliest
first-intermediate is **(n=11, k=3, i=2) at p ≈ 0.42** (specifically
p ∈ [≈0.4185, ≈0.4220]). There is a sharp discontinuous jump between
p = 0.4180 (first intermediate at n = 42) and p = 0.4185 (at n = 11),
signalling a reorganization of the w-sequence's local-max structure.

### Prompt 16
> Yes, please.

Added the p-sweep table and findings to [journal.md](journal.md).

### Prompt 17
> Let us take p=0.42 then. Can you prove that the optimal strategy for n=11, k=3 is neither A nor B using equations (written in a tex-file)?

Created [Manuscript/proof_intermediate_p042.tex](Manuscript/proof_intermediate_p042.tex)
with a proposition and proof: at p = 21/50, i*(11, 3) = 2 because the
three relevant continuation values satisfy w_9 > w_8 and w_9 > w_10. First
version used 18-digit decimal lower bounds L_m with the rigorous sandwich
L_m ≤ w_m < L_m + 10^{-18} and verified the gaps rigorously exceed the
rounding error (~10^{-6} ≫ 10^{-18}).

### Prompt 18
> Since you are using a fraction, 21/50, please also report all numbers as fractions, not as decimals. Only then, you can be sure that the numbers fit!

Rewrote the proof using exact reduced fractions throughout: w_1, …, w_7
inline, w_8, w_9, w_10 typeset with `\resizebox{\linewidth}{!}{...}` from
graphicx to fit the long numerators/denominators, and the two differences
w_9 − w_8 and w_9 − w_10 displayed as reduced positive rationals. The
proof's final step just notes that both have positive integer numerators
and positive integer denominators. No floating-point, no ε-arguments.

### Prompt 19
> Please update claude.md

Extended this log with prompts 13–19.

### Prompt 20
> Now try to show (prove, using abstract mathematics) for general but fixed p that there is a chance of a local maximum of n -> w_{n,p}. Summarize your findings in journal.md

Worked through what is and isn't provable. Added a dedicated section to
[journal.md](journal.md):

- Rigorous at $p\ge\tfrac12$: constant at $p=\tfrac12$; strictly
  increasing for $p>\tfrac12$ (Manuscript Lemma 0.3) — no local max.
- Perturbation at $p=\tfrac12$ with $h=p-\tfrac12$: expand
  $w_{n,p}=\tfrac12+\alpha_n h+\beta_n h^{2}+O(h^{3})$. Computed
  $\alpha_{1..4}=1,3/2,27/16,111/64$ and $\beta_{1..4}=0,0,-3/8,-25/32$
  with sympy. Proved $\alpha_n$ strictly increasing via Lemma 0.3 +
  continuity; observed $\beta_n$ strictly decreasing. Hence for
  $p<\tfrac12$, at every finite Taylor order, $w_n-w_{n-1}<0$. Local
  maximum is *non-perturbative* near $p=\tfrac12$.
- **Reduction lemma (rigorous, proved by induction on the Bellman):**
  if $(w_n)_{n\le N}$ is monotone non-increasing, then $w_n=b_n$ for
  $n\le N$. So local maxima of $w$ coincide with those of $b$ in the
  monotone regime, and it suffices to show $b$ is not monotone
  non-increasing for any candidate counter-example.
- Small-$p$ heuristic: $b_n/b_{n-1}\approx np$, predicting a peak near
  $n\approx 1/p$.
- Rigorous existence at $p=21/50$: the TeX proof at
  [Manuscript/proof\_intermediate\_p042.tex](Manuscript/proof_intermediate_p042.tex)
  exhibits the local maximum $w_9>w_8$, $w_9>w_{10}$ in exact rationals.
- Open conjecture: for every $p\in(0,\tfrac12)$, $(w_{n,p})$ has
  infinitely many strict local maxima (aligned with
  [2406.14700v2.pdf](2406.14700v2.pdf) §10).

Honest bottom line: no abstract proof of local-max existence for all
$p\in(0,\tfrac12)$; what's now rigorous is the reduction to showing
$b$ is not monotone, plus point-specific examples.

### Prompt 21
> Yes, please.

Extended this log with prompt 20.

### Prompt 22
> Please write down the Taylor expansion you just mentioned.

Made the Taylor analysis at $p=\tfrac12$ rigorous and concrete:
- Computed the B-recursion polynomials $w_1,\dots,w_4$ symbolically with
  sympy.
- Computed Taylor coefficients $\alpha_n,\beta_n,\gamma_n,\delta_n$ at
  $p=\tfrac12$ for $n$ up to 8 (strategy-B side).
- **Discovered my earlier "$\alpha_n$ strictly increasing" claim was
  wrong.** The correct picture has *separate* left/right derivatives at
  $p=\tfrac12$ because the $\max$ in the Bellman creates a corner. The
  right-side $\alpha_n^{\text{right}}$ (strategy A) is indeed strictly
  increasing; but the left-side $\alpha_n^{\text{left}}$ (numerically,
  via a recursion involving $\min_{m\in[j,n-1]}\alpha_m^{\text{left}}$)
  is valley-shaped — strictly increasing on $\{1,\dots,5\}$ then
  decreasing to a limit $\approx 1.703$.
- Consequence (Corollary in the write-up): at first order in $h<0$
  small, $(w_{n,\,1/2+h})$ has a strict local minimum at $n=5$ and *no*
  local maximum. Local maxima are non-perturbative in $h$.
- Rewrote the journal's Taylor section
  ([journal.md](journal.md) §"Taylor expansion at $p=\tfrac12$",
  starting at line 313) with left/right expansions, the recursion
  $\alpha_n^{\text{left}}=n/2^{n-1}+2^{-n}\sum_j\binom{n}{j}\min_{m\in[j,n-1]}\alpha_m^{\text{left}}$,
  numerical tables, the corollary, and an explicit correction of my
  earlier erroneous claim.

### Prompt 23
> I don't find the taylor expansion

Pointed at the exact location: journal.md line 313 heading "Taylor
expansion at $p=\tfrac12$", with an outline of what lines cover which
subsections. Suspected the user's editor had a cached view of the file.

### Prompt 24
> Please make a tex and pdf for the taylor expansion

Created [Manuscript/taylor_expansion.tex](Manuscript/taylor_expansion.tex)
and compiled to [Manuscript/taylor_expansion.pdf](Manuscript/taylor_expansion.pdf)
(3 pages). Structure: setting + regularity caveat, explicit polynomials
for small $n$, right-hand expansion with recursion for
$\alpha_n^{\text{right}}$, left-hand expansion with the min-recursion
\eqref{eq:alpha_left}, numerical table, Proposition on the valley shape
of $\alpha_n^{\text{left}}$, first-order Corollary on local min at $n=5$,
higher-order coefficient table, and a closing summary. Minor fixes during
compilation: removed `\texorpdfstring` (would require hyperref), kept one
cosmetic 9pt overfull in a proposition statement.

### Prompt 25
> THen upodate claude.md on what we did

Extended this log with prompts 22–25.

### Prompt (out-of-band)
> Can I somehow restore the current session on a different computer?

Answered separately: working directory `~/Uni/Arbeiten/coins` travels
via git; `memory/` under `~/.claude/projects/-home-pfaffelh-Uni-Arbeiten-coins/`
can be copied along (requires same project path). The live conversation
state is ephemeral, but [claude.md](claude.md) + [journal.md](journal.md)
are the reconstruction aids.

## Session 2 (2026-04-17)

### Prompt 26
> Read claude.md and journal.md to get uptodate.

Re-read both files; summarised state of work (simulation tooling,
policy-table observations, rigorous proof at $p=21/50$, Taylor
expansion, reduction lemma).

### Prompt 27
> Can you latex a condition for a local maximum?

Derived three equivalent forms. Most useful: when
$w_{n^\star,p}=\max_{m\le n^\star}w_{m,p}$ (running maximum), the
Bellman $\max$ collapses and $w_{n^\star+1,p}<w_{n^\star,p}$ reduces to
the single closed-form inequality
$w_{n^\star,p}>p^{n^\star+1}/(p^{n^\star+1}+(1-p)^{n^\star+1})$. Combined
with $w_{n^\star,p}>w_{n^\star-1,p}$ on the left.

### Prompt 28
> Start a new texfile, localmaximum.tex

Created
[Manuscript/localmaximum.tex](Manuscript/localmaximum.tex)
with a Proposition giving the running-max local-max condition, a
reduction Lemma ($w$ monotone non-increasing $\Rightarrow$ $w=b$), and
a Corollary characterising the first local maximum of $w$ in terms of
the strategy-(B) sequence $b$. Compiled to 2 pp.

### Prompt 29
> Become an expert in Bellman equations. Find the best reference in the web on how to solve these equations.

Spawned a research subagent (no web access) that produced a ranked
list, then verified URLs directly. Ranked top picks:
1. Puterman (1994), *Markov Decision Processes* — Ch. 4.7 on structural
   properties (Topkis, monotone policies).
2. Bertsekas (2017/2012), *DP and Optimal Control* Vols. I & II.
3. Stokey, Lucas & Prescott (1989), *Recursive Methods in Economic Dynamics*.
4. Chakravorty–Mahajan (2017), *Sufficient conditions for even &
   quasi-convex value functions*, arXiv:1703.10746.
5. Krishnamurthy (2023), *Interval dominance based structural results*,
   Automatica 153. Best open access: Bertsekas MIT OCW **6.231 Fall 2015**.

### Prompt 30
> Can you download refs Puterman, arxiv1703, and the last in a new folder "references"?

Created [references/](references/). Downloaded
[arxiv_1703.10746.pdf](references/arxiv_1703.10746.pdf) (8 pp.) and
[nsf_par_10425749.pdf](references/nsf_par_10425749.pdf) (Krishnamurthy,
8 pp.). Puterman is paywalled — suggested library-proxy or archive.org
loan as alternatives; did not download.

### Prompt 31
> Is this a Discounted Markov Decision Problem

No — classified the coin game as a **stochastic shortest-path (SSP)
MDP** with terminal reward: state $n$, absorbing "win" ($n=0$) and
"lose" (when $k=0$), zero per-step reward, unit terminal reward, no
discount ($\beta=1$), every policy proper since each round absorbs
with probability $\ge p^n+(1-p)^n>0$. Bellman operator is a contraction
in the SSP-weighted norm (Bertsekas–Tsitsiklis 1991), so structural
tools for discounted MDPs apply.

### Prompt 32
> Put these references into journal.md and add a date.

Added a 2026-04-17 section to [journal.md](journal.md) with: the
local-maximum condition, the SSP classification, the five ranked
references (with verified URLs and links to local copies), the MIT OCW
open-access link, and a working recommendation (Puterman §4.7 +
Krishnamurthy 2023 on our Bellman kernel).

### Prompt 33
> Corollary 3 of the new tex file is interesting. It implies that solving strategy B implies that we a tool for finding a local maximum, correct?

Confirmed. Strategy (B) has a linear recursion with **no $\max$**; its
sequence $b_{n,p}$ can be computed analytically/polynomially. By
Corollary 3 + reduction lemma, the first monotonicity failure of $b$
is automatically the first strict local maximum of the Bellman value
$w$, and the right-hand threshold inequality is essentially vacuous
for $p<\tfrac12$. This reduces the open local-max existence question
to: *is $b_{n,p}$ ever non-monotone?* — analytically a one-recursion
problem.

### Prompt 34
> First, put these insights into localmaximum.tex. Then, try the proof.

Extended [Manuscript/localmaximum.tex](Manuscript/localmaximum.tex) to 5
pp. with two new sections:

- *A tool for finding local maxima*: Prop.~3 (binomial-mixture
  identity $(1+q^n)b_{n,p}=\mathbb E[b_{J,p}]$ for $J\sim\mathrm{Bin}(n,q)$);
  Prop.~4 (polynomial structure $b_{n,p}=p^n P_n(q)$ with $P_n$ having
  non-negative integer coefficients, $\deg P_n=\binom{n}{2}$,
  $P_n(0)=1$, $P_n(1)=F_n$ Fubini, $P_n(1/2)=2^{n-1}$); Prop.~5
  (exponential generating function $G(x)=1+(e^{px}-1)G(qx)$ with
  product form). Verified Prop.~4 numerically via `exact_B` (Fubini
  1, 3, 13, 75, 541, 4683 recovered as $p\to 0$; $2^{n-1}$ at $p=1/2$).
- *Toward a general proof*: stated Conjecture 1 (for every
  $p\in(0,\tfrac12)$, $b$ is not monotone NI), derived the
  forward-difference identity
  $\Delta b_n=q\mathbb E[\Delta b_{J_{n-1}+1}]+q^{n-1}(b_{n-1}-qb_n)$,
  verified it in exact rationals at $p=21/50$ for $n=2..11$, and
  reduced Conjecture 1 to Conjecture 2 (the binomial-weighted tail of
  past decrements is eventually smaller than the explicit positive
  correction).

Proof attempt status (honest): the sum-over-$n$ of (eq:forwarddiff)
telescopes to $\sum q^{n-1}(b_{n-1}-qb_n)=qp$ and an explicit
expression $p(1+q)-L$ for the other side, giving only $L\le p$
(trivial, already known). The functional-equation approach via
$E(x)=D(x)e^{-x}$ gives a self-consistent iteration but no
contradiction — higher-order terms cancel the divergence I initially
thought I had. Conjecture 1 remains open.

### Prompt 35
> Please update claude.md and journal.md

Added prompts 26–34 to this file. Extended the 2026-04-17 section of
[journal.md](journal.md) with: the Strategy-(B)-as-tool reformulation,
three structural facts about $b_{n,p}$ (binomial-mixture identity,
polynomial $b_n=p^n P_n(q)$ with Fubini/$2^{n-1}$ evaluations, EGF), the
forward-difference identity, and the two failed proof attempts.

### Prompt 36
> Please re-latex localmaximum.

Added missing `conjecture` and `definition*` theorem environments to
the preamble; recompiled twice so cross-references resolve. Final:
[Manuscript/localmaximum.pdf](Manuscript/localmaximum.pdf), 5 pp.,
226 kB.

### Prompt 37
> Please look in the references if the Bellman equations studied in these papers have the same structure than the one we are facing here.

Read both PDFs. **Chakravorty–Mahajan (2017)**: continuous state on
$\mathbb R$ or $[-a,a]$, symmetric/even costs & transitions, fixed
action set; uses a "folding" trick to reduce to monotone-policy
machinery and deduce quasi-convexity. Our setup has no reflection
symmetry and we want the *opposite* conclusion — not portable.
**Krishnamurthy (2023)**: finite state, discounted, fixed action set;
generalises Topkis via interval-dominance to conclude $\mu^\ast(x)\uparrow x$.
Our action set is state-and-shock-dependent and the problem is SSP,
so the framework doesn't fit as stated. Diagnostic check: our binomial
kernel violates Krishnamurthy's (A4) and (A6)/(A7) — the $\max$ over
the suffix $\{j,\dots,n-1\}$ is the structural culprit. Net message:
the references are **diagnostic** (they explain why the standard
toolbox doesn't apply), consistent with the empirically observed
local maxima.

### Prompt 38
> yes

Wrote up the comparison as a new subsection
"Compatibility of our Bellman with the two reference papers" in
[journal.md](journal.md), including the three structural mismatches,
the diagnostic assumption-by-assumption table, and the conclusion that
the references rule out the standard structural toolbox and point us
back to the Fubini/$P_n(q)$ small-$p$ approach.

### Prompt 39
> Great insights. Please update journal.md

The comparison subsection was already written up in Prompt 38. Added
prompts 35–39 to this log so the meta-record stays in sync.


### Prompt 40
> Actually, (4) in Prop 1 has bad notation: w_{n^*,p} and w_{m,p} are the same notation if m = n^*.

Fixed: replaced the "running-max" hypothesis from
$w_{n^\star,p}=\max_{1\le m\le n^\star}w_{m,p}$ to
$w_{n^\star,p}\ge w_{k,p}$ for every $k\in\{1,\dots,n^\star-1\}$
(fresh index letter, excludes the trivial $k=n^\star$).

### Prompt 41
> The conditions of Prop 1 and Cor 3 are completely different. … the proof of Cor 3 is incorrect.

Confirmed gap. Under Cor 3's setup (first $b$-uptick at $n^\star$),
$(w_m)_{m=1}^{n^\star-1}$ is monotone non-increasing so $w_1$ is the
prefix max — $w_{n^\star}$ does not dominate $w_1$. Numerical witness
at $p=0.45$: $b_7\approx 0.411\ll w_1=0.45$. Rewrote Cor 3 to claim
only first non-monotonicity ($w_{n^\star}>w_{n^\star-1}$). Added a new
Cor 4 *"Non-monotonicity implies a local maximum"* proving that if $w$
is non-monotone, there is $N\ge 2$ that is a strict local max — via
the Manuscript Lemma (running max $\Rightarrow$ strict decrease) +
boundedness of $w$.

### Prompt 42
> Please check Lemma 0.3 in the manuscript file.

Located at [Manuscript/20231006_p.tex:675-699](Manuscript/20231006_p.tex#L675-L699),
unnumbered, statement: "Let $p<1/2$. If $w_{n-1,p}=\max_{k=1,\dots,n-1}w_{k,p}$,
then $w_{n,p}<w_{n-1,p}$." Verified the proof line by line — correct.
Used to upgrade Lemma 4 (lem:nogrowth) in localmaximum.tex with the
explicit $p<\tfrac12$ hypothesis (without which the lemma is false:
for $p>\tfrac12$, $w$ is strictly increasing).

### Prompt 43
> In the proof of Corollary 5, I do not understand why N=1 is not possible.

Real gap caught. Case B of the proof assumed $N\ge 2$ but $N=1$
(running-max set $\mathcal S=\{1\}$) is genuinely possible: at
$p=0.45$, $w_1=0.45$ is the overall sup of the sequence. Worked out a
counter-example sequence pattern (decreasing then monotone up to a
limit $L<w_1$ — has no strict local max). Replaced Cor 5 with a
weaker, correct version: if $w_n$ is a running max AND $w_n>w_{n-1}$,
then $n$ is a strict local max. Added a "Gap in earlier version"
remark documenting the false claim.

### Prompt 44
> Please analyze numerically the values of N different values of p.

Computed for $p\in\{0.1,0.2,\dots,0.49\}$: in EVERY case, the sup of
$(w_{n,p})$ over $n\le n_{\max}$ equals $w_{1,p}=p$ — no $n\ge 2$ ever
matches. So the gap is not edge-case but the generic regime.

### Prompt 45
> Maybe it is easy to show that w_{n,p} < p for n > 1?

Yes. Direct induction: $w_{n,p}\le p-pq(q^{n-1}-p^{n-1})<p$ for
$n\ge 2$, $p<\tfrac12$. Base $n=2$: $p-w_{2,p}=pq(q-p)$. Inductive
step uses $j=1$ contribution exact ($=p$) and $j\ge 2$ strictly $<p$
by IH. Added as Proposition (was Prop~6, now Prop~3 after deletions);
also added Corollary 7 stating that the running-max set is exactly
$\{1\}$ and hence the Manuscript Lemma is silent on $n\ge 2$.

### Prompt 46
> Can you show w_{n,p} < w_{2,p} for n > 2 as well?

Yes, same induction template with $w_2$ in place of $p$. Reduces to
$\bar w_n-w_2=-p^2q^2 G_n(p)$ with $G_n$ explicit, then a clean
recursion $G_n - qG_{n-1}=p^{n-3}(1-2p)[3p+n(q-p)]$ (sympy-verified)
propagates positivity of $G_n$ from base $G_3=3q(1-2p)>0$. Added as
Proposition (was Prop~8, now Prop~4 after deletions).

### Prompt 47
> So, some results in localmaximum are false, or never bite. Please delete them.

Removed: Form 2 of the local-max condition (a generic restatement),
Form 3 + Prop 1 (running-max condition, never satisfied for
$p<\tfrac12$ by Prop 3), the entire "Existence of a local maximum"
subsection (Lemma 4 = Manuscript Lemma + Cor 5 = "From a running max
to a local max", both never bite), Cor 7 (cor:tool-vacuous, references
deleted Cor 5), and the two end-of-section remarks. Bibliography
entry `coinmanuscript` removed (its only citer was Lemma 4). Tex now
5 pp. and contains only valid, biting results.

### Prompt 48
> Please compute numerically the first local minima, depending on p < 1/2.

Computed for 15 values of $p\in[0.05, 0.495]$: $N$ stabilises at 5 as
$p\to\tfrac12$ (matching Taylor analysis prediction); $N\sim p^{-2.2}$
as $p\to 0$. The local-min value $w_N$ is dramatically smaller than
$w_1=p$ for small $p$ (7 orders of magnitude at $p=0.05$).

### Prompt 49
> Can you generalize the proof of Prop 4 from 2 to 3?

Partial result: $w_n<w_3$ for $n\ge 4$, $p<\tfrac12$ holds
empirically, and the same proof template gives
$\bar w_n-w_3=p^3q^2(2p-1)R_n(p)$ with $R_n$ an explicit polynomial.
$R_n>0$ on $(0,\tfrac12)$ for $n\le 12$, but $R_n$ acquires a single
root $p_n\in(0,\tfrac12)$ that drifts toward $\tfrac12$ for $n\ge 13$.
So the simple template gives the result for $n\in\{4,\dots,12\}$ only;
$n\ge 13$ near $p=\tfrac12$ requires a tighter argument. Added as
Prop~9 of localmaximum.tex with explicit breakdown remark.

### Prompt 50
> yes, and update journal and claude.

Added new section "2026-04-18 — First local minima of $w_{n,p}$ vs $p$,
and the $w_n<w_3$ partial generalization" to journal.md with the LMin
table, three observations, and the partial $w_n<w_3$ result with
breakdown analysis. Appended prompts 40–50 to this log.

### Prompt 51
> Which approach would you follow next?

Recommended three directions: (1) chain $w_n<w_k$ bounds for higher $k$
(incremental), (2) small-$p$ rigorous version of the local-max
conjecture (closer to the main goal), (3) stronger local-max-decrease
lemma (high risk). Suggested starting with (1).

### Prompt 52
> Make a new tex-file. Prove that for p=1/2, the strategy does not matter since w_{n,1/2} = 1/2 for all n.

Created [Manuscript/halfp.tex](Manuscript/halfp.tex) (initially 2 pp.,
later grew to 6 pp.) with **Proposition 1**: $w_{n,1/2}=\tfrac12$ for
every $n\ge 1$, and any policy that takes the immediate win at $k=n$
heads achieves $\tfrac12$. Proof by induction using the binomial
identity $\sum_{j=1}^{n-1}\binom{n}{j}/2^n=1-2^{1-n}$. Sharpness
remarks: refusing the all-heads win gives $\tfrac12-2^{-(n+1)}<\tfrac12$;
$w_{n,p}=\tfrac12$ is special to $p=\tfrac12$.

### Prompt 53
> define \Delta_{n,p} := 1/2 - w_{n,p}. Obtain a recursion for \Delta_{n,p}

Derived
$\Delta_{n,p}=(q^n-p^n)/2+\sum_{j=1}^{n-1}\binom{n}{j}p^{n-j}q^j\,\min_{j\le m\le n-1}\Delta_{m,p}$
($\max$ on $w_m$ flips to $\min$ on $\Delta_m$). Added as Proposition 2
of halfp.tex with sanity checks (empty-sum at $n=1$, $\delta=0$ case)
and a sign corollary ($\Delta_n>0$ for $p<\tfrac12$, $<0$ for
$p>\tfrac12$, by induction).

### Prompt 54
> Ok. Now let us assume that p is close to 1/2. Let \delta := 1/2 - p (for p < 1/2), and exchange p with \delta in the recursion. Several things must cancel since n -> w_{n,1/2} is constant. Right?

Confirmed. Three pieces each $O(\delta)$:
constant term $(q^n-p^n)/2=n\delta/2^{n-1}+O(\delta^3)$;
binomial weights $\binom{n}{j}/2^n+O(\delta)$;
$\min_{j\le m\le n-1}\Delta_{m,p}=O(\delta)$ (by induction).
Writing $\Delta_{n,p}=c_n\delta+O(\delta^2)$ and matching first-order
yields the clean recursion
$c_n=n/2^{n-1}+(1/2^n)\sum_{j=1}^{n-1}\binom{n}{j}\min_{j\le m\le n-1}c_m$,
$c_1=1$ — exactly the $\alpha_n^{\text{left}}$ recursion from the
journal's earlier Taylor analysis. Numerics: $c_5=3555/2048$ peak,
$c_n\downarrow L\approx 1.7035$. First-order corollary: $w$ has a strict
local *minimum* at $n=5$ near $p=\tfrac12$, no local max.

### Prompt 55
> yes [add to halfp.tex]

Added section "Expansion near $p=\tfrac12$" with three-piece breakdown,
**Proposition 4** (recursion for $c_n$), corollary on the first-order
shape of $w_{n,p}$, and remark on non-perturbative origin of local
maxima.

### Prompt 56
> can you show the limit for c_n analytically?

Derived **Lemma 5** (asymptotic collapse of $\min$ for $n\ge 7$),
**Proposition 6** (linear recursion $c_n=A_n+(1-B_n)c_{n-1}$ with
$A_n,B_n$ explicit), and **Theorem 8** (existence of the limit and
explicit formula
$L=c_{n_0-1}\prod(1-B_m)+\sum A_k\prod_{m>k}(1-B_m)$).
High-precision value: $L=1.70347176087173673645\ldots$. No elementary
closed form (comparable to $\alpha_\infty^{\text{right}}\approx 2.607$).

### Prompt 57
> Where is the simplified recursion?

Located it in [halfp.tex](Manuscript/halfp.tex): Proposition 6 on
page 4, with the supporting Lemma 5 (collapse of $\min$) just above.
The threshold $n_0=7$ comes from $c_6=113337/65536\approx 1.7294<c_4=111/64$.

### Prompt 58
> Lemma 6 has no proof, only some numerical arguments. Can you prove Lemma 6, e.g. using induction?

Replaced the numerical justification with an actual proof. The lemma
splits into (L1) $c_m\ge\tfrac{27}{16}$ for $m\ge 4$, and (L2)
$(c_n)_{n\ge 5}$ strictly decreasing.
- (L1) for $m\in\{4,\dots,12\}$: direct algebraic identity
  $c_m\ge\tfrac{27}{16}-\tfrac{3(m^2-15m+36)}{32\cdot 2^m}$, with the
  bracket non-positive on $\{3,\dots,12\}$ (roots at $3$ and $12$).
- (L1) for $m\ge 13$: deficit recursion
  $\varepsilon_n=(1-B_n)\varepsilon_{n-1}+(A_n-\tfrac{27}{16}B_n)$,
  positivity propagates from $\varepsilon_{12}>\tfrac{1}{50}$ since
  the cumulative deficit is $<\tfrac{1}{160}$ ($\sum k^2/2^k=6$ minus
  finite partial sum).
- (L2): combines (L1) with the same algebraic identity.
Also fixed circular dependency: derived linear-recursion form within
the lemma's proof (instead of citing Prop 6 which depends on the
lemma).

### Prompt 59
> Please update claude.md and journal.md

Added "2026-04-18 — The fair-coin case $p=\tfrac12$ and the
$\delta$-expansion" section to journal.md covering all of halfp.tex's
content (main theorem at $p=\tfrac12$, $\Delta$-recursion, $\delta$-
expansion with $c_n$ recursion, asymptotic collapse lemma + proof
sketch, linear recursion + limit formula + numerical value
$L=1.70347176087\ldots$, algebraic identity at $n=12$ threshold).
Appended prompts 51-59 to this log.

### Prompt 60
> For the proof of Lemma 6, please run numerical simulations in order to see if all steps in the proof are supported by a simulation.

Wrote a comprehensive numerical verifier covering all 11 numbered steps
of the Lemma 5 proof in halfp.tex. **Found one real bug**: I claimed
$\varepsilon_{12} = c_{12} - 27/16 > 1/50 = 0.02$, but actually
$\varepsilon_{12} \approx 0.01861 < 1/50$. Also several other bounds in
the proof were loose (and one — $\sum_{m\ge 13}B_m = 15554/131072$ —
was a fabricated rational; the correct value is $243/2048$).

Corrected the proof in halfp.tex with tighter, exactly-verified
bounds:
- $\varepsilon_{12} > 1/60$ (verified, $0.01861 > 0.01667$).
- $\sum_{m\ge 13}B_m = 243/2048$ via closed form $\sum_{m\ge 0}B_m=10$
  (from $\sum m^k/2^m$ identities) minus $\sum_{m=0}^{12}B_m = 20237/2048$.
- $243/2048 < 1/8$, so by Weierstrass $\prod_{m\ge 13}(1-B_m) > 7/8$.
- First term: $(1/60)(7/8) = 7/480$.
- Cumulative deficit: $\sum_{k\ge 13} 3(k^2-15k+36)/(32 \cdot 2^k) \le
  (3/32)(99/2048) = 297/65536 < 1/200$, where $\sum_{k\ge 13}k^2/2^k = 99/2048$
  via $\sum_{k\ge 0}k^2/2^k=6$ minus $\sum_{k=0}^{12} k^2/2^k = 12189/2048$.
- Final: $\varepsilon_n > 7/480 - 1/200 = 23/2400 > 0$ for all $n\ge 13$.

All verified numerically; recompiled to 6 pp.

### Prompt 61
> Update claude.md and journal.md

Appended this entry to claude.md; added "2026-04-18 — Numerical
verification + correction of the Lemma 5 proof" subsection to
journal.md.

## Session 3 (2026-04-19)

### Prompt 62
> Read claude.md and journal.md to get uptodate.

Re-read both files; confirmed state of work.

### Prompt 63
> What would you need in order to run without interruption on the Lean project.

Checked prerequisites: Lean 4.29.1, Lake 5.0.0, elan all installed.
Listed requirements: Mathlib download (network), Bellman definition
sign-off, file-write and `lake build` permissions.

### Prompt 64
> The Bellman def from journal.md is fine.

Started the Lean formalization. Created `CoinsLean/` project via
`lake new CoinsLean math`, fetched Mathlib cache (8232 pre-built oleans).

Key design decisions encountered during implementation:
- **Termination**: Lean can't extract finset membership proofs for
  `decreasing_by` when using `∑ j ∈ Ico 1 (n+1), ... b p j ...`.
  Solution: use `(Ico 1 (n+1)).attach` to carry membership proofs,
  then prove `Finset.sum_attach` to convert back to the clean form.
- **Definition**: defined `b p n` (strategy B, no `max`) rather than
  the full Bellman `w p n` (which has `max` and would need `suffMax`).
  At $p=1/2$ these coincide, so this suffices for the first theorem.
- **Unfolding**: auto-generated `b.eq_1`/`b.eq_2` exist but use
  `attach`; proved clean `b_zero`/`b_succ` lemmas using `sum_attach`.

Created two files:
- [CoinsLean/CoinsLean/Bellman.lean](CoinsLean/CoinsLean/Bellman.lean):
  definition of `b p n` with `b_zero` and `b_succ` unfolding lemmas.
- [CoinsLean/CoinsLean/HalfP.lean](CoinsLean/CoinsLean/HalfP.lean):
  three results:
  1. `choose_sum_Ico`: $\sum_{j \in \text{Ico}\,1\,(n+1)} \binom{n+1}{j} = 2^{n+1} - 2$.
  2. `half_pow_arith`: $(1/2)^{n+1} + (2^{n+1}-2)(1/2)^{n+2} = 1/2$.
  3. **`b_half`**: $b(1/2, n) = 1/2$ for every $n \ge 1$.

Proof of `b_half` uses strong induction (`Nat.strongRecOn`), replaces
`b(1/2, j) = 1/2` by IH, collapses $(1/2)^{n+1-j}(1/2)^j = (1/2)^{n+1}$
via `pow_add`, factors the sum via `sum_mul`, applies
`choose_sum_Ico` and `half_pow_arith`.

The arithmetic lemma `half_pow_arith` required: (a) `nlinarith` with
the nonlinear fact $2^{n+1} \cdot (1/2)^{n+1} = 1$ (proved via
`inv_pow` + `mul_inv_cancel₀`), and (b) `linarith` for the final
cancellation.

**`lake build` passes with zero `sorry` and zero warnings.**

### Prompt 65
> How can you be run in nonstopmode, as much as possible?

Explained three options: `--dangerously-skip-permissions`,
allowlisting specific tools in `settings.json`, and headless mode
with `claude -p "..." --dangerously-skip-permissions`.

### Prompt 66
> Update journal.md and claude.md

Extended both files with Session 3 content.

### Prompt 67
> Let us make a manuscript file. Set up a latex file which should follow the outline of a scientific paper. ...

Created [Manuscript/manuscript.tex](Manuscript/manuscript.tex) (compiles
to 7 pp.\ PDF). Structure:

- **§1 Introduction.** The game, MDP/Bellman framework (SSP
  classification), strategies \textsc{One} and \textsc{All} (renamed
  from A/B), recursions \eqref{eq:a-rec} and \eqref{eq:b-rec}.
- **§2 The fair coin ($p=1/2$).** Theorem: $w_{n,1/2}=1/2$ for all
  $n$; any policy with $i_\pi(n,n)=n$ achieves $1/2$.
- **§3 Above the fair coin ($p>1/2$).** Theorem: \textsc{One} is
  optimal, $n\mapsto w_{n,p}$ strictly increasing. Proved by
  induction using $w_{n-1,p}<p^n/(p^n+q^n)$.
- **§4 Below the fair coin ($p<1/2$).** Deficit $\Delta_{n,p}$,
  its recursion (Proposition), first-order expansion
  $\Delta=c_n\delta+O(\delta^2)$ (Proposition), collapse of the
  $\min$ for $n\ge 7$ (Lemma, with sub-lemmas on lower bound
  $c_m\ge 27/16$ and monotone decrease for $n\ge 5$), linear
  recursion $c_n=A_n+(1-B_n)c_{n-1}$ (Proposition), limit theorem
  $L\approx 1.7035$ (Theorem), shape corollary (local min at $n=5$,
  no local max at first order).

References: van Doorn 2024 (arXiv:2406.14700), Bertsekas 2017,
Bertsekas–Tsitsiklis 1991, Dubins–Savage 1965, Puterman 1994,
Stokey–Lucas–Prescott 1989.

### Prompt 68
> Update journal.md and claude.md

Extended both files with Prompt 67.

### Prompt 69
> Make this folder a git repo, and push it to github as a public repo.

After clarifying questions about visibility, what to track, and how
to handle the inner Lean project: created `.gitignore` excluding
`CoinsLean/.lake/` (7 GB of Lean build + mathlib), `__pycache__`,
LaTeX intermediates (`*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`,
`*.synctex.gz`, `*.out`), `*~` backups, and
`.claude/settings.local.json`. Final tracked size: 3.8 MB across
46 files (largest 396 KB).

Removed the inner `CoinsLean/.git` (an empty `lake new` artifact
with no commits or remote) so `CoinsLean/` is treated as a normal
subfolder. Mathlib remains a Lake-managed dependency (pinned via
`lake-manifest.json`); `lake update mathlib` works without git
submodules — submodules don't help with Lake.

`git init -b main`, initial commit, then
`gh repo create coins --public --source=. --push` published the
repo at https://github.com/pfaffelh/coins.

### Prompt 70
> Now, we have the next big thing, formalization of all results in
> Manuskript/manuscript.pdf. Please do as much of the results as you
> can do. The p = 1/2 case is already formalized, as far as I remember.

Inventoried the existing formalization
(`HalfP.lean`: only `b(1/2,n)=1/2`) and the manuscript scope, then
extended `CoinsLean/` substantially:

- **Strategies.lean** — `a p n` (strategy ONE), with `a_succ`,
  `a_one`, and `a_half` (`a(1/2, n) = 1/2` for `n ≥ 1`).
- **Optimal.lean** — `w p n` defined via the Bellman equation with
  a `Finset.sup'` over `(Ico j (n+1)).attach`. Total `suffMax p j n`
  helper to enable a non-attach `w_succ`. Proved `w(1/2, n) = 1/2`
  by strong recursion (Theorem 2.1 step 1).
- **Above.lean** — Theorem 3.1 for `p > 1/2`: joint strong induction
  on `n ≥ 2` proving (i) strict monotonicity, (ii) the sharp bound
  `w(p, n-1)·(p^n + q^n) < p^n`, (iii) `w = a`. Required:
  - `binom_sum_middle`: `∑_{j=1}^{n-1} C(n,j) p^{n-j} q^j = 1 − p^n − (1−p)^n`
    (via `add_pow` with `x = 1−p`, `y = p` to dodge reindexing).
  - `suffMax_eq_top` under monotonicity.
  - `chain_mono`: pointwise step → chained inequality.
  - `w_rec_of_mono`: collapses Bellman to the strategy-ONE recursion
    when `w` is monotone on `[1, n+1]`.
  - The (ii) inductive step uses the algebraic identity
    `(LHS − pA) · (A+B) = AB(q−p) + (1−A−B)·(C+D)·(w·(A+B) − A)`
    with both terms on the RHS non-positive.
- **Perturbation.lean** — `deficit p n := 1/2 − w p n`,
  `deficit_zero`, `deficit_half`, `deficit_neg_of_above` (sign for
  `p > 1/2`). Defined `c : ℕ → ℝ` via the manuscript's recursion
  with `(Ico j (n+2)).attach.inf'`.
- Wired everything into `CoinsLean.lean` and verified with
  `lake build` (8256 jobs, green).

Pushed as commit `3ecf718`.

### Prompt 71
> Let us work on §4 now. Start with the simplest task, please.

Picked **Example 4.5, first value: `c_2 = 3/2`**. Refactored
`Perturbation.lean`:
- Added `suffMin j n` (total suffix-min, `0` when `j ≥ n`).
- `suffMin_singleton: suffMin n (n+1) = c n` via `Finset.inf'_le`
  + `Finset.le_inf'` on the singleton attach.
- `c_succ`: plain-sum form of the c-recursion at `n+2`,
  derived from the original definition by `Finset.sum_attach`.
- `c_two : c 2 = 3/2` via `c_succ` + singleton reduction.

Pushed as commit `84ca569`.

### Prompt 72
> Can you proceed with the next task?

`c_3 = 27/16`:
- Added `suffMin_pair: suffMin n (n+2) = min (c n) (c (n+1))`.
- `c_three: c 3 = 27/16` by reducing `Ico 1 3 = {1,2}`,
  using `suffMin_pair` for `j=1` and `suffMin_singleton` for `j=2`.

Pushed as commit `12d8aac`.

### Prompt 73
> continue

`c_4 = 111/64`:
- Added the general `suffMin_split: suffMin n m = min (c n) (suffMin (n+1) m)`
  (for `n+1 < m`), reducing any `suffMin` to a chain of mins.
- `c_four`: chain `suffMin_split` + `suffMin_pair` + `suffMin_singleton`.
- Hit `decide` failure on `(Nat.choose 4 2 : ℝ) = 6` (decide can't
  reduce real-valued Nat.cast); worked around with
  `exact_mod_cast (by decide : Nat.choose 4 2 = 6)`.

Pushed as commit `f62c628`.

### Prompt 74
> do c_5

`c_5 = 3555/2048`: same pattern, 4 sum terms, four `suffMin`
reductions. Concrete arithmetic via `norm_num` after substituting
`(Nat.choose 5 2 : ℝ) = 10` and `(Nat.choose 5 3 : ℝ) = 10`.

Pushed as commit `a66b14e`. All four numerical values from
Example 4.5 are now verified.

### Prompt 75
> lemma 4.7

Flagged the manuscript's circular dependency for the full Lemma 4.7
(uses linear recursion → collapse → 4.7). Did the trivial part:
`c_four_ge`, `c_five_ge` (`c_n ≥ 27/16` from the explicit values).

Pushed as commit `b87bc08`.

### Prompt 76
> Formalize the inductive bound for n ∈ {4,...,12} — needs suffMin_eq_c_k

Strong-induction proof `c_ge_27_16_le_12: ∀ n, 4 ≤ n → n ≤ 12 → c n ≥ 27/16`.
Built up:
- `suffMin_ge_const`: lift a pointwise lower bound on `c` to a
  lower bound on `suffMin`.
- `c_ge_one_of_ih`, `c_ge_three_halves_of_ih`,
  `c_ge_27_16_of_ih`: pointwise lower bounds on `c m` under the IH
  `c k ≥ 27/16` for `4 ≤ k < N`.
- `choose_sum_3_to_pred`: `∑_{j=3}^{n-1} C(n,j) = 2^n − 2 − n − C(n,2)`.
- `c_ind_step`: combines all of the above with the polynomial
  inequality `7n − 18 − C(n,2) ≥ 0` (i.e. `n² − 15n + 36 ≤ 0`),
  decided by `interval_cases n' <;> decide` after casting to ℕ.
- The final algebra clears `Q*Qp` denominators via `field_simp`
  inside a `show … from …` rewrite.

Pushed as commit `0e02311`.

### Prompt 77
> please keep going.

Did the next foundational pieces in §4:

- `deficit_succ` (Proposition 4.2 recursion) using `binom_sum_middle`
  (made non-private in Above.lean).
- `deficit_pos_of_below`: `Δ_{n,p} > 0` for `0 < p < 1/2`, by
  strong induction with the hypothesis "every `w(p, m)` on the
  suffix is `< 1/2`" → `1/2 − suffMax ≥ 0`.

Pushed as commits `d65293f`, `7bb7382`.

### Prompt 78
> please keep going.

Cleaned up the deficit recursion to match the manuscript exactly:

- `suffMinDelta p j n` (suffix-min of the deficit).
- `suffMinDelta_eq: suffMinDelta = 1/2 − suffMax` via
  `Finset.exists_mem_eq_sup'` (one direction) + `Finset.le_inf'`
  (other direction).
- `deficit_succ'`: restated recursion with `suffMinDelta` factor.
- Added `c_pos: c n > 0 for n ≥ 1` and `c_ge_one: c n ≥ 1 for n ≥ 1`
  (the latter via `field_simp` + `le_div_iff₀`).
- `c_one_lt_two`, `c_two_lt_three`, `c_three_lt_four`, `c_four_lt_five`
  — strict monotonicity on `{1,…,5}` (Example 4.5).

Pushed as commits `f922fd5`, `751152f`, `d359645`, `6603e60`.

### Prompt 79
> In the manuscipt, I think i_π(n,n) in Thm 2.1 was not introduced. In
> the last sentence of Section 1.3, note that the same applies to the
> recursion a.

Two manuscript fixes:

- §1.2: added a proper definition of `i_π(n, k) ∈ {1, …, k}` and
  `v_n^π` so the symbol used in Theorem 2.1 / Remark 2.2 is
  introduced.
- §1.3: linearity comment now mentions BOTH `a` and `b`
  (was only mentioning `b`).

PDF rebuilt cleanly.

### Prompt 80
> For the formalization, I want you to write out the lemmas you will
> have to prove, and say by sorry for their proofs.

Added a "Remaining §4 lemmas (TODO)" section at the end of
`Perturbation.lean` with `sorry` stubs for:

- `A_lin n`, `B_lin n` — the constants from Prop 4.9 (eq:AB).
- `c_ge_27_16_full` (Lemma 4.7 in full).
- `c_strict_anti_from_five` (Lemma 4.8).
- `suffMin_collapse_low / _high` (Lemma 4.6, two cases).
- `c_linear_rec` (Prop 4.9).
- `c_limit_exists` and `c_limit_formula` (Theorem 4.10, existence
  and explicit form via products and series).
- `deficit_first_order` (Proposition 4.4).
- `w_gap_first_order`, `w_local_min_at_five`,
  `no_first_order_local_max` (Corollary 4.11 i, ii, iii).

Each statement uses `sorry`; the file builds with 12 `sorry`
warnings. A section comment sketches the dependency structure
(circularly tangled at first glance — clarified next).

Pushed combined with the manuscript fixes as commit `287b119`.

### Prompt 81
> Wait. As you say above, is the complete argument circular? This
> way, will not be able to formalize it...

Re-examined and clarified: the dependencies between Lemmas 4.6,
4.7, 4.8 and Prop 4.9 form a circle **at the lemma level** but the
manuscript's actual proof is a **simultaneous strong induction on
n**. At each step `n ≥ 7`, the IH for indices `< n` provides
exactly what's needed for all four claims at level `n`:

```
collapse@n  ← IH 4.7 + 4.8     (only c values at < n)
linear@n    ← collapse@n
4.7@n       ← linear@n + algebraic identity
4.8@n       ← linear@n + IH 4.7
```

Base cases `n ∈ {4, 5, 6}` come from explicit values of
`c_4, c_5, c_6` (need `c_6 = 113337/65536`). So formalization is
possible — just needs the joint-induction structure.

### Prompt 82
> Great insight. Please first cean this in the manuscript, such that
> the stories of manuscript and formalization will eventually fit
> together.

Restructured manuscript §4.3-4.4 to match the joint induction:

- Merged §4.3 (Collapse) and §4.4 (Linear recursion and the limit)
  into one §4.3 "Collapse, lower bound, and linear recursion".
- All four results stated upfront, then a single "Joint proof"
  proceeds by induction on `n` establishing claims (a)-(d) at each
  step.
- Algebraic identity (eq:alg-id) moved into the statement of
  Prop 4.9 so it's available without circular reference.
- Added `c_6 = 113337/65536` to Example 4.5 with the inequalities
  `c_4 > c_6` and `c_5 > c_6` flagged as base cases.
- New §4.4 "The limit" houses Theorem 4.10.

PDF rebuilt cleanly (8 pages). Pushed as commit `db6613c`.

### Prompt 83
> Is the formalization in line with the manuscript now, or do you
> have to adapt it?

Identified three mismatches that need adapting:

1. The Lean scaffold has four independent `sorry` stubs, but the
   manuscript proves them jointly — should be one master
   `joint_step` theorem with four corollaries.
2. The algebraic identity `eq:alg-id` is now in the statement of
   Prop 4.9; the formalization doesn't have it as a separate lemma.
3. `c_6 = 113337/65536` appears in the manuscript's Example 4.5 as
   a base case; the Lean side hasn't computed it.

Asked the user for permission to bring the formalization in line.

### Prompt 84
> Please update claude.md and journal.md

Extended both files with Prompts 69-84 (this update).

### Prompt 85
> Now, please bring the formalization in line, as you suggested above.

Three changes to align `Perturbation.lean` with the restructured
manuscript §4.3:

1. **Compute `c_6 = 113337/65536`** explicitly. Same chained
   `suffMin_split` + `suffMin_pair` + `suffMin_singleton` pattern as
   `c_5`, with explicit `Nat.choose 6 j` cast lemmas for j = 2, 3, 4.
2. **Prove `alg_id`** (Prop 4.9 algebraic identity):
   `A_n − (27/16) · B_n = −3·(n²−15n+36) / (32·2^n)`. Key insight:
   the `c_3` coefficient cancels exactly between `A` and `(27/16)·B`,
   so only `Nat.cast_choose_two` is needed; close with `field_simp +
   ring` after rewriting `2^(n−1) = 2^n / 2`.
3. **Replace four scattered §4.3 stubs with one `joint_step`** (still
   `sorry`-stubbed) plus four one-line corollaries:
   - `c_ge_27_16_full := joint_step.1`
   - `c_strict_anti_from_five := joint_step.2.1` (with index shift)
   - `c_linear_rec := joint_step.2.2.1`
   - `suffMin_collapse_low/high := joint_step.2.2.2 …`

Sorry count: 12 → 7 (four §4.3 stubs absorbed into joint_step).
Pushed as commit `a8546e8`.

Side question from user: *Does the formalization include the
transition from `w` to `Δ` to `c`?* Answer: `w → Δ` yes (via
`deficit_succ`/`deficit_succ'` derived from `w_succ`); `Δ → c` no
(only as a `sorry` stub: `deficit_first_order`).

### Prompt 86
> Yes, if that fills the gap to Δ!

Built out the `Δ → c` bridge (Prop 4.4):

- **Base case proved**: `deficit_first_order_one : ∀ δ,
  deficit (1/2 − δ) 1 = c 1 · δ` — exact identity (no error term),
  since `w(1/2−δ, 1) = 1/2−δ` and `c_1 = 1`.
- **Three sub-lemmas identified** (each `sorry`-stubbed with
  explicit statements):
  - `constant_term_taylor`: Taylor estimate for the constant term
    `((1/2+δ)^n − (1/2−δ)^n)/2 = nδ/2^(n−1) + O(δ²)`.
  - `binom_weight_perturb`: `|C·p^a q^b − C/2^(a+b)| ≤ M·δ`.
  - `suffMinDelta_first_order`: under the IH, `|suffMinDelta −
    suffMin·δ| ≤ M·δ²` (using 1-Lipschitz of `min`).
- **Inductive step `sorry`-stubbed** with a comment outlining the
  combinatorial argument (combine the three sub-lemmas + `c_succ`).

Sorry count: 7 → 10 (added 3 sub-lemma stubs identifying the
missing real-analysis pieces; gained the proved n=1 base case).
Pushed as commit `493e1d5`.

### Prompt 87
> What should we do next?

Offered three options ranked by impact:
1. Prove `joint_step` (master §4.3 induction) — high impact,
   collapses many sorries.
2. Prove `constant_term_taylor` (Δ→c bridge sub-lemma) — clean,
   independent.
3. Prove `c_limit_exists` (Theorem 4.10) — requires (1) first.

### Prompt 88
> Yes, please do (1)!

Wrote out `joint_step` as a strong-induction proof. Added two
helpers: `suffMin_eq_of_min` (equality version) and `c_anti_chain`
(chains the IH `c k < c (k-1)` into `c n ≤ c m`).

Status of the inductive step at `n ≥ 7`:
- **(a) Collapse**: PROVED. Both `j ∈ {1, 2, 3}` (via the existing
  `c_ge_*_of_ih` helpers) and `j ∈ {4, …, n−1}` (via `c_anti_chain`
  + the explicit `c_4 > c_6`).
- **(d) Linear recursion**: PROVED. Apply `c_succ`, split `Ico 1 n`
  at `j = 4`, substitute `h_a` on each piece, factor out `c (n−1)`
  on the high piece, evaluate via `choose_sum_3_to_pred`, close with
  `field_simp + push_cast + ring`.
- **(b) Lower bound**:
  - n ∈ [7, 12]: PROVED via `alg_id` + IH(b).
  - n ≥ 13: SUB-SORRY (cumulative argument: ε_12 > 1/60, infinite
    series and products).
- **(c) Strict decrease**:
  - n ≥ 13: PROVED via `alg_id` + IH(b).
  - n ∈ [7, 12]: SUB-SORRY (per-n numerical, requires explicit
    c_7..c_12).
- **`hB_lt`** (`B_n < 1` for n ≥ 7): SUB-SORRY (easy but skipped).

Base cases n ∈ {4, 5, 6} fully proved from the explicit values.

Sorry count unchanged at 10 — `joint_step` still counts as one
sorry, but with three explicit internal sub-sorries instead of
being one giant stub. Pushed as commit `f87d0c5`.

### Prompt 89
> Please update claude.md and journal.md

Extended both files with Prompts 85-89 (this update).

### Prompt 90
> Yes, I want you to chip away at the three remaining sub-sorries inside joint_step?

Closed two of three sub-sorries:
- **`hB_lt`** (`B_n < 1` for n ≥ 7): proved via `choose_sum_3_to_pred`
  + `Finset.sum_pos` on the `j ≥ 4` part.
- **(c) for n = 7**: c_7 < c_6 reduces to a concrete rational
  inequality after substituting c_6 = 113337/65536 and the cast
  lemmas Nat.choose 7 2 = 21, Nat.choose 7 3 = 35; closed by `norm_num`.

Pushed as commits `82b2ef6`.

### Prompts 91-92
> continue / yes

Extended (c) ≤ 12 case:
- **n = 8**: pre-derived `hc8 = 1843764663 / 1073741824` from h_d at 7
  + c_six.
- **n = 9**: derived `hc9 = 941650327899 / 549755813888` from h_d at 8
  + hc8.
- **n = 10**: pattern continues with `hc10`.
- **n = 11, 12**: switched to symbolic chain (no need to specify
  numerical c_10 and c_11 values; norm_num handles the deeply nested
  rational).

After all six cases: (c) ≤ 12 sub-sorry is fully closed. Only
remaining sub-sorry inside joint_step: (b) for n ≥ 13.

Pushed as commits `3b4b859`, `83481dc`.

### Prompt 93
> /usage

Clarified that `/usage` is a Claude Code slash command, not something
I can execute — user should type it in the prompt directly. Offered
informal session summary.

### Prompt 94
> Continue

Started attacking (b) ≥ 13:
- Derived `c_12` explicitly inside (b) ≥ 13 via the IH(d) chain
  hc7 → hc8 → … → hc12 (six derivations using cast lemmas).
- Verified `h_buffer : c_12 ≥ 27/16 + 1/60` by `norm_num` on the
  fully-substituted symbolic expression.
- Pushed as commit `a4fd139`.

Then proved the polynomial fact `poly_cube_bound : 12·k² + 7·k + 12 ≤ k³`
for k ≥ 13 (the algebraic core for the geometric ratio
`B_{k+1} ≤ (5/8)·B_k`). Pushed as `2ce697b`.

### Prompt 95
> Can you try 2. for a limited amount of time?

Attempted four different inductive lower-bound invariants for
`c_n ≥ 27/16 + γ` (constant `γ`, polynomial `α/n^k`, threshold
`L₀`, substitution `(c_n − 27/16)·2^n`). All four fail at the
inductive step or the base case because the naive recursive bound
on `c_12 − 27/16 ≥ 2847/8388608 ≈ 3.4·10⁻⁴` is too small to
bootstrap any clean invariant — the manuscript's actual buffer
`> 1/60` is genuinely needed and requires explicit computation.

Reported back that "option 2" doesn't escape the underlying need
for some explicit computation.

### Prompt 96
> Yes, please do option 1 compactly.

Did Compactly: derived hc12 explicitly via the IH(d) chain
inside (b) ≥ 13, verified `h_buffer : c_12 ≥ 27/16 + 1/60`. Already
done in Prompt 94 — this prompt confirmed direction.

### Prompt 97
> Please attempt the series-tail bound.

Built the algebraic foundation for the geometric tail:
- **`cast_choose_three`**: `(Nat.choose n 3 : ℝ) = n·(n−1)·(n−2)/6`
  for all `n`. Proved by induction using `Nat.choose_succ_succ`
  (Pascal) and `Nat.cast_choose_two`.
- **`B_ratio_bound`**: `B_{k+1} ≤ (5/8)·B_k` for `k ≥ 13`.
  After unfolding B_lin and substituting cast lemmas, `nlinarith`
  closes using `poly_cube_bound`.
- **`poly_quad_bound`**: `7·k² + 406 ≥ 127·k` for `k ≥ 14`.
- **`delta_ratio_bound`**: `δ_{k+1} ≤ (9/11)·δ_k` for `k ≥ 14`
  (the δ-series is increasing at k = 13, so the geometric ratio
  starts at k = 14). Translates `poly_quad_bound` to ℝ and uses
  `nlinarith`.

Pushed as commits `04fb3fa`, `5a67add`.

### Prompt 98
> yes, let's do it!!!

Pushed all the way through to closing the (b) ≥ 13 sub-sorry,
fully proving Lemmas 4.6, 4.7, 4.8 and Prop 4.9.

New lemmas added:
- **`geometric_sum_bound`**: generic
  `(0 ≤ r < 1) → (0 ≤ x_a) → (∀ k ≥ a, x (k+1) ≤ r · x k) → ∀ N, ∑_{k=a}^{N-1} x_k ≤ x_a / (1-r)`.
  Proves first `x_k ≤ x_a · r^(k-a)` by `Nat.le_induction`, then bounds
  `∑_{j=0}^{N-a-1} r^j ≤ ∑'_n r^n = (1-r)⁻¹` using Mathlib's
  `summable_geometric_of_lt_one` and `tsum_geometric_of_lt_one`.
- **`B_tail_bound`**: `∑_{k=13}^{N-1} B_k ≤ 1/8` (numerical:
  `B_13 = 379/8192`, `B_13 · 8/3 = 379/3072 < 384/3072 = 1/8`).
- **`delta_seq`** + **`delta_seq_ratio`**: rephrasing of
  delta_ratio_bound using a clean `delta_seq` definition for use
  with `geometric_sum_bound`.
- **`delta_tail_bound`**: `∑_{k=13}^{N-1} delta_seq k ≤ 1/200`.
  Splits at k = 14: `δ_13 + δ_14 · 11/2 < 1/200`.
- **`cum_eps_bound`**: cumulative invariant
  `c m − 27/16 ≥ (1/60)·(1 − ∑ B_k) − ∑ delta_seq k`
  for m ≥ 12, given the buffer at m = 12 and the linear recursion at
  all k ∈ [13, m]. Inductive: at each step,
    LHS − RHS = B_{k+1} · ((1/60)·∑ B + ∑ δ) ≥ 0
  closes via nlinarith with h_alg, nonnegativities, and B_lin (k+1) < 1.

Application inside (b) ≥ 13:
- Build `h_lin_rec : ∀ k ∈ [13, n], c k = A_lin k + (1−B_lin k)·c (k−1)`
  by combining IH(d) at k < n with the local h_d at k = n.
- Apply `cum_eps_bound n h_buffer h_lin_rec`.
- Combine with `B_tail_bound (n+1)` and `delta_tail_bound (n+1)`:
    c n − 27/16 ≥ (1/60)·(7/8) − 1/200 = 23/2400 > 0.
- linarith closes.

🎉 **Sorry count: 10 → 9.** joint_step is fully proved end-to-end.
The four manuscript-facing lemmas (Lemma 4.6, 4.7, 4.8, Prop 4.9)
are now formally established, no longer sorry-conditional.

The remaining 9 sorries are all in §4.4 (Δ→c bridge sub-lemmas,
Theorem 4.10 limit, Cor 4.11 shape claims) — independent of §4.3.

Pushed as commits `897fab6`, `d1d30a1`.

### Prompt 99
> please update claude.md and journal.md

Extended both files with Prompts 90-99 (this update).

### Prompt 100
> Did anything in the formalization come up which needs an update in
> manuscript, e.g. edge cases?

Identified three observations from the formalization, with no actual
mathematical errors but two minor clarifications worth adding to the
manuscript:

1. The δ-series is **increasing at k = 13** (`δ_14/δ_13 = 11/10`)
   before decreasing geometrically from k = 14. The closed-form
   route in the manuscript bypasses this; an inductive proof must
   split at k = 14.
2. **`B_n < 1`** for n ≥ 7 is used implicitly (in (1 − B_n)·c_{n−1}
   for the linear recursion). The numerator
   `2 + n + C(n,2) + C(n,3)` is strictly less than `2^n` because
   the missing terms `∑_{j=4}^{n-1} C(n,j) > 0`.
3. The buffer `ε_12 > 1/60` is *very* tight numerically (actual
   value ≈ 0.01672 vs `1/60 ≈ 0.01667`); a larger buffer would
   work too but the manuscript's choice is correct.

### Prompt 101
> yes

Added the two clarifying remarks (1) and (2) to §4.3 of
manuscript.tex. Pushed as commit `2a5d013`. PDF stays at 8 pages.

### Prompt 102
> What needs to be fixed still?

Provided a status snapshot:

**Fully formalized:** §1, §2, §3, §4.1, §4.2, §4.3 (joint_step
done — Lemmas 4.6, 4.7, 4.8, Prop 4.9 + Example 4.5 values).

**Still has `sorry` (9 total, all in §4.4):**
1. `constant_term_taylor` — Taylor estimate for the deficit
   constant term.
2. `binom_weight_perturb` — linear perturbation of the binomial
   weights.
3. `suffMinDelta_first_order` — perturbation of the suffix-min.
4. `deficit_first_order` (n ≥ 2 step) — combine 1, 2, 3.
5. `c_limit_exists` — Theorem 4.10 existence.
6. `c_limit_formula` — Theorem 4.10 explicit formula.
7. `w_gap_first_order` — Cor 4.11 (i).
8. `w_local_min_at_five` — Cor 4.11 (ii).
9. `no_first_order_local_max` — Cor 4.11 (iii).

Items 5, 6 are tractable independently (use the now-proved Prop 4.9
+ Mathlib's filter machinery). Items 7-9 wait on item 4. Items 1-3
are independent real-analysis lemmas. Estimated total effort:
~600 lines.

### Prompt 103
> Let us do this tomorrow and stop formalizing today.

Acknowledged. End-of-session summary: 15 commits today since
`6c6ce2a`; §1–§4.3 fully formalized; 9 sorries remain in §4.4.
Latest commit `2a5d013` on `main`, pushed to
https://github.com/pfaffelh/coins. Build green.

### Prompt 104
> Final update of journal.md and claude.md for today.

This update — Prompts 100-104.

## 2026-04-20 — Session 3

### Prompt 105
> Side question: Would you be able to do the formalization in a
> different proof assistant?

Offered a brief comparison: Coq (older, more mature tactics but
less automation), Isabelle/HOL (strongest automation, classical
default), Lean 4 / Mathlib (chosen here — active community, best
library for coin games / probability / combinatorics). Rocq
(Coq's rebrand) would work but lacks Mathlib's formal reach.

### Prompt 106
> Let us continue with the formalization. Where did we end yesternday?

Recap: 9 sorries remain in §4.4 (items 1–9 of the status list).
Recommended picking up with either items 5/6 (Theorem 4.10 — limit
of `c_n`) or items 1–4 (Δ → c bridge — real-analysis chain).

### Prompt 107
> B

Interpreted as option B = Theorem 4.10 (limit of `c_n`).

### Prompt 108
> Please attempt this first!

Proved `c_limit_exists` (Theorem 4.10 existence form) via shift
`f n := c (n+5)`, which is antitone (from `c_strict_anti_from_five`)
and bounded below by `27/16` (from `c_ge_27_16_full`), using
`tendsto_atTop_ciInf`. Committed as `7ffd55a`.

Next: proved `c_iterate` — the finite iteration of the linear
recursion `c_n = c_{n₀-1}·∏(1-B_m) + ∑ A_k·∏(1-B_m)` by
induction on `n`. Committed as `aff03c3`.

### Prompt 109 (multiple messages)
> a / "No, please try a"

User chose option (a) = explicit form of Theorem 4.10
(`c_limit_formula`). Pushed through the tower of helper lemmas:

1. `summable_B_lin` (ℕ-indexed, via split at 13 + `B_tail_bound`) —
   `0a1ab5b`.
2. `multipliable_one_minus_B` (subtype, via
   `Real.multipliable_one_add_of_summable`) — `2cd8ef9`.
3. `shiftEquiv : ℕ ≃ {m // n₀ ≤ m}`, `multipliable_one_minus_B_shifted`
   (ℕ-indexed shifted form), `tprod_subtype_eq_tprod_shifted`
   (reindex subtype tprod to ℕ tprod), `tendsto_prod_Ico_B`
   (finite `∏ m ∈ Ico n₀ (n+1)` converges to subtype tprod) —
   `0157050`.
4. `c_limit_formula` (structure complete) — passes finite
   identity `c_iterate` through `Tendsto`, combines product and
   sum convergence via uniqueness of limits.
   One narrow sub-sorry remains: `tendsto_sum_Ico_A_prod`
   (sum convergence — requires Tannery's theorem / dominated
   convergence, `Summable A_lin`, and pointwise convergence of
   inner products). — `ba8c703`.

**End-of-session status (2026-04-20):**
- `c_limit_exists` and `c_iterate`: proved.
- `c_limit_formula`: proved modulo one narrow sub-sorry.
- Sorry count: 9 → 8 (net -1, but really 2 items resolved with 1
  new focused sub-gap introduced).
- Build green throughout. All commits pushed to GitHub.

### Prompt 110
> Is the open gap also in the manuscript?

Identified that the open gap *is* in the manuscript: the proof of
Theorem 4.10 says only "Iterating the recursion from $n=n_0$ and
taking $n\to\infty$ yields (eq:L-formula); the rate follows from
$B_n=O(n^3/2^n)$." This compresses into one sentence both:
(a) infinite-product convergence and
(b) dominated-convergence / Tannery interchange for the series of
    products (exactly the Lean `tendsto_sum_Ico_A_prod` sorry).

### Prompt 111
> Please make the manuscript more exact, including a reference.
> Then we will go to its formalization.

Rewrote the proof of Theorem 4.10 with three explicit steps:
existence (Lemmas 4.7 + 4.8), infinite product (via summability
of $B_m$ and $0<B_m<1$ for $m\ge 7$), and series of products
(Tannery's theorem with dominant $|A_k|$ summable). Added
Knopp 1990 (*Theory and Application of Infinite Series*) to the
bibliography as the reference for both steps. PDF: 8 → 9 pages.
Commit `cd121b4`.

### Prompt 112
> yes

Started formalizing the three pieces for
`tendsto_sum_Ico_A_prod`:

**Piece 1 — summable `|A_lin|` on ℕ.** Proved via
`A_lin_le_bound`: decomposed `A_lin n` into four pieces each
≤ (polynomial) · (1/2)^n, summable by
`summable_pow_mul_geometric_of_norm_lt_one`. Cubic bound
`n(n-1)(n-2) ≤ n³` uses `n³ − n(n-1)(n-2) = 3n² − 2n ≥ 0`,
split on `n = 0` vs `n ≥ 1` to avoid cubic-polynomial nlinarith
timeouts. `A_lin_nonneg`, `n_div_pow_pred_le` as helpers.
Commits `73f3ecb`, `4653150`.

**Piece 2 — uniform bound on inner products.** Extracted
`B_lin_pos` and `B_lin_lt_one` (for `n ≥ 7`) as global lemmas
from inline inside `joint_step`. Added `one_minus_B_pos`,
`one_minus_B_le_one`, and `prod_Ico_one_minus_B_in_unit_interval`
(finite partial products of `(1-B_m)` for `m ≥ 7` lie in `[0, 1]`).
Commit `e771c74`.

**Piece 3 — pointwise inner-product convergence + Tannery.**
Not attempted yet. Pointwise convergence would follow from
applying `tendsto_prod_Ico_B` with `n₀ := k+1` (noting `{m // k < m}
= {m // k+1 ≤ m}` since `<` on ℕ is `+1 ≤`). The Tannery
application requires converting the finite Finset.Ico-sum into a
subtype tsum with zero-extension — moderate but fiddly.

**Final status (2026-04-20, evening):**
- Sorry count: 9 → 8 (one new narrow sorry introduced, one older
  resolved).
- `c_limit_exists`, `c_iterate`, `summable_A_lin`, and all Piece 1 +
  Piece 2 infrastructure: done.
- `tendsto_sum_Ico_A_prod` (Piece 3): still sorry. The manuscript
  now documents the Tannery step explicitly with a reference, so
  the formal/informal gap aligns.
