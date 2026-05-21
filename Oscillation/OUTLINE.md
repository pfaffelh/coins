# Paper 2 — outline and gap analysis

*Planning document. Decided 2026-05-21: the all-heads coin-game work
splits into two papers. Paper 1 (`Manuscript/`, fully Lean-verified)
goes to Experimental Mathematics unchanged. Paper 2 — this folder — is
the asymptotic / log-periodic regime: rigorous partial results +
conjecture + numerics, not Lean-verified.*

*Status update: the unified manuscript `Oscillation/manuscript.tex` now
exists and is the paper of record. The development note `infMaxMin.tex`
is **deprecated** (superseded by it); `strategy_all_asymptotics.tex`
remains a building block. The section structure and gap catalogue
below are reflected, in finished form, in the manuscript itself.*

---

## 1. Working title

**"Log-periodic oscillation in the all-heads coin game."**
Alternatives: *"The non-perturbative regime of the all-heads coin
game"*; *"Asymptotics of the all-heads coin game below the fair
coin."*

## 2. Thesis (one paragraph)

Paper 1 determines the optimal winning probability `w(p,n)` exactly at
`p = 1/2`, for `p > 1/2` (with the limit `W(p)`), and to first order
in `1/2 - p` for `p < 1/2`. Paper 2 studies the *non-perturbative*,
large-`n` structure for `p < 1/2`. Two threads, tied together:

- **Strategy ALL** has a clean log-periodic large-`n` description:
  `b(p,n)` is asymptotic to a non-constant function periodic in
  `log n` of period `log(1/(1-p))`, so it does *not* converge.
- **The optimal value** `w(p,n)` is conjectured to inherit this:
  for every `p < 1/2` it has infinitely many local maxima and minima
  (it is not eventually monotone).

The paper assembles the rigorous partial results, a renormalisation
framework reducing the conjecture to a single non-degeneracy, and
numerical evidence — and delineates precisely the analytic gaps a full
proof still requires.

## 3. Relationship to Paper 1

Paper 2 cites Paper 1 for the setup and the exact/perturbative
results; it is the asymptotic/oscillatory companion. Honest contrast:
Paper 1 is exact, perturbative, and **machine-checked**; Paper 2 is
analytic (analytic combinatorics, Mellin transforms, a renormalisation
argument), with **rigorous results + a conjecture + numerics**, and is
not — and in the near term cannot be — formally verified.

## 4. Source material already in the repository

| File | Provides |
|---|---|
| `Manuscript/strategy_all_asymptotics.tex` | strategy-ALL functional equation, q-Fubini, Mellin asymptotics, numerics |
| `Manuscript/infMaxMin.tex` | the optimal-value oscillation: reduction, Proposition A, transfer lemma, renormalisation route, gap analysis |
| `simulation/b_asymptotics.py` | strategy-ALL log-periodicity, numerical |
| `simulation/renorm_validation.py` | renormalisation-route validation |

Proposed first action: migrate the two `.tex` files into this folder
(`git mv`), since they are Paper 2's building blocks (see §8).

## 5. Section structure

1. **Introduction.** The game (brief recall); Paper 1 settled the
   exact/perturbative picture; the question of fine non-perturbative
   structure for `p < 1/2`; statement of the two threads and of the
   main conjecture; honest note on epistemic status.
2. **Setup and recollections.** Bellman equation, strategies ONE/ALL,
   `a, b, w`; cite Paper 1. Strategy ALL recursion; deficit notions as
   needed.
3. **Strategy ALL: functional equation and log-periodic asymptotics.**
   EGF functional equation `B(z) = 1 + (e^{pz}-1)B(qz)`; iterated
   series; the `q`-analogue of the Fubini (ordered-Bell) polynomials;
   saddle-point / Mellin analysis; the log-periodic profile `Φ_p`;
   the three regimes (`p = 1/2`, `p > 1/2`, `p < 1/2`). Source:
   `strategy_all_asymptotics.tex`. **Carries Gaps A, B.**
4. **The optimal value below 1/2 is not eventually increasing.**
   Proposition A (the `q^n`-domination argument). **Rigorous.**
5. **Reduction and the transfer lemma.** Conjecture ⇔ ¬(eventually
   increasing) ∧ ¬(eventually decreasing); the exact transfer lemma
   (on a non-increasing tail, `w` is a strategy-ALL sequence with
   finitely many initial values modified). **Rigorous.**
6. **The renormalisation route.** The recursion as a log-scale
   smoothing; the local fundamental coefficient `A(t)`; the
   propagation estimate (κ-part rigorous, remainder = Gap C); the
   conditional renormalisation theorem. Source: `infMaxMin.tex` §8.
7. **Eliminating the polynomial P.** The G3 reduction: the obstruction
   is `P`-independent — linear independence of the auxiliary profiles.
   Source: `infMaxMin.tex` §7. **Rigorous reduction.**
8. **Numerical evidence.** Log-periodicity of `b`; convergence of
   `A(t_0+kL)` to a non-zero limit; `n|κ(n)-1| → p ω²/(2q)`.
9. **The main conjecture and the status of a proof.** Clean statement;
   the gap analysis of §6 below; what each route (Mellin /
   renormalisation) still needs.
10. **Discussion / open problems.** Connection to van Doorn's
    "infinitely complex" remark; the local-extremum structure;
    possible further conjectures.

## 6. THE GAPS

A complete proof of the main conjecture is **not** in hand. The
missing pieces, named precisely:

| Gap | What | Where | Status | Closing it needs |
|---|---|---|---|---|
| **A** | Hayman-admissibility / sector control of `B(z)` | strategy-ALL asymptotics (§3) | open; the stated obstruction ("grows faster than `e^z`") dissolved after the `e^{z/p}→e^z` correction — `B` is entire of order 1, type 1. The real difficulty is the non-constant log-periodic factor. | a direct sector saddle-point estimate, or H-admissibility adapted to the oscillating factor. *Standard in spirit.* |
| **B** | Mellin contour justification | strategy-ALL asymptotics (§3) | open | the strip of analyticity and the contour shift for the Mellin transform of `log B(z) - z`. *Standard in spirit (Flajolet–Sedgewick).* |
| **C** | The remainder `r(t)` of the propagation estimate | renormalisation route (§6) | open | a density-level local CLT for `log J_n`, `J_n ~ Bin(n,q)`, plus the windowed-transfer bookkeeping. *Hard but standard.* |
| **D** | The non-degeneracy `A_∞ ≠ 0` (the base case) | §6–§7, the crux | open | for the genuine `b`, `A_∞ = γ_1`; non-vanishing follows from `ζ(1+it) ≠ 0` **given** the Mellin framework (Gaps A,B). The §7 reduction recasts it as linear independence of the profiles `Ψ_r`. **The genuine open problem.** |

**Done — not gaps** (the rigorous backbone of the paper):

- the EGF functional equation, the iterated series, the `q`-Fubini
  identity (strategy ALL);
- **Proposition A**: `w(p,n)` is not eventually increasing for
  `p < 1/2`;
- the **transfer lemma** (exact);
- the **κ-estimate** (Lemma 8.4: `κ(n) = 1 - (p/2qn)(ω²+iω) +
  O(n^{-3/2})`) — formerly "Step 1";
- the reduction lemmas and the **G3 `P`-elimination reduction**;
- the numerical confirmations.

### Dependency logic

```
Main conjecture
   ⇔  ¬(eventually increasing)  ∧  ¬(eventually decreasing)
        |                              |
        = Proposition A  ✓             ⟸ transfer lemma  ✓
                                          + renormalisation route:
                                              Theorem (conditional)
                                              needs  Gap C  ∧  Gap D
```

`Gap D`, as currently understood, is reachable only through the Mellin
picture, i.e. it presupposes `Gap A ∧ Gap B`. Hence:

> **A full proof of the main conjecture = Proposition A (done) +
> Gap C + Gap D, with Gaps A, B underpinning Gap D.**
> Step 1 (the κ-estimate) is done.

The two routes are complementary: the **renormalisation route** is the
elementary skeleton (replaces A, B by the single Gap C); the **Mellin
route** identifies the limit and supplies the `ζ(1+it) ≠ 0` input for
Gap D.

## 7. What a referee gets either way

Even with Gaps A–D open, Paper 2 is a genuine paper: a rigorous
theorem (Proposition A), the exact transfer lemma, the κ-estimate, the
reductions, a clean conjecture with a fully delineated proof
programme, and numerics confirming every prediction across many orders
of magnitude. This is squarely an *Experimental Mathematics*-style
contribution.

## 8. Suggested next steps

1. **Migrate** `infMaxMin.tex` and `strategy_all_asymptotics.tex` into
   `Oscillation/` (`git mv`); fix the in-prose cross-references.
2. **Merge the framing**: write Paper 2's Introduction and Setup,
   unifying the two notes (shared notation, one reference list).
3. Then attack the gaps incrementally — natural order **C, then A+B,
   then D** (C is self-contained; A+B feed D).

## 9. Open decisions

- Folder name `Oscillation/` — rename if preferred.
- Target venue for Paper 2 (Experimental Mathematics is a natural fit;
  decide after Paper 1's outcome).
- Whether to keep the Mellin route in the paper as a parallel
  (heuristic) section, or relegate it to a remark once the
  renormalisation route is complete.
