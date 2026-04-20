/-
  Summary.lean — a one-page tour of the key formalized results.

  This file uses only `#check` statements to display the types of the
  definitions and theorems that together state Theorem 4.10 and
  Corollary 4.11 of the manuscript, as formalised in Lean 4.

  Building this file verifies — via Lean's kernel — that all the
  signatures below type-check against the formalization in
  `CoinsLean.Perturbation`; it does not re-prove anything.

  To see the output, run (from `CoinsLean/`):
      lake env lean CoinsLean/Summary.lean
-/

import CoinsLean.Perturbation

-- # Definitions

-- `w p n` — optimal winning probability with `n` coins and head
-- probability `p`; defined recursively via the Bellman equation.
-- Expected: w : ℝ → ℕ → ℝ
#check @w

-- `deficit p n := 1/2 - w p n` — the shortfall from the fair-coin
-- optimum (Definition 4.1).
-- Expected: deficit : ℝ → ℕ → ℝ
#check @deficit

-- `c n` — the first-order coefficient of `deficit (1/2 - δ) n` in δ,
-- defined by the recursion from Proposition 4.4:
-- `c_n = n/2^(n-1) + (1/2^n) · Σ_{j=1}^{n-1} C(n,j) · min_{j ≤ m ≤ n-1} c_m`.
-- Expected: c : ℕ → ℝ
#check @c

-- `A_lin n` and `B_lin n` — the coefficients of the linear recursion
-- `c_n = A_n + (1 − B_n)·c_{n−1}` for `n ≥ 7` (Proposition 4.9).
-- They are marked `private` in `Perturbation.lean`, so no `#check` here.

-- # Theorem 4.10 (existence)

-- The limit `L := lim c_n` exists.
-- Expected:
--   c_limit_exists : ∃ L, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L)
#check @c_limit_exists

-- # Theorem 4.10 (explicit formula)

-- For any `n₀ ≥ 7`,
--   L = c_{n₀−1} · ∏_{m ≥ n₀} (1 − B_m)  +  Σ_{k ≥ n₀} A_k · ∏_{m > k} (1 − B_m).
#check @c_limit_formula

-- # Proposition 4.4 (first-order bridge)

-- `c n · δ` is the first-order term of `deficit (1/2 − δ) n` as δ → 0⁺.
#check @deficit_first_order

-- # Corollary 4.11 (shape near p = 1/2)

-- (i) The gap `w_{n−1,p} − w_{n,p}` has first-order coefficient
-- `c_n − c_{n−1}` as `p = 1/2 − δ`, `δ → 0⁺`.
#check @w_gap_first_order

-- (ii) To first order, `n = 5` is a strict local minimum of
-- `n ↦ w(1/2 − δ, n)`.
#check @w_local_min_at_five

-- (iii) No local maximum at first order: eventually
-- `w(1/2 − δ, n) < w(1/2 − δ, n + 1)`.
#check @no_first_order_local_max

-- # Axioms used
-- Every main result depends only on the three standard Lean axioms:
--   propext, Classical.choice, Quot.sound.
-- No custom axioms are introduced.
#print axioms c_limit_exists
#print axioms c_limit_formula
#print axioms deficit_first_order
#print axioms w_gap_first_order
#print axioms w_local_min_at_five
#print axioms no_first_order_local_max
