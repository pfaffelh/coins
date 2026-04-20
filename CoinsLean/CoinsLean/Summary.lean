/-
  Summary.lean — a one-page tour of the key formalized results.

  For each definition we first quote the original source (from
  `Optimal.lean` or `Perturbation.lean`) as a block comment, then run
  `#print` so Lean's kernel confirms (and shows) the fully elaborated
  form.  For each theorem we run `#check` to show its type, and at the
  end `#print axioms` confirms that the proofs rely only on the three
  standard Lean foundational axioms.

  To see the output, run (from `CoinsLean/`):
      lake env lean CoinsLean/Summary.lean
-/

import CoinsLean.Perturbation

-- ======================================================================
-- # Definitions
-- ======================================================================

-- ## `w p n` — optimal winning probability for `n` coins with
--              head-probability `p`.  Defined by the Bellman equation:
/-
  noncomputable def w (p : ℝ) : ℕ → ℝ
    | 0     => 1
    | n + 1 =>
      p ^ (n + 1) +
        ∑ j ∈ (Ico 1 (n + 1)).attach,
          (Nat.choose (n + 1) j.val : ℝ) * p ^ (n + 1 - j.val) * (1 - p) ^ j.val *
            ((Ico j.val (n + 1)).attach.sup'
              (mem_attach _ _) (fun m => w p m.val))
    termination_by n => n
-/
#check @w
#print w

-- ## `deficit p n` — the shortfall from the fair-coin optimum
--                    (Definition 4.1 of the manuscript):
/-
  noncomputable def deficit (p : ℝ) (n : ℕ) : ℝ := 1 / 2 - w p n
-/
#check @deficit
#print deficit

-- ## `c n` — the first-order coefficient of `deficit (1/2 − δ) n` in δ.
--            Defined directly by the Bellman-like recursion from
--            Proposition 4.4:
/-
  noncomputable def c : ℕ → ℝ
    | 0     => 0          -- not used; the recursion starts at n = 1
    | 1     => 1
    | n + 2 =>
      ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) +
        (1 / (2 : ℝ) ^ (n + 2)) *
          ∑ j ∈ (Ico 1 (n + 2)).attach,
            (Nat.choose (n + 2) j.val : ℝ) *
              ((Ico j.val (n + 2)).attach.inf'
                (mem_attach _ _) (fun m => c m.val))
    termination_by n => n
-/
#check @c
#print c

-- (The coefficients `A_lin n` and `B_lin n` of the linear recursion
-- `c_n = A_n + (1 − B_n)·c_{n-1}` for `n ≥ 7` (Proposition 4.9) are
-- `private` in `Perturbation.lean` and therefore not accessible here.)

-- ======================================================================
-- # Theorems
-- ======================================================================

-- ## Theorem 4.10 (existence). The limit `L := lim c_n` exists.
#check @c_limit_exists

-- ## Theorem 4.10 (explicit formula). For any `n₀ ≥ 7`,
--    L = c_{n₀−1} · ∏_{m ≥ n₀} (1 − B_m) + Σ_{k ≥ n₀} A_k · ∏_{m > k} (1 − B_m).
#check @c_limit_formula

-- ## Proposition 4.4. `c n · δ` is the first-order term of
--    `deficit (1/2 − δ) n` as δ → 0⁺.
#check @deficit_first_order

-- ## Corollary 4.11 (i). The gap `w_{n−1,p} − w_{n,p}` has first-order
--    coefficient `c_n − c_{n−1}` as `p = 1/2 − δ`, `δ → 0⁺`.
#check @w_gap_first_order

-- ## Corollary 4.11 (ii). To first order, `n = 5` is a strict local
--    minimum of `n ↦ w(1/2 − δ, n)`.
#check @w_local_min_at_five

-- ## Corollary 4.11 (iii). No local maximum at first order: eventually
--    `w(1/2 − δ, n) < w(1/2 − δ, n + 1)`.
#check @no_first_order_local_max

-- ======================================================================
-- # Axioms used
-- ======================================================================

-- All main results depend only on Lean's three foundational axioms:
-- `propext`, `Classical.choice`, and `Quot.sound`.  No custom axioms.
#print axioms c_limit_exists
#print axioms c_limit_formula
#print axioms deficit_first_order
#print axioms w_gap_first_order
#print axioms w_local_min_at_five
#print axioms no_first_order_local_max
