/-
  Challenge.lean — Statements of the headline theorems of the Coins paper.

  This file is the *trusted* surface of the formalization.  A verifier
  reads this file together with `CoinsLean/Defs.lean` (which provides
  the seven definitions `a`, `w`, `c`, `deficit`, `suffMin`, `A_lin`,
  `B_lin`) and confirms that the sixteen theorems below faithfully
  capture the manuscript (`Manuscript/manuscript.tex`).  The proofs
  are deferred to `sorry` here; they live under `CoinsLean/` and are
  packaged in `Solution.lean`.

  The Lean comparator
  (https://github.com/leanprover/comparator) verifies, with a sandboxed
  build and a kernel replay, that the proofs in `Solution.lean`
  establish exactly the statements declared here, using only the three
  standard foundational axioms `propext`, `Quot.sound`,
  `Classical.choice`.

  Both `Challenge.lean` and the proof modules import the same
  `CoinsLean.Defs` module; this means there is exactly one kernel-level
  definition for each of `a`, `w`, `c`, `deficit`, `suffMin`, `A_lin`,
  `B_lin`, eliminating any risk of two slightly-different elaborations.
-/
import Mathlib
import CoinsLean.Defs

open Finset BigOperators Nat

/-! ## Theorems -/

/-- **Theorem 2.1.**  At the fair coin every strategy that takes the
    immediate win wins with probability `1/2`. -/
theorem w_half : ∀ n : ℕ, 1 ≤ n → w (1/2 : ℝ) n = 1/2 := by
  sorry

/-- **Theorem 3.1.**  For `1/2 < p < 1` and `n ≥ 2`:
    (i) `w` is strictly increasing in `n`,
    (ii) the sharp bound `w(p, n−1) · (p^n + (1−p)^n) < p^n` holds,
    (iii) `w` agrees with strategy ONE: `w(p, n) = a(p, n)`. -/
theorem above_half (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt_one : p < 1) :
    ∀ n : ℕ, 2 ≤ n →
      w p (n - 1) < w p n ∧
      w p (n - 1) * (p ^ n + (1 - p) ^ n) < p ^ n ∧
      w p n = a p n := by
  sorry

/-- **Corollary 3.2** (linear recursion above `1/2`).
    For `1/2 < p < 1` and every `n ≥ 1`,
    `w(p, n) = p^n + (1 − p^n − (1−p)^n) · w(p, n−1)`. -/
theorem above_linear_rec (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    w p n = p ^ n + (1 - p ^ n - (1 - p) ^ n) * w p (n - 1) := by
  sorry

/-- **Theorem 3.3 (existence of `W(p)`).**
    For `1/2 < p < 1`, the limit `W(p) := lim_{n→∞} w(p, n)` exists. -/
theorem above_limit_exists (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1) :
    ∃ W : ℝ, Filter.Tendsto (fun n => w p n) Filter.atTop (nhds W) := by
  sorry

/-- **Theorem 3.3 (lower bound).**  For `1/2 < p < 1`, the limit `W(p)`
    satisfies `W(p) ≥ p > 1/2`. -/
theorem above_limit_ge (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1) :
    ∀ W : ℝ, Filter.Tendsto (fun n => w p n) Filter.atTop (nhds W) →
      p ≤ W := by
  sorry

/-- **Lemma 4.5** (asymptotic collapse, low part).  For `n ≥ 7` and
    `j ∈ {1, 2, 3}`, `min_{j ≤ m ≤ n−1} c_m = c_j`. -/
theorem suffMin_collapse_low (n j : ℕ) (hn : 7 ≤ n) (h1 : 1 ≤ j) (h3 : j ≤ 3) :
    suffMin j n = c j := by
  sorry

/-- **Lemma 4.5** (asymptotic collapse, high part).  For `n ≥ 7` and
    `j ∈ {4, …, n−1}`, `min_{j ≤ m ≤ n−1} c_m = c_{n−1}`. -/
theorem suffMin_collapse_high (n j : ℕ) (hn : 7 ≤ n) (h4 : 4 ≤ j) (hjn : j < n) :
    suffMin j n = c (n - 1) := by
  sorry

/-- **Lemma 4.6** (uniform lower bound).  `c_m ≥ 27/16` for every `m ≥ 4`. -/
theorem c_ge_27_16_full : ∀ m : ℕ, 4 ≤ m → c m ≥ 27 / 16 := by
  sorry

/-- **Lemma 4.7** (strict decrease).  The sequence `(c_n)_{n ≥ 5}` is
    strictly decreasing: `c_{n+1} < c_n` for every `n ≥ 5`. -/
theorem c_strict_anti_from_five : ∀ n : ℕ, 5 ≤ n → c (n + 1) < c n := by
  sorry

/-- **Proposition 4.8** (linear recursion).  For every `n ≥ 7`,
    `c_n = A_n + (1 − B_n) · c_{n−1}`. -/
theorem c_linear_rec (n : ℕ) (h : 7 ≤ n) :
    c n = A_lin n + (1 - B_lin n) * c (n - 1) := by
  sorry

/-- **Theorem 4.10 (existence).**  The limit `L := lim_{n→∞} c_n` exists. -/
theorem c_limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L) := by
  sorry

/-- **Numerical buffer for §4.3, n ≥ 13.**  `c_{12} − 27/16 ≥ 1/60`.
    This explicit lower bound seeds the cumulative argument that
    propagates `c_n ≥ 27/16` for all `n ≥ 13`. -/
theorem c_twelve_buffer : c 12 - 27 / 16 ≥ 1 / 60 := by
  sorry

/-- **Proposition 4.4 (first-order coefficient).**
    `c n · δ` is the first-order term of `deficit (1/2 − δ) n` as `δ → 0⁺`:
    there exist `M ≥ 0` and `δ₀ > 0` such that the second-order remainder
    is bounded by `M · δ²` on `(0, δ₀)`. -/
theorem deficit_first_order (n : ℕ) (hn : 1 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |deficit (1/2 - δ) n - c n * δ| ≤ M * δ ^ 2 := by
  sorry

/-- **Corollary 4.11 (i).**  The gap `w(p, n−1) − w(p, n)` has first-order
    coefficient `c_n − c_{n−1}` as `p = 1/2 − δ`, `δ → 0⁺`. -/
theorem w_gap_first_order (n : ℕ) (hn : 2 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |w (1/2 - δ) (n - 1) - w (1/2 - δ) n - (c n - c (n - 1)) * δ| ≤
        M * δ ^ 2 := by
  sorry

/-- **Corollary 4.11 (ii).**  At first order, `n = 5` is a strict local
    minimum of `n ↦ w(1/2 − δ, n)` near the fair coin. -/
theorem w_local_min_at_five :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) 5 < w (1/2 - δ) 4 ∧ w (1/2 - δ) 5 < w (1/2 - δ) 6 := by
  sorry

/-- **Corollary 4.11 (iii).**  No first-order local maximum: there exists
    `N` such that for every `n ≥ N` the value `w(1/2 − δ, n)` is
    eventually less than `w(1/2 − δ, n + 1)`. -/
theorem no_first_order_local_max :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) n < w (1/2 - δ) (n + 1) := by
  sorry
