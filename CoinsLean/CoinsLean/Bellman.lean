/-
  Bellman.lean — Definition of the strategy B value b(p, n)
  for the all-heads-wins coin game, and proof that b(1/2, n) = 1/2.
-/
import Mathlib

open Finset BigOperators Nat

/-! ### Strategy B value -/

/-- Winning probability under strategy B (set aside all heads each round). -/
noncomputable def b (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    p ^ (n + 1) +
      ∑ j ∈ (Ico 1 (n + 1)).attach,
        (Nat.choose (n + 1) (j : ℕ) : ℝ) * p ^ (n + 1 - (j : ℕ)) * (1 - p) ^ (j : ℕ) *
          b p (j : ℕ)
  termination_by n => n
  decreasing_by
    have := (Finset.mem_Ico.mp j.prop).2
    omega

/-! ### Rewriting lemma: convert attach-based sum to plain sum -/

theorem b_zero (p : ℝ) : b p 0 = 1 := by
  rw [b.eq_1]

theorem b_succ (p : ℝ) (n : ℕ) :
    b p (n + 1) =
      p ^ (n + 1) +
        ∑ j ∈ Ico 1 (n + 1),
          (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j * b p j := by
  rw [b.eq_2]
  congr 1
  exact Finset.sum_attach (Ico 1 (n + 1))
    (fun j => (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j * b p j)
