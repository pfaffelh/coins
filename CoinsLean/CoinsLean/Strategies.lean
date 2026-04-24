/-
  Strategies.lean — Strategy ONE value a(p,n) and proof that a(1/2,n) = 1/2.

  The recursion (eq:a-rec in the manuscript) is
      a(p, 0)     = 1,
      a(p, n+1)   = p^(n+1) + (1 - p^(n+1) - (1-p)^(n+1)) * a(p, n).
-/
import Mathlib

open Finset BigOperators Nat

/-- Winning probability under strategy ONE (set aside exactly one head when
    `1 ≤ k ≤ n-1`, all `n` heads when `k = n`). -/
noncomputable def a (p : ℝ) : ℕ → ℝ
  | 0     => 1
  | n + 1 => p ^ (n + 1) + (1 - p ^ (n + 1) - (1 - p) ^ (n + 1)) * a p n

theorem a_zero (p : ℝ) : a p 0 = 1 := rfl

theorem a_succ (p : ℝ) (n : ℕ) :
    a p (n + 1) = p ^ (n + 1) + (1 - p ^ (n + 1) - (1 - p) ^ (n + 1)) * a p n := rfl

theorem a_one (p : ℝ) : a p 1 = p := by
  rw [a_succ, a_zero]; ring

/-- a(1/2, n) = 1/2 for every n ≥ 1. -/
theorem a_half : ∀ n : ℕ, 1 ≤ n → a (1/2 : ℝ) n = 1/2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rw [a_succ]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [a_zero]; norm_num
    · have ih' := ih hk
      rw [ih']
      have hpow : (1 - (1/2 : ℝ) - 1/2) = 0 ∨
                  (1 - (1/2 : ℝ) ^ (k + 1) - (1/2) ^ (k + 1)) =
                    1 - 2 * (1/2 : ℝ) ^ (k + 1) := by
        right; ring
      have h2 : (1 - (1/2 : ℝ) ^ (k + 1) - (1 - 1/2) ^ (k + 1)) * (1/2)
                = 1/2 - (1/2 : ℝ) ^ (k + 1) := by
        have : (1 : ℝ) - 1/2 = 1/2 := by norm_num
        rw [this]
        ring
      linarith [h2]
