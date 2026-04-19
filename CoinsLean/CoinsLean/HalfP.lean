/-
  HalfP.lean — Proof that b(1/2, n) = 1/2 for every n ≥ 1.
-/
import CoinsLean.Bellman

open Finset BigOperators Nat

/-- Helper: ∑_{j ∈ Ico 1 (n+1)} C(n+1,j) = 2^{n+1} - 2. -/
private lemma choose_sum_Ico (n : ℕ) :
    (∑ j ∈ Ico 1 (n + 1), (Nat.choose (n + 1) j : ℝ)) = 2 ^ (n + 1) - 2 := by
  have total : (∑ j ∈ range (n + 2), (Nat.choose (n + 1) j : ℝ)) = 2 ^ (n + 1) := by
    exact_mod_cast Nat.sum_range_choose (n + 1)
  rw [sum_range_succ, Nat.choose_self] at total
  have hsplit : range (n + 1) = {0} ∪ Ico 1 (n + 1) := by
    ext j; simp [mem_range, mem_Ico]; omega
  rw [hsplit, sum_union] at total
  · simp only [sum_singleton, Nat.choose_zero_right, Nat.cast_one] at total; linarith
  · simp

/-- Key arithmetic fact: (1/2)^{n+1} + (2^{n+1} - 2) * (1/2)^{n+2} = 1/2. -/
private lemma half_pow_arith (n : ℕ) :
    (1/2 : ℝ) ^ (n + 1) + (2 ^ (n + 1) - 2) * (1/2 : ℝ) ^ (n + 2) = 1/2 := by
  have h2 : (2 : ℝ) ^ (n + 1) * (1/2 : ℝ) ^ (n + 1) = 1 := by
    rw [show (1/2 : ℝ) = 2⁻¹ from by norm_num, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))]
  -- (1/2)^{n+2} = (1/2)^{n+1} * (1/2)
  -- (2^{n+1} - 2) * (1/2)^{n+1} * (1/2) = (2^{n+1} * (1/2)^{n+1} - 2 * (1/2)^{n+1}) * (1/2)
  --   = (1 - 2 * (1/2)^{n+1}) * (1/2) = 1/2 - (1/2)^{n+1}
  -- So total = (1/2)^{n+1} + 1/2 - (1/2)^{n+1} = 1/2
  have step1 : (2 ^ (n + 1) - 2) * (1/2 : ℝ) ^ (n + 2) =
      1/2 - (1/2 : ℝ) ^ (n + 1) := by
    have : (1/2 : ℝ) ^ (n + 2) = (1/2) ^ (n + 1) * (1/2) := by
      rw [pow_succ]
    rw [this]
    nlinarith
  linarith

/-- b(1/2, n) = 1/2 for every n ≥ 1. -/
theorem b_half : ∀ n : ℕ, 1 ≤ n → b (1/2 : ℝ) n = 1/2 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | n + 1 =>
      intro _
      rw [b_succ]
      have hb : ∀ j ∈ Ico 1 (n + 1), b (1/2 : ℝ) j = 1/2 := by
        intro j hj
        exact ih j (mem_Ico.mp hj).2 (mem_Ico.mp hj).1
      -- Simplify summands
      have step : ∀ j ∈ Ico 1 (n + 1),
          (Nat.choose (n + 1) j : ℝ) * (1/2 : ℝ) ^ (n + 1 - j) * (1 - 1/2) ^ j *
            b (1/2 : ℝ) j =
          (Nat.choose (n + 1) j : ℝ) * (1/2 : ℝ) ^ (n + 2) := by
        intro j hj
        rw [hb j hj, show (1 : ℝ) - 1/2 = 1/2 from by norm_num]
        have hj_le : j ≤ n := by linarith [(mem_Ico.mp hj).2]
        have key : (1/2 : ℝ) ^ (n + 1 - j) * (1/2) ^ j = (1/2) ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        calc (↑((n + 1).choose j) : ℝ) * (1/2) ^ (n + 1 - j) * (1/2) ^ j * (1/2)
            = ↑((n + 1).choose j) * ((1/2) ^ (n + 1 - j) * (1/2) ^ j) * (1/2) := by ring
          _ = ↑((n + 1).choose j) * (1/2) ^ (n + 1) * (1/2) := by rw [key]
          _ = ↑((n + 1).choose j) * (1/2) ^ (n + 2) := by
              rw [show n + 2 = (n + 1) + 1 from by omega, pow_succ]; ring
      rw [sum_congr rfl step, ← Finset.sum_mul, choose_sum_Ico, half_pow_arith]
