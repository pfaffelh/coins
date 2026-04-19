/-
  Optimal.lean — Optimal winning probability w(p,n) defined by the Bellman
  equation (Definition 1.1, eq:bellman in the manuscript), and proof that
  w(1/2,n) = 1/2 (Theorem 2.1, Step 1).
-/
import Mathlib
import CoinsLean.Strategies

open Finset BigOperators Nat

/-- Optimal winning probability defined by the Bellman equation. -/
noncomputable def w (p : ℝ) : ℕ → ℝ
  | 0     => 1
  | n + 1 =>
    p ^ (n + 1) +
      ∑ j ∈ (Ico 1 (n + 1)).attach,
        (Nat.choose (n + 1) j.val : ℝ) * p ^ (n + 1 - j.val) * (1 - p) ^ j.val *
          ((Ico j.val (n + 1)).attach.sup'
            ⟨⟨j.val, by
              have := (mem_Ico.mp j.prop)
              exact mem_Ico.mpr ⟨le_refl _, this.2⟩⟩, mem_attach _ _⟩
            (fun m => w p m.val))
  termination_by n => n
  decreasing_by
    have hm := mem_Ico.mp m.prop
    omega

/-- Suffix-maximum of `w p` over `[j, n)`; returns `0` when `j ≥ n`. -/
noncomputable def suffMax (p : ℝ) (j n : ℕ) : ℝ :=
  if h : j < n then
    (Ico j n).attach.sup'
      ⟨⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩, mem_attach _ _⟩
      (fun m => w p m.val)
  else 0

theorem w_zero (p : ℝ) : w p 0 = 1 := by
  show w p 0 = 1
  rw [w]

/-- The Bellman equation in plain form. -/
theorem w_succ (p : ℝ) (n : ℕ) :
    w p (n + 1) =
      p ^ (n + 1) +
        ∑ j ∈ Ico 1 (n + 1),
          (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
            suffMax p j (n + 1) := by
  show w p (n + 1) = _
  rw [w]
  congr 1
  rw [← Finset.sum_attach (Ico 1 (n + 1))
        (fun j => (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
                  suffMax p j (n + 1))]
  apply Finset.sum_congr rfl
  intro j _
  have hj := mem_Ico.mp j.prop
  have hjlt : j.val < n + 1 := hj.2
  unfold suffMax
  rw [dif_pos hjlt]

/-- If every value of `w p` on `[j, n)` equals `c`, then the suffix-max equals `c`. -/
theorem suffMax_const (p : ℝ) (j n : ℕ) (h : j < n) (c : ℝ)
    (hc : ∀ m ∈ Ico j n, w p m = c) :
    suffMax p j n = c := by
  unfold suffMax
  rw [dif_pos h]
  apply le_antisymm
  · apply Finset.sup'_le
    intro m _
    exact (hc m.val m.prop).le
  · have hmem : (⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩ : (Ico j n)) ∈ (Ico j n).attach :=
      mem_attach _ _
    have hle := Finset.le_sup' (s := (Ico j n).attach)
                  (f := fun m : (Ico j n) => w p m.val) hmem
    rw [hc j (mem_Ico.mpr ⟨le_refl _, h⟩)] at hle
    exact hle

/-- ∑_{j ∈ Ico 1 (n+1)} C(n+1,j) = 2^{n+1} - 2. -/
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
  have step1 : (2 ^ (n + 1) - 2) * (1/2 : ℝ) ^ (n + 2) =
      1/2 - (1/2 : ℝ) ^ (n + 1) := by
    have : (1/2 : ℝ) ^ (n + 2) = (1/2) ^ (n + 1) * (1/2) := by rw [pow_succ]
    rw [this]; nlinarith
  linarith

/-- w(1/2, n) = 1/2 for every n ≥ 1 (Theorem 2.1, Step 1). -/
theorem w_half : ∀ n : ℕ, 1 ≤ n → w (1/2 : ℝ) n = 1/2 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => omega
    | n + 1 =>
      intro _
      rw [w_succ]
      have hsuff : ∀ j ∈ Ico 1 (n + 1),
          suffMax (1/2 : ℝ) j (n + 1) = 1/2 := by
        intro j hj
        have hjr := mem_Ico.mp hj
        apply suffMax_const _ _ _ (by omega : j < n + 1)
        intro m hm
        have hmr := mem_Ico.mp hm
        exact ih m (by omega) (by omega)
      have step : ∀ j ∈ Ico 1 (n + 1),
          (Nat.choose (n + 1) j : ℝ) * (1/2 : ℝ) ^ (n + 1 - j) * (1 - 1/2) ^ j *
              suffMax (1/2 : ℝ) j (n + 1) =
          (Nat.choose (n + 1) j : ℝ) * (1/2 : ℝ) ^ (n + 2) := by
        intro j hj
        rw [hsuff j hj, show (1 : ℝ) - 1/2 = 1/2 from by norm_num]
        have hjle : j ≤ n := by have := mem_Ico.mp hj; omega
        have key : (1/2 : ℝ) ^ (n + 1 - j) * (1/2) ^ j = (1/2) ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        calc (↑((n + 1).choose j) : ℝ) * (1/2) ^ (n + 1 - j) * (1/2) ^ j * (1/2)
            = ↑((n + 1).choose j) * ((1/2) ^ (n + 1 - j) * (1/2) ^ j) * (1/2) := by ring
          _ = ↑((n + 1).choose j) * (1/2) ^ (n + 1) * (1/2) := by rw [key]
          _ = ↑((n + 1).choose j) * (1/2) ^ (n + 2) := by
              rw [show n + 2 = (n + 1) + 1 from by omega, pow_succ]; ring
      rw [sum_congr rfl step, ← Finset.sum_mul, choose_sum_Ico, half_pow_arith]
