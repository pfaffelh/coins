/-
  Above.lean — The case p > 1/2 (Theorem 3.1 in the manuscript).
  Joint strong induction on n ≥ 2:
    (i)   w(p,n)   > w(p,n-1)
    (ii)  w(p,n-1) * (p^n + (1-p)^n) < p^n
    (iii) w(p,n)   = a(p,n)
-/
import Mathlib
import CoinsLean.Optimal

open Finset BigOperators Nat

/-- ∑_{j=1}^{n-1} C(n,j) p^{n-j} (1-p)^j = 1 - p^n - (1-p)^n  (for n ≥ 1). -/
theorem binom_sum_middle (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Ico 1 n, (Nat.choose n j : ℝ) * p ^ (n - j) * (1 - p) ^ j) =
    1 - p ^ n - (1 - p) ^ n := by
  have htotal : (∑ j ∈ range (n + 1),
      (Nat.choose n j : ℝ) * p ^ (n - j) * (1 - p) ^ j) = 1 := by
    calc (∑ j ∈ range (n + 1), (Nat.choose n j : ℝ) * p ^ (n - j) * (1 - p) ^ j)
        = ∑ k ∈ range (n + 1), (1 - p) ^ k * p ^ (n - k) * (Nat.choose n k : ℝ) := by
            apply Finset.sum_congr rfl; intros j _; ring
      _ = ((1 - p) + p) ^ n := (add_pow (1 - p) p n).symm
      _ = 1 := by rw [show (1 - p) + p = (1 : ℝ) from by ring]; exact one_pow _
  -- Split range (n+1) = {0} ∪ Ico 1 n ∪ {n} (n ≥ 1).
  have hsplit : range (n + 1) = insert 0 (insert n (Ico 1 n)) := by
    ext j; simp only [mem_range, mem_insert, mem_Ico]; omega
  have h0n : 0 ∉ insert n (Ico 1 n) := by simp [mem_Ico]; omega
  have hn_in : n ∉ Ico 1 n := by simp [mem_Ico]
  rw [hsplit, sum_insert h0n, sum_insert hn_in] at htotal
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.choose_self,
             Nat.sub_zero, pow_zero, mul_one, one_mul, Nat.sub_self] at htotal
  linarith

/-- 1 - p^n - (1-p)^n > 0 when n ≥ 2 and 0 < p < 1. -/
private lemma binom_middle_pos (p : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hp_pos : 0 < p) (hp1 : p < 1) :
    0 < 1 - p ^ n - (1 - p) ^ n := by
  have hq_pos : 0 < 1 - p := by linarith
  rw [← binom_sum_middle p n (by omega)]
  apply Finset.sum_pos
  · intro j hj
    have hj' := mem_Ico.mp hj
    have hcj : 0 < (Nat.choose n j : ℝ) := by
      have : 0 < Nat.choose n j := Nat.choose_pos (by omega)
      exact_mod_cast this
    positivity
  · refine ⟨1, ?_⟩; simp [mem_Ico]; omega

/-- Suffix-max equals top value when w is monotone on [1, n]. -/
private lemma suffMax_eq_top (p : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hmono : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n → w p m₁ ≤ w p m₂)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    suffMax p j (n + 1) = w p n := by
  unfold suffMax
  rw [dif_pos (by omega : j < n + 1)]
  apply le_antisymm
  · apply Finset.sup'_le
    intro m _
    have hm := mem_Ico.mp m.prop
    exact hmono m.val n (by omega) (by omega) (by omega)
  · have hmem : (⟨n, mem_Ico.mpr ⟨hjn, by omega⟩⟩ : (Ico j (n + 1))) ∈
        (Ico j (n + 1)).attach := mem_attach _ _
    exact Finset.le_sup' (s := (Ico j (n + 1)).attach)
            (f := fun m : (Ico j (n + 1)) => w p m.val) hmem

lemma w_one (p : ℝ) : w p 1 = p := by
  have h := w_succ p 0
  simp only [Nat.zero_add, pow_one, Ico_self, sum_empty, add_zero] at h
  exact h

/-- Pointwise step → chained monotonicity. -/
private lemma chain_mono (p : ℝ) (n : ℕ)
    (hstep : ∀ k : ℕ, 1 ≤ k → k ≤ n → w p k ≤ w p (k + 1)) :
    ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n + 1 → w p m₁ ≤ w p m₂ := by
  intro m₁ m₂ h₁
  induction m₂ with
  | zero => intros h₂ _; omega
  | succ m ih =>
    intros h₂ h₃
    rcases Nat.lt_or_ge m₁ (m + 1) with hlt | hge
    · -- m₁ ≤ m, chain via ih and step at m
      have hh : m₁ ≤ m := by omega
      have h_step := hstep m (by omega) (by omega)
      exact (ih hh (by omega)).trans h_step
    · -- m₁ = m + 1
      rw [show m₁ = m + 1 from by omega]

/-- Recursion identity for w at the inductive step. -/
private lemma w_rec_of_mono (p : ℝ) (n : ℕ)
    (hmono : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n + 1 → w p m₁ ≤ w p m₂) :
    w p (n + 2) = p ^ (n + 2) +
        (1 - p ^ (n + 2) - (1 - p) ^ (n + 2)) * w p (n + 1) := by
  have h := w_succ p (n + 1)
  rw [show (n + 1 + 1) = n + 2 from rfl] at h
  rw [h]
  have hsuff : ∀ j ∈ Ico 1 (n + 2), suffMax p j (n + 2) = w p (n + 1) :=
    fun j hj => suffMax_eq_top p (n + 1) (by omega) hmono j (mem_Ico.mp hj).1 (by
      have := mem_Ico.mp hj; omega)
  have hstep : ∀ j ∈ Ico 1 (n + 2),
      (Nat.choose (n + 2) j : ℝ) * p ^ (n + 2 - j) * (1 - p) ^ j *
          suffMax p j (n + 2) =
      (Nat.choose (n + 2) j : ℝ) * p ^ (n + 2 - j) * (1 - p) ^ j *
          w p (n + 1) := fun j hj => by rw [hsuff j hj]
  rw [sum_congr rfl hstep, ← Finset.sum_mul,
      binom_sum_middle p (n + 2) (by omega)]

/-- The joint induction: (i), (ii), (iii) for n ≥ 2. -/
theorem above_half (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt_one : p < 1) :
    ∀ n : ℕ, 2 ≤ n →
      w p (n - 1) < w p n ∧
      w p (n - 1) * (p ^ n + (1 - p) ^ n) < p ^ n ∧
      w p n = a p n := by
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < 1 - p := by linarith
  have hpq : 1 - p < p := by linarith
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    -- IH: w_k = a_k for 1 ≤ k ≤ n' + 1.
    have hwa_lo : ∀ k : ℕ, 1 ≤ k → k ≤ n' + 1 → w p k = a p k := by
      intro k hk1 hkn
      rcases lt_or_eq_of_le hk1 with hlt | heq
      · exact (ih k (by omega) hlt).2.2
      · rw [← heq, w_one]; exact (a_one p).symm
    -- Pointwise mono step on [1, n'].
    have hstep_mono : ∀ k : ℕ, 1 ≤ k → k ≤ n' → w p k ≤ w p (k + 1) := by
      intro k hk1 hkn
      have hii := (ih (k + 1) (by omega) (by omega)).1
      rw [show k + 1 - 1 = k from by omega] at hii
      exact hii.le
    have hmono : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ n' + 1 →
        w p m₁ ≤ w p m₂ := chain_mono p n' hstep_mono
    have hw_eq : w p (n' + 2) =
        p ^ (n' + 2) + (1 - p ^ (n' + 2) - (1 - p) ^ (n' + 2)) * w p (n' + 1) :=
      w_rec_of_mono p n' hmono
    -- (iii)
    have h_eq_a : w p (n' + 2) = a p (n' + 2) := by
      rw [hw_eq, a_succ, hwa_lo (n' + 1) (by omega) (le_refl _)]
    -- 0 ≤ w p (n'+1)
    have hw_nn : 0 ≤ w p (n' + 1) := by
      have := hmono 1 (n' + 1) (le_refl _) (by omega) (le_refl _)
      rw [w_one] at this; linarith
    -- Positivity 1 - p^{n'+2} - q^{n'+2} > 0.
    have hbinom_pos : 0 < 1 - p ^ (n' + 2) - (1 - p) ^ (n' + 2) :=
      binom_middle_pos p (n' + 2) (by omega) hp_pos hp_lt_one
    -- The key bound on w(n'+1) at the n'+2 binomial level.
    -- (Equivalent to (ii) at n'+2; we will derive it via the algebraic shift.)
    have hii_curr : w p (n' + 1) * (p ^ (n' + 2) + (1 - p) ^ (n' + 2)) < p ^ (n' + 2) := by
      rcases Nat.eq_zero_or_pos n' with hn0 | hn0
      · -- n' = 0: prove directly. Goal: w(1) * (p^2 + (1-p)^2) < p^2.
        subst hn0
        rw [w_one]
        have h1 : p ^ 2 + (1 - p) ^ 2 < p := by nlinarith [sq_nonneg (2*p - 1)]
        have h2 : p * (p ^ 2 + (1 - p) ^ 2) < p * p := mul_lt_mul_of_pos_left h1 hp_pos
        have hpp : p * p = p ^ (0 + 2) := by ring
        have hgoal_eq : p * (p ^ (0 + 2) + (1 - p) ^ (0 + 2)) = p * (p ^ 2 + (1 - p) ^ 2) := by ring
        linarith [h2, hpp, hgoal_eq]
      · -- n' ≥ 1: use IH (ii) at n'+1 and the algebraic shift.
        have hii_prev := (ih (n' + 1) (by omega) (by omega)).2.1
        rw [show n' + 1 - 1 = n' from by omega] at hii_prev
        -- Recursion at n'+1: w(n'+1) = p^{n'+1} + (1 - p^{n'+1} - q^{n'+1}) * w(n').
        have hmono' : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ (n' - 1) + 1 →
            w p m₁ ≤ w p m₂ := fun m₁ m₂ h₁ h₂ h₃ =>
          hmono m₁ m₂ h₁ h₂ (by omega)
        have hw_eq_prev : w p (n' + 1) =
            p ^ (n' + 1) + (1 - p ^ (n' + 1) - (1 - p) ^ (n' + 1)) * w p n' := by
          have := w_rec_of_mono p (n' - 1) hmono'
          rw [show n' - 1 + 2 = n' + 1 from by omega,
              show n' - 1 + 1 = n' from by omega] at this
          exact this
        -- Set A = p^{n'+1}, B = q^{n'+1}, C = p^{n'+2} = pA, D = q^{n'+2} = qB.
        set A : ℝ := p ^ (n' + 1) with hA_def
        set B : ℝ := (1 - p) ^ (n' + 1) with hB_def
        have hA_pos : 0 < A := pow_pos hp_pos _
        have hB_pos : 0 < B := pow_pos hq_pos _
        have hAB_pos : 0 < A + B := by linarith
        have hbinom_prev_pos : 0 < 1 - A - B := by
          rw [hA_def, hB_def]
          exact binom_middle_pos p (n' + 1) (by omega) hp_pos hp_lt_one
        have h_wn : w p n' * (A + B) < A := by rw [hA_def, hB_def]; exact hii_prev
        -- Goal becomes: w(n'+1) * (pA + qB) < pA.
        have hCe : p ^ (n' + 2) = p * A := by rw [hA_def, pow_succ]; ring
        have hDe : (1 - p) ^ (n' + 2) = (1 - p) * B := by rw [hB_def, pow_succ]; ring
        rw [hw_eq_prev, hCe, hDe]
        -- Algebraic identity (verified by `ring`):
        --   ((A + (1-A-B)*w_n) * (pA + qB) - pA) * (A + B)
        --   = AB(q-p) + (1-A-B)*(pA+qB)*(w_n*(A+B) - A)
        have hid : ((A + (1 - A - B) * w p n') * (p * A + (1 - p) * B) - p * A) * (A + B) =
            A * B * ((1 - p) - p) +
            (1 - A - B) * (p * A + (1 - p) * B) * (w p n' * (A + B) - A) := by ring
        have h_t1 : A * B * ((1 - p) - p) < 0 :=
          mul_neg_of_pos_of_neg (mul_pos hA_pos hB_pos) (by linarith)
        have hCDpos : 0 < p * A + (1 - p) * B := by positivity
        have h_t2 : (1 - A - B) * (p * A + (1 - p) * B) * (w p n' * (A + B) - A) ≤ 0 := by
          have hfac : 0 ≤ (1 - A - B) * (p * A + (1 - p) * B) := by positivity
          have hdiff : w p n' * (A + B) - A ≤ 0 := by linarith
          exact mul_nonpos_of_nonneg_of_nonpos hfac hdiff
        have hsum_neg :
            ((A + (1 - A - B) * w p n') * (p * A + (1 - p) * B) - p * A) * (A + B) < 0 := by
          rw [hid]; linarith
        nlinarith [hsum_neg, hAB_pos]
    -- Now (i) and (ii) at level n' + 2.
    rw [show (n' + 2) - 1 = n' + 1 from by omega]
    refine ⟨?_, hii_curr, h_eq_a⟩
    -- (i): w(n'+1) < w(n'+2). Use hw_eq + hii_curr.
    rw [hw_eq]
    nlinarith [hii_curr, pow_pos hp_pos (n' + 2), pow_pos hq_pos (n' + 2),
               hbinom_pos, hw_nn]
