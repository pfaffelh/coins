/-
  Perturbation.lean — Section 4 of the manuscript: deficit Δ_{n,p} := 1/2 - w_{n,p}.
  We give the basic definition and its consequences derived from earlier results
  (Δ = 0 at p = 1/2, Δ < 0 for p > 1/2). The full perturbation expansion in
  δ = 1/2 - p (Propositions 4.4–4.9, Theorem 4.10) is left for future work.
-/
import Mathlib
import CoinsLean.Optimal
import CoinsLean.Above

open Finset BigOperators Nat

/-- Deficit (Definition 4.1): Δ_{n,p} := 1/2 - w_{n,p}. -/
noncomputable def deficit (p : ℝ) (n : ℕ) : ℝ := 1/2 - w p n

theorem deficit_zero (p : ℝ) : deficit p 0 = -1/2 := by
  unfold deficit; rw [w_zero]; norm_num

/-- At the fair coin, the deficit vanishes for every n ≥ 1 (Theorem 2.1 corollary). -/
theorem deficit_half (n : ℕ) (hn : 1 ≤ n) : deficit (1/2 : ℝ) n = 0 := by
  unfold deficit; rw [w_half n hn]; ring

/-- For p > 1/2, the deficit is strictly negative for n ≥ 1
    (since w(p,n) > 1/2 by monotonicity from above_half). -/
theorem deficit_neg_of_above (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp1 : p < 1) :
    ∀ n : ℕ, 1 ≤ n → deficit p n < 0 := by
  intro n hn
  unfold deficit
  -- For n = 1: w(p,1) = p > 1/2.
  -- For n ≥ 2: by above_half (i), w is strictly increasing, so w(p,n) > w(p,1) = p > 1/2.
  rcases eq_or_lt_of_le hn with heq | hlt
  · rw [← heq, w_one]; linarith
  · -- n ≥ 2
    have h2 : 2 ≤ n := hlt
    -- Chain w(1) < w(2) < ... < w(n) using above_half (i).
    have hchain : ∀ k : ℕ, 2 ≤ k → k ≤ n → w p 1 < w p k := by
      intro k hk hkn
      induction k, hk using Nat.le_induction with
      | base =>
        have := (above_half p hp hp1 2 (le_refl _)).1
        rw [show (2 : ℕ) - 1 = 1 from rfl] at this
        exact this
      | succ k hk ih =>
        have hknprev : k ≤ n := by omega
        have hih := ih hknprev
        have hstep := (above_half p hp hp1 (k + 1) (by omega)).1
        rw [show (k + 1) - 1 = k from by omega] at hstep
        exact hih.trans hstep
    have := hchain n h2 (le_refl _)
    rw [w_one] at this
    linarith

/-- Convention: c_n is the leading coefficient of Δ_{n, 1/2 - δ} as δ → 0⁺.
    We define c_n directly via the (finite) recursion of Proposition 4.4:
        c_1 = 1,
        c_n = n / 2^{n-1} + (1 / 2^n) * ∑_{j=1}^{n-1} C(n,j) * (min_{j ≤ m ≤ n-1} c_m). -/
noncomputable def c : ℕ → ℝ
  | 0     => 0          -- not used; the definition starts at n = 1
  | 1     => 1
  | n + 2 =>
    ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) +
      (1 / (2 : ℝ) ^ (n + 2)) *
        ∑ j ∈ (Ico 1 (n + 2)).attach,
          (Nat.choose (n + 2) j.val : ℝ) *
            ((Ico j.val (n + 2)).attach.inf'
              ⟨⟨j.val, by
                have := (mem_Ico.mp j.prop)
                exact mem_Ico.mpr ⟨le_refl _, this.2⟩⟩, mem_attach _ _⟩
              (fun m => c m.val))
  termination_by n => n
  decreasing_by
    have hm := mem_Ico.mp m.prop
    omega

theorem c_zero : c 0 = 0 := by show c 0 = 0; rw [c]
theorem c_one : c 1 = 1 := by show c 1 = 1; rw [c]

/-- Suffix-minimum of `c` over indices `[j, n)`; returns `0` when `j ≥ n`. -/
noncomputable def suffMin (j n : ℕ) : ℝ :=
  if h : j < n then
    (Ico j n).attach.inf'
      ⟨⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩, mem_attach _ _⟩
      (fun m => c m.val)
  else 0

/-- Singleton suffix-min: `suffMin n (n+1) = c n`. -/
theorem suffMin_singleton (n : ℕ) : suffMin n (n + 1) = c n := by
  unfold suffMin
  rw [dif_pos (Nat.lt_succ_self n)]
  apply le_antisymm
  · exact Finset.inf'_le _
      (mem_attach _ ⟨n, mem_Ico.mpr ⟨le_refl _, Nat.lt_succ_self _⟩⟩)
  · apply Finset.le_inf'
    intro m _
    have hm := mem_Ico.mp m.prop
    have hval : m.val = n := by omega
    rw [hval]

/-- The c-recursion in plain (non-attach) form for n ≥ 2. -/
theorem c_succ (n : ℕ) :
    c (n + 2) = ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) +
      (1 / (2 : ℝ) ^ (n + 2)) *
        ∑ j ∈ Ico 1 (n + 2),
          (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2) := by
  show c (n + 2) = _
  rw [c]
  congr 1
  congr 1
  rw [← Finset.sum_attach (Ico 1 (n + 2))
        (fun j => (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2))]
  apply Finset.sum_congr rfl
  intro j _
  have hj := mem_Ico.mp j.prop
  have hjlt : j.val < n + 2 := hj.2
  unfold suffMin
  rw [dif_pos hjlt]

/-- Example 4.5, first value: c_2 = 3/2. -/
theorem c_two : c 2 = 3/2 := by
  change c (0 + 2) = 3/2
  rw [c_succ]
  have hIco : Ico 1 (0 + 2) = ({1} : Finset ℕ) := by
    ext x; simp only [mem_Ico, mem_singleton]; omega
  rw [hIco, sum_singleton]
  rw [show (0 + 2 : ℕ) = 1 + 1 from rfl, suffMin_singleton, c_one]
  norm_num

/-- Splitting suffix-min: `suffMin n m = min (c n) (suffMin (n+1) m)` when `n+1 < m`. -/
theorem suffMin_split (n m : ℕ) (h : n + 1 < m) :
    suffMin n m = min (c n) (suffMin (n + 1) m) := by
  unfold suffMin
  rw [dif_pos (by omega : n < m), dif_pos (by omega : n + 1 < m)]
  apply le_antisymm
  · apply le_min
    · exact Finset.inf'_le _
        (mem_attach _ ⟨n, mem_Ico.mpr ⟨le_refl _, by omega⟩⟩)
    · apply Finset.le_inf'
      intro k _
      have hk := mem_Ico.mp k.prop
      exact Finset.inf'_le _
        (mem_attach _ ⟨k.val, mem_Ico.mpr ⟨by omega, hk.2⟩⟩)
  · apply Finset.le_inf'
    intro m' _
    have hm' := mem_Ico.mp m'.prop
    rcases (show m'.val = n ∨ n + 1 ≤ m'.val by omega) with heq | hge
    · rw [heq]; exact min_le_left _ _
    · refine min_le_right _ _ |>.trans ?_
      exact Finset.inf'_le _
        (mem_attach _ ⟨m'.val, mem_Ico.mpr ⟨hge, hm'.2⟩⟩)

/-- Two-element suffix-min: `suffMin n (n+2) = min (c n) (c (n+1))`. -/
theorem suffMin_pair (n : ℕ) : suffMin n (n + 2) = min (c n) (c (n + 1)) := by
  unfold suffMin
  rw [dif_pos (by omega : n < n + 2)]
  apply le_antisymm
  · apply le_min
    · exact Finset.inf'_le _
        (mem_attach _ ⟨n, mem_Ico.mpr ⟨le_refl _, by omega⟩⟩)
    · exact Finset.inf'_le _
        (mem_attach _ ⟨n + 1, mem_Ico.mpr ⟨by omega, by omega⟩⟩)
  · apply Finset.le_inf'
    intro m _
    have hm := mem_Ico.mp m.prop
    rcases (show m.val = n ∨ m.val = n + 1 by omega) with h | h
    · rw [h]; exact min_le_left _ _
    · rw [h]; exact min_le_right _ _

/-- Example 4.5, second value: c_3 = 27/16. -/
theorem c_three : c 3 = 27/16 := by
  change c (1 + 2) = 27/16
  rw [c_succ]
  have hIco : Ico 1 (1 + 2) = ({1, 2} : Finset ℕ) := by
    ext x; simp only [mem_Ico, mem_insert, mem_singleton]; omega
  rw [hIco, sum_insert (by simp), sum_singleton]
  -- suffMin 1 3 = min (c 1) (c 2) = min 1 (3/2) = 1
  have hs1 : suffMin 1 (1 + 2) = 1 := by
    rw [show (1 + 2 : ℕ) = 1 + 2 from rfl, suffMin_pair, c_one, c_two]
    norm_num
  -- suffMin 2 3 = suffMin 2 (2+1) = c 2 = 3/2
  have hs2 : suffMin 2 (1 + 2) = 3/2 := by
    rw [show (1 + 2 : ℕ) = 2 + 1 from rfl, suffMin_singleton, c_two]
  rw [hs1, hs2]
  norm_num

/-- Example 4.5, third value: c_4 = 111/64. -/
theorem c_four : c 4 = 111/64 := by
  change c (2 + 2) = 111/64
  rw [c_succ]
  have hIco : Ico 1 (2 + 2) = ({1, 2, 3} : Finset ℕ) := by
    ext x; simp only [mem_Ico, mem_insert, mem_singleton]; omega
  rw [hIco, sum_insert (by simp), sum_insert (by simp), sum_singleton]
  -- suffMin 1 4 = min (c 1) (min (c 2) (c 3)) = min 1 (min (3/2) (27/16)) = 1
  have hs1 : suffMin 1 (2 + 2) = 1 := by
    have h1 : suffMin 1 (2 + 2) = min (c 1) (suffMin 2 (2 + 2)) :=
      suffMin_split 1 (2 + 2) (by omega)
    have h2 : suffMin 2 (2 + 2) = min (c 2) (c 3) := suffMin_pair 2
    rw [h1, h2, c_one, c_two, c_three]; norm_num
  have hs2 : suffMin 2 (2 + 2) = 3/2 := by
    rw [suffMin_pair, c_two, c_three]; norm_num
  have hs3 : suffMin 3 (2 + 2) = 27/16 := by
    change suffMin 3 (3 + 1) = 27/16
    rw [suffMin_singleton, c_three]
  rw [hs1, hs2, hs3]
  have hc2 : (Nat.choose 4 2 : ℝ) = 6 := by
    have : Nat.choose 4 2 = 6 := by decide
    exact_mod_cast this
  rw [hc2]
  norm_num

/-- Example 4.5, fourth value: c_5 = 3555/2048. -/
theorem c_five : c 5 = 3555/2048 := by
  change c (3 + 2) = 3555/2048
  rw [c_succ]
  have hIco : Ico 1 (3 + 2) = ({1, 2, 3, 4} : Finset ℕ) := by
    ext x; simp only [mem_Ico, mem_insert, mem_singleton]; omega
  rw [hIco]
  rw [sum_insert (by simp), sum_insert (by simp), sum_insert (by simp), sum_singleton]
  have hs4 : suffMin 4 (3 + 2) = 111/64 := by
    change suffMin 4 (4 + 1) = 111/64
    rw [suffMin_singleton, c_four]
  have hs3 : suffMin 3 (3 + 2) = 27/16 := by
    change suffMin 3 (3 + 2) = 27/16
    rw [suffMin_pair, c_three, c_four]; norm_num
  have hs2 : suffMin 2 (3 + 2) = 3/2 := by
    have h1 : suffMin 2 (3 + 2) = min (c 2) (suffMin 3 (3 + 2)) :=
      suffMin_split 2 (3 + 2) (by omega)
    rw [h1, hs3, c_two]; norm_num
  have hs1 : suffMin 1 (3 + 2) = 1 := by
    have h1 : suffMin 1 (3 + 2) = min (c 1) (suffMin 2 (3 + 2)) :=
      suffMin_split 1 (3 + 2) (by omega)
    rw [h1, hs2, c_one]; norm_num
  rw [hs1, hs2, hs3, hs4]
  have hc52 : (Nat.choose 5 2 : ℝ) = 10 := by
    have : Nat.choose 5 2 = 10 := by decide
    exact_mod_cast this
  have hc53 : (Nat.choose 5 3 : ℝ) = 10 := by
    have : Nat.choose 5 3 = 10 := by decide
    exact_mod_cast this
  rw [hc52, hc53]
  norm_num
