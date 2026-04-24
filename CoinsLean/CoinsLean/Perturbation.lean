/-
  Perturbation.lean — Section 4 of the manuscript: deficit Δ_{n,p} := 1/2 - w_{n,p}.
  We give the basic definition and its consequences derived from earlier results
  (Δ = 0 at p = 1/2, Δ < 0 for p > 1/2). The full perturbation expansion in
  δ = 1/2 - p (Propositions 4.3–4.9, Theorem 4.10) is left for future work.
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
    We define c_n directly via the (finite) recursion of Proposition 4.3:
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

/-- Example 4.4, first value: c_2 = 3/2. -/
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

/-- Example 4.4, second value: c_3 = 27/16. -/
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

/-- Example 4.4, third value: c_4 = 111/64. -/
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

/-- Example 4.4, fourth value: c_5 = 3555/2048. -/
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

/-- Example 4.4, fifth value (added base case for the §4.3 joint induction):
    `c_6 = 113337/65536`. -/
theorem c_six : c 6 = 113337/65536 := by
  change c (4 + 2) = 113337/65536
  rw [c_succ]
  have hIco : Ico 1 (4 + 2) = ({1, 2, 3, 4, 5} : Finset ℕ) := by
    ext x; simp only [mem_Ico, mem_insert, mem_singleton]; omega
  rw [hIco]
  rw [sum_insert (by simp), sum_insert (by simp), sum_insert (by simp),
      sum_insert (by simp), sum_singleton]
  have hs5 : suffMin 5 (4 + 2) = 3555/2048 := by
    change suffMin 5 (5 + 1) = 3555/2048
    rw [suffMin_singleton, c_five]
  have hs4 : suffMin 4 (4 + 2) = 111/64 := by
    rw [suffMin_pair, c_four, c_five]; norm_num
  have hs3 : suffMin 3 (4 + 2) = 27/16 := by
    have h1 : suffMin 3 (4 + 2) = min (c 3) (suffMin 4 (4 + 2)) :=
      suffMin_split 3 (4 + 2) (by omega)
    rw [h1, hs4, c_three]; norm_num
  have hs2 : suffMin 2 (4 + 2) = 3/2 := by
    have h1 : suffMin 2 (4 + 2) = min (c 2) (suffMin 3 (4 + 2)) :=
      suffMin_split 2 (4 + 2) (by omega)
    rw [h1, hs3, c_two]; norm_num
  have hs1 : suffMin 1 (4 + 2) = 1 := by
    have h1 : suffMin 1 (4 + 2) = min (c 1) (suffMin 2 (4 + 2)) :=
      suffMin_split 1 (4 + 2) (by omega)
    rw [h1, hs2, c_one]; norm_num
  rw [hs1, hs2, hs3, hs4, hs5]
  have hc62 : (Nat.choose 6 2 : ℝ) = 15 := by
    have : Nat.choose 6 2 = 15 := by decide
    exact_mod_cast this
  have hc63 : (Nat.choose 6 3 : ℝ) = 20 := by
    have : Nat.choose 6 3 = 20 := by decide
    exact_mod_cast this
  have hc64 : (Nat.choose 6 4 : ℝ) = 15 := by
    have : Nat.choose 6 4 = 15 := by decide
    exact_mod_cast this
  rw [hc62, hc63, hc64]
  norm_num

/-! ### Lemma 4.6: lower bound c_m ≥ 27/16 for m ≥ 4

  The full lemma in the manuscript holds for every m ≥ 4. The proof uses the
  linear recursion (Prop 4.8), which itself relies on the collapse lemma (4.6),
  which in turn relies on Lemma 4.6 — the circle is broken in the manuscript by
  proving the polynomial bound  A_m − (27/16)·B_m  ≥ 0 directly for m ∈ {3,…,12}
  and treating m ≥ 13 with a contraction argument.

  Below we prove the two cases that follow trivially from the values computed in
  Example 4.4; the inductive bound for m ∈ {6,…,12} and the asymptotic case
  m ≥ 13 are left for future work. -/

/-! ### Proposition 4.2: deficit recursion

  Restating the Bellman equation in terms of the deficit `Δ_{n,p} := 1/2 − w_{n,p}`:
      Δ_{n+1,p} = ((1−p)^(n+1) − p^(n+1)) / 2
                 + ∑_{j=1}^{n} C(n+1,j) p^{n+1−j} (1−p)^j · (1/2 − suffMax p j (n+1)).
  Since `min Δ_m = 1/2 − max w_m`, the bracketed factor is exactly `min_{j ≤ m ≤ n} Δ_m`. -/

theorem deficit_succ (p : ℝ) (n : ℕ) :
    deficit p (n + 1) = ((1 - p) ^ (n + 1) - p ^ (n + 1)) / 2 +
      ∑ j ∈ Ico 1 (n + 1),
        (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
          (1/2 - suffMax p j (n + 1)) := by
  unfold deficit
  rw [w_succ]
  have hbinom := binom_sum_middle p (n + 1) (by omega)
  -- Split the RHS sum: ∑ C * (1/2 - suffMax) = (1/2) * ∑ C - ∑ C * suffMax.
  have hRHS_sum :
      ∑ j ∈ Ico 1 (n + 1), (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
          (1/2 - suffMax p j (n + 1))
      =
      (1/2) * (1 - p ^ (n + 1) - (1 - p) ^ (n + 1)) -
      ∑ j ∈ Ico 1 (n + 1), (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
          suffMax p j (n + 1) := by
    rw [← hbinom, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros j _; ring
  rw [hRHS_sum]
  ring

/-- Suffix-minimum of the deficit `Δ p` over `[j, n)`. Returns 0 when `j ≥ n`. -/
noncomputable def suffMinDelta (p : ℝ) (j n : ℕ) : ℝ :=
  if h : j < n then
    (Ico j n).attach.inf'
      ⟨⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩, mem_attach _ _⟩
      (fun m => deficit p m.val)
  else 0

/-- The inf of `1/2 − w` equals `1/2 − sup w`. -/
theorem suffMinDelta_eq (p : ℝ) (j n : ℕ) (h : j < n) :
    suffMinDelta p j n = 1/2 - suffMax p j n := by
  unfold suffMinDelta suffMax
  rw [dif_pos h, dif_pos h]
  apply le_antisymm
  · -- inf' deficit ≤ 1/2 − sup' w: use the sup'-achieving element.
    obtain ⟨m_max, hmax_mem, hmax_eq⟩ := Finset.exists_mem_eq_sup'
      ⟨⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩, mem_attach _ _⟩
      (fun m : (Ico j n) => w p m.val)
    rw [hmax_eq]
    have h_inf := Finset.inf'_le (s := (Ico j n).attach)
                    (f := fun m : (Ico j n) => deficit p m.val) hmax_mem
    unfold deficit at h_inf ⊢
    linarith
  · -- 1/2 − sup' w ≤ inf' deficit: bound below by each element.
    apply Finset.le_inf'
    intro m _
    have h_le := Finset.le_sup' (s := (Ico j n).attach)
                  (f := fun m : (Ico j n) => w p m.val) (mem_attach _ m)
    unfold deficit
    linarith

/-- Proposition 4.2 in deficit form (manuscript statement). -/
theorem deficit_succ' (p : ℝ) (n : ℕ) :
    deficit p (n + 1) = ((1 - p) ^ (n + 1) - p ^ (n + 1)) / 2 +
      ∑ j ∈ Ico 1 (n + 1),
        (Nat.choose (n + 1) j : ℝ) * p ^ (n + 1 - j) * (1 - p) ^ j *
          suffMinDelta p j (n + 1) := by
  rw [deficit_succ]
  apply congrArg (((1 - p) ^ (n + 1) - p ^ (n + 1)) / 2 + ·)
  apply Finset.sum_congr rfl
  intros j hj
  have hjr := mem_Ico.mp hj
  rw [suffMinDelta_eq p j (n + 1) hjr.2]

/-- Proposition 4.2 (i): for `0 < p < 1/2` and `n ≥ 1`, the deficit is positive. -/
theorem deficit_pos_of_below (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1/2) :
    ∀ n : ℕ, 1 ≤ n → 0 < deficit p n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [deficit_succ]
    have hq_pos : 0 < 1 - p := by linarith
    have hpq : p < 1 - p := by linarith
    -- First term: ((1-p)^(n'+1) - p^(n'+1)) / 2 > 0  since 1 - p > p > 0.
    have hpow_lt : p ^ (n' + 1) < (1 - p) ^ (n' + 1) :=
      pow_lt_pow_left₀ hpq hp_pos.le (by omega)
    have h_first : 0 < ((1 - p) ^ (n' + 1) - p ^ (n' + 1)) / 2 := by
      apply _root_.div_pos (by linarith) (by norm_num)
    -- Sum term: each summand ≥ 0 (the factor `1/2 - suffMax p j (n'+1)` is ≥ 0
    -- because every w p m on the suffix is < 1/2 by IH).
    have h_sum_nn : 0 ≤ ∑ j ∈ Ico 1 (n' + 1),
        (Nat.choose (n' + 1) j : ℝ) * p ^ (n' + 1 - j) * (1 - p) ^ j *
          (1/2 - suffMax p j (n' + 1)) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjr := mem_Ico.mp hj
      have h_choose : 0 ≤ (Nat.choose (n' + 1) j : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pp : 0 ≤ p ^ (n' + 1 - j) := pow_nonneg hp_pos.le _
      have h_qq : 0 ≤ (1 - p) ^ j := pow_nonneg hq_pos.le _
      have h_sufmax_le : suffMax p j (n' + 1) ≤ 1/2 := by
        unfold suffMax
        rw [dif_pos hjr.2]
        apply Finset.sup'_le
        intro m _
        have hm := mem_Ico.mp m.prop
        have h_def_pos : 0 < deficit p m.val :=
          ih m.val (by omega) (by omega)
        unfold deficit at h_def_pos
        linarith
      have h_factor : 0 ≤ 1/2 - suffMax p j (n' + 1) := by linarith
      positivity
    linarith

theorem c_four_ge : c 4 ≥ 27/16 := by rw [c_four]; norm_num

theorem c_five_ge : c 5 ≥ 27/16 := by rw [c_five]; norm_num

/-! Strict monotonicity of `c` on `{1, …, 5}` (Example 4.4). -/

theorem c_one_lt_two   : c 1 < c 2 := by rw [c_one,   c_two];   norm_num
theorem c_two_lt_three : c 2 < c 3 := by rw [c_two,   c_three]; norm_num
theorem c_three_lt_four : c 3 < c 4 := by rw [c_three, c_four];  norm_num
theorem c_four_lt_five : c 4 < c 5 := by rw [c_four,  c_five];  norm_num

/-! ### Inductive bound for n ∈ {4, …, 12}

  We give the strong-induction proof that `c n ≥ 27/16` for `4 ≤ n ≤ 12`.
  The argument bounds the c-recursion sum term-by-term:

    suffMin 1 n ≥ 1     (from c_1 = 1, c_2 = 3/2 ≥ 1, c_3 = 27/16 ≥ 1, IH for m ≥ 4)
    suffMin 2 n ≥ 3/2   (from c_2 = 3/2, c_3 = 27/16 ≥ 3/2, IH for m ≥ 4)
    suffMin j n ≥ 27/16 for j ≥ 3 (c_3 = 27/16, IH for m ≥ 4)

  Combining and using ∑ C(n,j) = 2^n - 2:
      c_n ≥ 27/16 + (3 / (16 · 2^n)) · (7n − 18 − C(n,2))
  The bracket is `≥ 0` iff `n² − 15n + 36 ≤ 0`, i.e. `3 ≤ n ≤ 12`. -/

/-- `c_n > 0` for every `n ≥ 1`. -/
theorem c_pos : ∀ n : ℕ, 1 ≤ n → 0 < c n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => rw [c_one]; norm_num
    | n + 2, _ =>
      rw [c_succ]
      have h1 : 0 < ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by
        apply _root_.div_pos
        · exact_mod_cast (by omega : 0 < n + 2)
        · positivity
      have h2 : 0 ≤ (1 / (2 : ℝ) ^ (n + 2)) *
          ∑ j ∈ Ico 1 (n + 2),
            (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2) := by
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro j hj
        have hjr := mem_Ico.mp hj
        have h_choose : 0 ≤ (Nat.choose (n + 2) j : ℝ) := by
          exact_mod_cast Nat.zero_le _
        have h_suffMin_pos : 0 ≤ suffMin j (n + 2) := by
          unfold suffMin
          rw [dif_pos hjr.2]
          apply Finset.le_inf'
          intro m _
          have hmr := mem_Ico.mp m.prop
          exact (ih m.val hmr.2 (by omega)).le
        positivity
      linarith

/-- `c_n ≥ 1` for every `n ≥ 1`. (Stronger than `c_pos`.) -/
theorem c_ge_one : ∀ n : ℕ, 1 ≤ n → 1 ≤ c n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => rw [c_one]
    | n + 2, _ =>
      rw [c_succ]
      -- Lower bound the inner sum: each suffMin ≥ 1 by IH.
      have hsuff_ge : ∀ j ∈ Ico 1 (n + 2), 1 ≤ suffMin j (n + 2) := by
        intro j hj
        have hjr := mem_Ico.mp hj
        unfold suffMin
        rw [dif_pos hjr.2]
        apply Finset.le_inf'
        intro m _
        have hmr := mem_Ico.mp m.prop
        exact ih m.val hmr.2 (by omega)
      -- ∑ C(n+2, j) * suffMin j (n+2) ≥ ∑ C(n+2, j) = 2^(n+2) - 2.
      have hsum_lb : ∑ j ∈ Ico 1 (n + 2),
          (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2)
          ≥ ∑ j ∈ Ico 1 (n + 2), (Nat.choose (n + 2) j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hcj : 0 ≤ (Nat.choose (n + 2) j : ℝ) := by exact_mod_cast Nat.zero_le _
        have h_one : 1 ≤ suffMin j (n + 2) := hsuff_ge j hj
        nlinarith
      -- ∑ C(n+2, j) for j in Ico 1 (n+2) = 2^(n+2) - 2.
      have hsum_eq : (∑ j ∈ Ico 1 (n + 2), (Nat.choose (n + 2) j : ℝ)) =
          (2 : ℝ) ^ (n + 2) - 2 := by
        have htot : (∑ j ∈ range (n + 3), (Nat.choose (n + 2) j : ℝ)) = (2 : ℝ) ^ (n + 2) := by
          exact_mod_cast Nat.sum_range_choose (n + 2)
        have hsplit : range (n + 3) = insert 0 (insert (n + 2) (Ico 1 (n + 2))) := by
          ext j; simp only [mem_range, mem_insert, mem_Ico]; omega
        have h0 : 0 ∉ insert (n + 2) (Ico 1 (n + 2)) := by simp [mem_Ico]
        have hn_in : n + 2 ∉ Ico 1 (n + 2) := by simp [mem_Ico]
        rw [hsplit, sum_insert h0, sum_insert hn_in] at htot
        simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at htot
        linarith
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (n + 2) := by positivity
      have hpow_pos' : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
      -- Now: c (n+2) ≥ (n+2)/2^(n+1) + (1/2^(n+2)) * (2^(n+2) - 2)
      --             = (n+2)/2^(n+1) + 1 - 1/2^(n+1)
      --             = 1 + (n+1)/2^(n+1) ≥ 1
      have hQ_eq : (2 : ℝ) ^ (n + 2) = 2 * (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
      have hN_ge : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ n + 2)
      -- Combine fractions: N/Qp + S/Q = (2N + S) / Q  (using Q = 2 Qp).
      rw [show ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) + 1 / (2 : ℝ) ^ (n + 2) *
            (∑ j ∈ Ico 1 (n + 2), ((Nat.choose (n + 2) j : ℕ) : ℝ) * suffMin j (n + 2))
          = (2 * ((n + 2 : ℕ) : ℝ) +
              ∑ j ∈ Ico 1 (n + 2), ((Nat.choose (n + 2) j : ℕ) : ℝ) * suffMin j (n + 2))
            / (2 : ℝ) ^ (n + 2)
          from by rw [hQ_eq]; field_simp]
      rw [le_div_iff₀ hpow_pos]
      linarith [hsum_lb, hsum_eq, hN_ge]

/-- Generic lower bound for `suffMin`: if every `c m` on `[j, n)` is at least `x`,
    then `suffMin j n ≥ x`. -/
private lemma suffMin_ge_const (j n : ℕ) (h : j < n) (x : ℝ)
    (hx : ∀ m ∈ Ico j n, x ≤ c m) :
    x ≤ suffMin j n := by
  unfold suffMin
  rw [dif_pos h]
  apply Finset.le_inf'
  intro m _
  exact hx m.val m.prop

/-- Pointwise lower bound on `c`: under the IH `c k ≥ 27/16` for `4 ≤ k < N`,
    every `c m` with `1 ≤ m < N` is `≥ 1`. -/
private lemma c_ge_one_of_ih (N : ℕ) (h_ih : ∀ k, 4 ≤ k → k < N → c k ≥ 27/16)
    (m : ℕ) (h1 : 1 ≤ m) (hN : m < N) : 1 ≤ c m := by
  rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h
  · subst h; rw [c_one]
  · subst h; rw [c_two]; norm_num
  · subst h; rw [c_three]; norm_num
  · have := h_ih m h hN; linarith

/-- Pointwise lower bound on `c`: under the IH, every `c m` with `2 ≤ m < N` is `≥ 3/2`. -/
private lemma c_ge_three_halves_of_ih (N : ℕ) (h_ih : ∀ k, 4 ≤ k → k < N → c k ≥ 27/16)
    (m : ℕ) (h2 : 2 ≤ m) (hN : m < N) : 3/2 ≤ c m := by
  rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h
  · subst h; rw [c_two]
  · subst h; rw [c_three]; norm_num
  · have := h_ih m h hN; linarith

/-- Pointwise lower bound on `c`: under the IH, every `c m` with `3 ≤ m < N` is `≥ 27/16`. -/
private lemma c_ge_27_16_of_ih (N : ℕ) (h_ih : ∀ k, 4 ≤ k → k < N → c k ≥ 27/16)
    (m : ℕ) (h3 : 3 ≤ m) (hN : m < N) : 27/16 ≤ c m := by
  rcases (show m = 3 ∨ 4 ≤ m by omega) with h | h
  · subst h; rw [c_three]
  · exact h_ih m h hN

/-- ∑_{j=3}^{n-1} C(n, j) = 2^n - 2 - n - C(n, 2) for n ≥ 3. -/
private lemma choose_sum_3_to_pred (n : ℕ) (hn : 3 ≤ n) :
    (∑ j ∈ Ico 3 n, (Nat.choose n j : ℝ)) =
    (2 : ℝ) ^ n - 2 - n - Nat.choose n 2 := by
  -- We have ∑_{j ∈ Ico 1 n} C(n,j) = 2^n - 2 (from HalfP via add_pow); split at j ∈ {1, 2}.
  have htotal : (∑ j ∈ Ico 1 n, (Nat.choose n j : ℝ)) = (2 : ℝ) ^ n - 2 := by
    -- Replicate the proof from HalfP.lean's choose_sum_Ico for direct ℕ ≥ 1.
    have htot' : (∑ j ∈ range (n + 1), (Nat.choose n j : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    have hsplit : range (n + 1) = insert 0 (insert n (Ico 1 n)) := by
      ext j; simp only [mem_range, mem_insert, mem_Ico]; omega
    have h0 : 0 ∉ insert n (Ico 1 n) := by simp [mem_Ico]; omega
    have hn_in : n ∉ Ico 1 n := by simp [mem_Ico]
    rw [hsplit, sum_insert h0, sum_insert hn_in] at htot'
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at htot'
    linarith
  have hsplit : Ico 1 n = insert 1 (insert 2 (Ico 3 n)) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  have h1 : 1 ∉ insert 2 (Ico 3 n) := by simp [mem_Ico]
  have h2 : 2 ∉ Ico 3 n := by simp [mem_Ico]
  rw [hsplit, sum_insert h1, sum_insert h2] at htotal
  simp only [Nat.choose_one_right] at htotal
  linarith

/-- Inductive step: under the IH, `c n ≥ 27/16` for `4 ≤ n ≤ 12`. -/
private lemma c_ind_step (n : ℕ) (h4 : 4 ≤ n) (h12 : n ≤ 12)
    (h_ih : ∀ k, 4 ≤ k → k < n → c k ≥ 27/16) : c n ≥ 27/16 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hn'2 : 2 ≤ n' := by omega
  have hn'10 : n' ≤ 10 := by omega
  rw [c_succ]
  -- Split Ico 1 (n'+2) into {1} ∪ {2} ∪ Ico 3 (n'+2).
  have hsplit : Ico 1 (n' + 2) = insert 1 (insert 2 (Ico 3 (n' + 2))) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  have hd1 : 1 ∉ insert 2 (Ico 3 (n' + 2)) := by simp [mem_Ico]
  have hd2 : 2 ∉ Ico 3 (n' + 2) := by simp [mem_Ico]
  rw [hsplit, sum_insert hd1, sum_insert hd2]
  -- Set abbreviations for compactness.
  set N : ℝ := ((n' + 2 : ℕ) : ℝ) with hN_def
  set C2 : ℝ := ((Nat.choose (n' + 2) 2 : ℕ) : ℝ) with hC2_def
  set Q : ℝ := (2 : ℝ) ^ (n' + 2) with hQ_def
  set Qp : ℝ := (2 : ℝ) ^ (n' + 1) with hQp_def
  have hQ_pos : 0 < Q := by rw [hQ_def]; positivity
  have hQp_pos : 0 < Qp := by rw [hQp_def]; positivity
  have hQ_eq : Q = 2 * Qp := by rw [hQ_def, hQp_def, pow_succ]; ring
  have hN_nn : 0 ≤ N := by rw [hN_def]; exact_mod_cast Nat.zero_le _
  have hC2_nn : 0 ≤ C2 := by rw [hC2_def]; exact_mod_cast Nat.zero_le _
  -- Lower bounds on each suffMin.
  have hs1 : suffMin 1 (n' + 2) ≥ 1 := by
    apply suffMin_ge_const 1 (n' + 2) (by omega) 1
    intro m hm
    have hmr := mem_Ico.mp hm
    exact c_ge_one_of_ih (n' + 2) h_ih m hmr.1 hmr.2
  have hs2 : suffMin 2 (n' + 2) ≥ 3/2 := by
    apply suffMin_ge_const 2 (n' + 2) (by omega) (3/2)
    intro m hm
    have hmr := mem_Ico.mp hm
    exact c_ge_three_halves_of_ih (n' + 2) h_ih m hmr.1 hmr.2
  have hs_rest : ∀ j ∈ Ico 3 (n' + 2), suffMin j (n' + 2) ≥ 27/16 := by
    intro j hj
    have hjr := mem_Ico.mp hj
    apply suffMin_ge_const j (n' + 2) hjr.2 (27/16)
    intro m hm
    have hmr := mem_Ico.mp hm
    exact c_ge_27_16_of_ih (n' + 2) h_ih m (by omega) hmr.2
  -- Sum bound on Ico 3 (n'+2).
  have hsum_3 : (∑ j ∈ Ico 3 (n' + 2),
      ((Nat.choose (n' + 2) j : ℕ) : ℝ) * suffMin j (n' + 2)) ≥
      (27/16 : ℝ) * ∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hcj : 0 ≤ ((Nat.choose (n' + 2) j : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    have := hs_rest j hj
    nlinarith [this, hcj]
  -- Identity for the binomial sum: ∑_{j ∈ Ico 3} C(n+2, j) = Q - 2 - N - C2.
  have hsum_eq : (∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ)) = Q - 2 - N - C2 := by
    rw [hQ_def, hN_def, hC2_def]; exact choose_sum_3_to_pred (n' + 2) (by omega)
  -- C(n+2, 1) = n+2.
  have hc1 : ((Nat.choose (n' + 2) 1 : ℕ) : ℝ) = N := by
    rw [hN_def, show Nat.choose (n' + 2) 1 = n' + 2 from Nat.choose_one_right _]
  -- Polynomial inequality 7N - 18 - C2 ≥ 0 (the key fact, holds for n' + 2 ∈ {4,…,12}).
  have hpoly : 7 * N - 18 - C2 ≥ 0 := by
    have key_nat : 7 * (n' + 2) ≥ 18 + Nat.choose (n' + 2) 2 := by
      interval_cases n' <;> decide
    have h_cast : ((7 * (n' + 2) : ℕ) : ℝ) ≥ ((18 + Nat.choose (n' + 2) 2 : ℕ) : ℝ) := by
      exact_mod_cast key_nat
    rw [hN_def, hC2_def]
    push_cast at h_cast ⊢
    linarith
  -- Combine: lower-bound the inner sum.
  have hsum_inner_lb :
      N * suffMin 1 (n' + 2) + C2 * suffMin 2 (n' + 2) +
        ∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ) * suffMin j (n' + 2)
      ≥ N + (3/2) * C2 + (27/16) * (Q - 2 - N - C2) := by
    have h_t1 : N * 1 ≤ N * suffMin 1 (n' + 2) :=
      mul_le_mul_of_nonneg_left hs1 hN_nn
    have h_t2 : C2 * (3/2) ≤ C2 * suffMin 2 (n' + 2) :=
      mul_le_mul_of_nonneg_left hs2 hC2_nn
    have h_t3 := hsum_3
    rw [hsum_eq] at h_t3
    linarith
  -- Final calculation: the three-term goal becomes
  --   N/Qp + (1/Q) * (inner) ≥ 27/16.
  -- Multiply through by 16Q (positive); reduces to 27Q ≤ 32N + 16 * inner with inner ≥ ...
  rw [hc1]
  -- Now: N/Qp + (1/Q) * (N * sM1 + C2 * sM2 + ∑) ≥ 27/16.
  -- Combine and use the polynomial bound.
  have hge_sum :
      N * suffMin 1 (n' + 2) +
          (C2 * suffMin 2 (n' + 2) +
            ∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ) * suffMin j (n' + 2))
      ≥ N + (3/2) * C2 + (27/16) * (Q - 2 - N - C2) := by
    have := hsum_inner_lb; linarith
  -- Multiply through by Q · Qp (both positive) to clear denominators.
  -- The cleanest path: lower-bound the LHS by an expression in N, C2, Q only,
  -- then use hpoly via nlinarith.
  have hQQp_pos : 0 < Q * Qp := mul_pos hQ_pos hQp_pos
  have hQQpne : Q * Qp ≠ 0 := ne_of_gt hQQp_pos
  rw [ge_iff_le, ← sub_nonneg]
  have h_clear :
      N / Qp + 1 / Q *
        (N * suffMin 1 (n' + 2) +
          (C2 * suffMin 2 (n' + 2) +
            ∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ) * suffMin j (n' + 2)))
        - 27/16 =
      (Q * N + Qp * (N * suffMin 1 (n' + 2) +
          (C2 * suffMin 2 (n' + 2) +
            ∑ j ∈ Ico 3 (n' + 2), ((Nat.choose (n' + 2) j : ℕ) : ℝ) * suffMin j (n' + 2)))
        - 27/16 * (Q * Qp)) / (Q * Qp) := by
    field_simp
  rw [h_clear]
  apply div_nonneg _ hQQp_pos.le
  -- Now: Q * N + Qp * inner - (27/16) * Q * Qp ≥ 0
  -- Substitute Q = 2 * Qp (so Q * Qp = 2 * Qp²) and lower bound inner.
  rw [hQ_eq]
  nlinarith [hge_sum, hpoly, hQp_pos, hN_nn, hC2_nn,
             mul_pos hQp_pos hQp_pos, sq_nonneg Qp]

/-- Lemma 4.6 for `n ∈ {4, …, 12}`. -/
theorem c_ge_27_16_le_12 : ∀ n : ℕ, 4 ≤ n → n ≤ 12 → c n ≥ 27/16 := by
  intro n h4 h12
  induction n using Nat.strongRecOn with
  | _ n ih =>
    apply c_ind_step n h4 h12
    intro k hk1 hk2
    exact ih k hk2 hk1 (by omega)

/-! ## Remaining §4 lemmas (TODO)

  The lemmas below complete §4 of the manuscript. They form an interconnected
  cluster which the manuscript breaks via specific algebraic identities
  involving the constants `A_lin`, `B_lin` defined below.

  Dependency sketch:
    - `c_ge_27_16_full` (Lemma 4.6) — uses `c_linear_rec` for `m ≥ 13` and
      direct computation for `m ∈ {4, …, 12}` (already done in
      `c_ge_27_16_le_12`).
    - `c_strict_anti_from_five` (Lemma 4.7) — uses `c_linear_rec` and
      `c_ge_27_16_full`.
    - `suffMin_collapse_*` (Lemma 4.5) — uses Lemmas 4.6 and 4.7.
    - `c_linear_rec` (Prop 4.8) — uses Lemma 4.5 (collapse).
    - `c_limit_exists` (Thm 4.10) — uses Prop 4.8.
    - `deficit_first_order` (Prop 4.3) — independent (asymptotic claim).
    - `w_*` (Cor 4.11) — uses Prop 4.3 + properties of `c`. -/

/-- The constant `A_n` from the linear recursion (Prop 4.8, eq:AB). -/
noncomputable def A_lin (n : ℕ) : ℝ :=
  (n : ℝ) / (2 : ℝ) ^ (n - 1) +
    ((n : ℝ) * c 1 + (Nat.choose n 2 : ℝ) * c 2 + (Nat.choose n 3 : ℝ) * c 3) /
      (2 : ℝ) ^ n

/-- The constant `B_n` from the linear recursion (Prop 4.8, eq:AB). -/
noncomputable def B_lin (n : ℕ) : ℝ :=
  (2 + (n : ℝ) + (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ)) / (2 : ℝ) ^ n

/-- Polynomial bound used for the geometric tail of the B-series:
    For `k ≥ 13`, `k^3 ≥ 12·k^2 + 7·k + 12`. Equivalently,
    `k^2·(k-12) ≥ 7k + 12`. -/
private lemma poly_cube_bound (k : ℕ) (hk : 13 ≤ k) :
    12 * k ^ 2 + 7 * k + 12 ≤ k ^ 3 := by
  have h1 : k ^ 2 ≥ 169 := by nlinarith [hk]
  have h2 : k ^ 3 = k * k ^ 2 := by ring
  have h3 : k * k ^ 2 ≥ 13 * k ^ 2 := by nlinarith [hk, sq_nonneg k]
  nlinarith [hk, h1, h2, h3, sq_nonneg (k - 13)]

/-- Real cast of `Nat.choose n 3 = n * (n-1) * (n-2) / 6`. Holds for all `n` because
    both sides are `0` for `n ∈ {0, 1, 2}`. -/
private lemma cast_choose_three (n : ℕ) :
    ((Nat.choose n 3 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.cast_choose_two ℝ m, ih]
    push_cast
    ring

/-- Polynomial bound for the δ-series geometric ratio:
    `7·k² + 406 ≥ 127·k` for `k ≥ 14`.
    (Equivalently, `(k − 14)·(7k − 29) ≥ 0`.) -/
private lemma poly_quad_bound (k : ℕ) (hk : 14 ≤ k) :
    127 * k ≤ 7 * k ^ 2 + 406 := by
  have h1 : k ^ 2 ≥ 196 := by nlinarith [hk]
  nlinarith [hk, h1, sq_nonneg k, sq_nonneg (k - 14)]

/-- The δ sequence in real form: `δ_k = 3·(k² − 15k + 36) / (32·2^k)`. -/
private noncomputable def delta_seq (k : ℕ) : ℝ :=
  3 * ((k : ℝ) ^ 2 - 15 * (k : ℝ) + 36) / (32 * (2 : ℝ) ^ k)

/-- Geometric ratio bound for the δ-series: `δ_{k+1} ≤ (9/11) · δ_k` for `k ≥ 14`.
    The series `δ_k = 3·(k² − 15k + 36) / (32·2^k)` is increasing at k = 13
    (δ_14 = (11/10)·δ_13) but decreasing geometrically from k = 14 onward. -/
private lemma delta_ratio_bound (k : ℕ) (hk : 14 ≤ k) :
    3 * ((((k + 1 : ℕ) : ℝ)) ^ 2 - 15 * ((k + 1 : ℕ) : ℝ) + 36) / (32 * (2 : ℝ) ^ (k + 1)) ≤
      (9 / 11 : ℝ) *
        (3 * ((k : ℝ) ^ 2 - 15 * (k : ℝ) + 36) / (32 * (2 : ℝ) ^ k)) := by
  have hk_real : (14 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hquad_pos : (0 : ℝ) < (k : ℝ) ^ 2 - 15 * (k : ℝ) + 36 := by nlinarith [hk_real]
  have hpoly : (127 : ℝ) * (k : ℝ) ≤ 7 * (k : ℝ) ^ 2 + 406 := by
    exact_mod_cast poly_quad_bound k hk
  rw [show ((2 : ℝ) ^ (k + 1) : ℝ) = (2 : ℝ) ^ k * 2 from pow_succ 2 k]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * ((2 : ℝ) ^ k * 2))]
  push_cast
  rw [show (9 / 11 : ℝ) * (3 * ((k : ℝ) ^ 2 - 15 * (k : ℝ) + 36) / (32 * (2 : ℝ) ^ k)) *
        (32 * ((2 : ℝ) ^ k * 2)) =
      (9 * 6 / 11 : ℝ) * ((k : ℝ) ^ 2 - 15 * (k : ℝ) + 36) from by
    field_simp; ring]
  nlinarith [hpoly, hquad_pos, hk_real, sq_nonneg ((k : ℝ) - 14)]

/-- Generic geometric tail-sum bound: if `x_{k+1} ≤ r · x_k` for all `k ≥ a`
    with `0 ≤ r < 1` and `0 ≤ x_a`, then for any `N`,
    `∑_{k=a}^{N-1} x_k ≤ x_a / (1 - r)`. -/
private lemma geometric_sum_bound (x : ℕ → ℝ) (a : ℕ) (r : ℝ)
    (hr_nn : 0 ≤ r) (hr_lt : r < 1) (hx_nn : 0 ≤ x a)
    (hx_geo : ∀ k, a ≤ k → x (k + 1) ≤ r * x k) :
    ∀ N, ∑ k ∈ Finset.Ico a N, x k ≤ x a / (1 - r) := by
  -- Step 1: x_k ≤ x_a · r^{k-a} for k ≥ a, by induction.
  have h_term : ∀ k, a ≤ k → x k ≤ x a * r ^ (k - a) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have h1 := hx_geo m hm
      have h2 : r * x m ≤ r * (x a * r ^ (m - a)) := mul_le_mul_of_nonneg_left ih hr_nn
      have h3 : r * (x a * r ^ (m - a)) = x a * r ^ ((m + 1) - a) := by
        rw [show ((m + 1) - a : ℕ) = (m - a) + 1 from by omega, pow_succ]
        ring
      linarith
  intro N
  rcases (Nat.lt_or_ge N a) with hNa | hNa
  · have : Finset.Ico a N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    apply div_nonneg hx_nn (by linarith)
  · have h1 : ∀ k ∈ Finset.Ico a N, x k ≤ x a * r ^ (k - a) := by
      intro k hk
      have hka := (Finset.mem_Ico.mp hk).1
      exact h_term k hka
    have h_sum_le : ∑ k ∈ Finset.Ico a N, x k ≤
        ∑ k ∈ Finset.Ico a N, x a * r ^ (k - a) := Finset.sum_le_sum h1
    have h_factor : ∑ k ∈ Finset.Ico a N, x a * r ^ (k - a) =
        x a * ∑ k ∈ Finset.Ico a N, r ^ (k - a) := by rw [← Finset.mul_sum]
    have h_reindex : ∑ k ∈ Finset.Ico a N, r ^ (k - a) =
        ∑ j ∈ Finset.range (N - a), r ^ j := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    have h_geom_summable : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr_nn hr_lt
    have h_partial_le_tsum : ∑ j ∈ Finset.range (N - a), r ^ j ≤ ∑' n : ℕ, r ^ n :=
      h_geom_summable.sum_le_tsum (Finset.range (N - a))
        (fun i _ => pow_nonneg hr_nn i)
    have h_tsum : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr_nn hr_lt
    rw [h_tsum] at h_partial_le_tsum
    have h_inv : (1 - r)⁻¹ = 1 / (1 - r) := inv_eq_one_div _
    rw [h_inv] at h_partial_le_tsum
    calc ∑ k ∈ Finset.Ico a N, x k
        ≤ x a * ∑ k ∈ Finset.Ico a N, r ^ (k - a) := by rw [← h_factor]; exact h_sum_le
      _ = x a * ∑ j ∈ Finset.range (N - a), r ^ j := by rw [h_reindex]
      _ ≤ x a * (1 / (1 - r)) := mul_le_mul_of_nonneg_left h_partial_le_tsum hx_nn
      _ = x a / (1 - r) := by ring

/-- Geometric ratio bound for the B-series: `B_{k+1} ≤ (5/8) · B_k` for `k ≥ 13`.
    Equivalent to `5·f(k) − 4·f(k+1) ≥ 0`, which by direct algebra equals
    `(k³ − 12k² − 7k − 12)/6 ≥ 0` — exactly `poly_cube_bound`. -/
private lemma B_ratio_bound (k : ℕ) (hk : 13 ≤ k) :
    B_lin (k + 1) ≤ (5 / 8 : ℝ) * B_lin k := by
  unfold B_lin
  rw [Nat.cast_choose_two ℝ k, cast_choose_three k,
      Nat.cast_choose_two ℝ (k + 1), cast_choose_three (k + 1)]
  rw [pow_succ]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpoly_r : (12 : ℝ) * (k : ℝ) ^ 2 + 7 * (k : ℝ) + 12 ≤ (k : ℝ) ^ 3 := by
    exact_mod_cast poly_cube_bound k hk
  push_cast
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k * 2)]
  rw [show (5 / 8 : ℝ) * ((2 + (k : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2 +
        (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) / 6) / (2 : ℝ) ^ k) *
        ((2 : ℝ) ^ k * 2) =
      (5 / 4) * (2 + (k : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2 +
        (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) / 6) from by
    field_simp; ring]
  nlinarith [hpoly_r, hpos, sq_nonneg ((k : ℝ) - 13)]

/-- B-tail bound: `∑_{k=13}^N B_k ≤ 1/8` for all `N`. -/
private lemma B_tail_bound (N : ℕ) :
    ∑ k ∈ Finset.Ico 13 N, B_lin k ≤ (1 / 8 : ℝ) := by
  have h_nn : (0 : ℝ) ≤ B_lin 13 := by unfold B_lin; positivity
  have h_geo := geometric_sum_bound B_lin 13 (5 / 8 : ℝ)
    (by norm_num) (by norm_num) h_nn B_ratio_bound N
  -- h_geo : ∑ ≤ B_lin 13 / (1 - 5/8) = B_lin 13 · 8/3
  -- Need: B_lin 13 · 8/3 ≤ 1/8, i.e., B_lin 13 ≤ 3/64.
  have h_value : B_lin 13 = 379 / 8192 := by
    unfold B_lin
    rw [Nat.cast_choose_two ℝ 13, cast_choose_three 13]
    push_cast
    norm_num
  have h_compute : B_lin 13 / (1 - 5 / 8 : ℝ) ≤ 1 / 8 := by
    rw [h_value]; norm_num
  linarith

/-- δ-series ratio in `delta_seq` form (matches `geometric_sum_bound`'s shape). -/
private lemma delta_seq_ratio (k : ℕ) (hk : 14 ≤ k) :
    delta_seq (k + 1) ≤ (9 / 11 : ℝ) * delta_seq k := by
  unfold delta_seq
  have h := delta_ratio_bound k hk
  push_cast at h ⊢
  exact h

/-- δ-tail bound: `∑_{k=13}^N delta_seq k ≤ 1/200` for all `N`. -/
private lemma delta_tail_bound (N : ℕ) :
    ∑ k ∈ Finset.Ico 13 N, delta_seq k ≤ (1 / 200 : ℝ) := by
  -- δ_k = 3·(k²-15k+36)/(32·2^k). δ_13 = 30/262144. Increasing at k=14, decreasing thereafter.
  -- Split: ∑_{k=13}^N = δ_13 + ∑_{k=14}^N (if N ≥ 14).
  have h_nn14 : (0 : ℝ) ≤ delta_seq 14 := by
    unfold delta_seq
    have : (0 : ℝ) ≤ 3 * (((14 : ℕ) : ℝ) ^ 2 - 15 * ((14 : ℕ) : ℝ) + 36) := by push_cast; norm_num
    positivity
  rcases (Nat.lt_or_ge N 14) with hN | hN
  · -- N ≤ 13: sum is empty (or has only k = 13 if N = 14, but here N < 14 so N ≤ 13).
    rcases (Nat.lt_or_ge N 13) with hN13 | hN13
    · have : Finset.Ico 13 N = ∅ := Finset.Ico_eq_empty (by omega)
      rw [this, Finset.sum_empty]; norm_num
    · -- 13 ≤ N < 14, so N = 13. Sum = ∅.
      have hN_eq : N = 13 := by omega
      subst hN_eq
      simp [Finset.Ico_self]
  · -- N ≥ 14: split.
    have h_split : Finset.Ico 13 N = insert 13 (Finset.Ico 14 N) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have h_no_13 : 13 ∉ Finset.Ico 14 N := by simp [Finset.mem_Ico]
    rw [h_split, Finset.sum_insert h_no_13]
    -- ∑ = δ_13 + ∑_{k ∈ Ico 14 N} δ_k
    have h_geo := geometric_sum_bound delta_seq 14 (9 / 11 : ℝ)
      (by norm_num) (by norm_num) h_nn14 delta_seq_ratio N
    -- h_geo : ∑_{Ico 14 N} ≤ δ_14 / (1 - 9/11) = δ_14 · 11/2
    have h_value13 : delta_seq 13 = 30 / 262144 := by
      unfold delta_seq; push_cast; norm_num
    have h_value14 : delta_seq 14 = 66 / 524288 := by
      unfold delta_seq; push_cast; norm_num
    have h_compute : delta_seq 13 + delta_seq 14 / (1 - 9 / 11 : ℝ) ≤ 1 / 200 := by
      rw [h_value13, h_value14]; norm_num
    linarith

/-- The algebraic identity from Proposition 4.8 (eq:alg-id):
    `A_n − (27/16) · B_n = −3·(n²−15n+36) / (32·2^n)`.

    This identity is independent of the linear recursion itself: it follows
    by direct algebra from the definitions of `A_lin` and `B_lin`. The
    `c 3` coefficient cancels exactly between A and `(27/16)·B`, so we only
    need the closed form for `Nat.choose n 2`. -/
theorem alg_id (n : ℕ) (hn : 1 ≤ n) :
    A_lin n - (27 / 16) * B_lin n =
      -3 * ((n : ℝ) ^ 2 - 15 * n + 36) / (32 * (2 : ℝ) ^ n) := by
  have hpow_eq : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n / 2 := by
    have h : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]; ring
    rw [h]; field_simp
  unfold A_lin B_lin
  rw [c_one, c_two, c_three, Nat.cast_choose_two ℝ n, hpow_eq]
  have h2pow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-- Cumulative ε bound (helper for the (b) ≥ 13 sub-case of `joint_step`).
    Given the buffer at `m = 12` and the linear recursion at all `k ∈ [13, m]`,
    proves the cumulative bound on `c m − 27/16`. Inductive in `m`. -/
private lemma cum_eps_bound : ∀ m, 12 ≤ m →
    (c 12 - 27 / 16 ≥ 1 / 60) →
    (∀ k, 13 ≤ k → k ≤ m → c k = A_lin k + (1 - B_lin k) * c (k - 1)) →
    c m - 27 / 16 ≥ (1 / 60) * (1 - ∑ k ∈ Finset.Ico 13 (m + 1), B_lin k) -
                              ∑ k ∈ Finset.Ico 13 (m + 1), delta_seq k := by
  intro m hm hbuf hrec
  induction m, hm using Nat.le_induction with
  | base =>
    -- m = 12: Finset.Ico 13 13 = ∅, so RHS = (1/60)·1 - 0 = 1/60.
    simp [Finset.Ico_self]
    linarith
  | succ k hk ih =>
    have hrec' : ∀ j, 13 ≤ j → j ≤ k → c j = A_lin j + (1 - B_lin j) * c (j - 1) :=
      fun j h1 h2 => hrec j h1 (by omega)
    have ih' := ih hrec'
    have h_rec_k1 : c (k + 1) = A_lin (k + 1) + (1 - B_lin (k + 1)) * c k := by
      have := hrec (k + 1) (by omega) (le_refl _)
      rw [show ((k + 1) - 1 : ℕ) = k from by omega] at this
      exact this
    -- alg_id: A_(k+1) − (27/16)B_(k+1) = −delta_seq(k+1).
    have h_alg : A_lin (k + 1) - (27 / 16) * B_lin (k + 1) = - delta_seq (k + 1) := by
      rw [alg_id (k + 1) (by omega)]
      unfold delta_seq
      push_cast
      ring
    have hB_nn : (0 : ℝ) ≤ B_lin (k + 1) := by unfold B_lin; positivity
    have hSB_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 13 (k + 1), B_lin j := by
      apply Finset.sum_nonneg
      intro j _; unfold B_lin; positivity
    have hSδ_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 13 (k + 1), delta_seq j := by
      apply Finset.sum_nonneg
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      unfold delta_seq
      have hquad : (0 : ℝ) ≤ ((j : ℕ) : ℝ) ^ 2 - 15 * ((j : ℕ) : ℝ) + 36 := by
        have : (13 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj'.1
        nlinarith [this]
      positivity
    -- B_lin (k+1) < 1 for k+1 ≥ 13 (in fact for ≥ 7).
    have hB_lt : B_lin (k + 1) < 1 := by
      unfold B_lin
      rw [div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 1))]
      have h_3 := choose_sum_3_to_pred (k + 1) (by omega)
      have h_split : Ico 3 (k + 1) = insert 3 (Ico 4 (k + 1)) := by
        ext; simp only [mem_Ico, mem_insert]; omega
      have h_no3 : 3 ∉ Ico 4 (k + 1) := by simp [mem_Ico]
      rw [h_split, sum_insert h_no3] at h_3
      have h_sum_pos : (0 : ℝ) < ∑ j ∈ Ico 4 (k + 1), ((Nat.choose (k + 1) j : ℕ) : ℝ) := by
        apply Finset.sum_pos
        · intro j hj
          have hj' := mem_Ico.mp hj
          have : 0 < Nat.choose (k + 1) j := Nat.choose_pos (by omega)
          exact_mod_cast this
        · exact ⟨4, by simp [mem_Ico]; omega⟩
      linarith [h_sum_pos]
    have h_split_B : ∑ j ∈ Finset.Ico 13 (k + 1 + 1), B_lin j =
        B_lin (k + 1) + ∑ j ∈ Finset.Ico 13 (k + 1), B_lin j := by
      have h_split : Finset.Ico 13 (k + 1 + 1) = insert (k + 1) (Finset.Ico 13 (k + 1)) := by
        ext; simp [Finset.mem_Ico, Finset.mem_insert]; omega
      have h_no : (k + 1) ∉ Finset.Ico 13 (k + 1) := by simp [Finset.mem_Ico]
      rw [h_split, Finset.sum_insert h_no]
    have h_split_d : ∑ j ∈ Finset.Ico 13 (k + 1 + 1), delta_seq j =
        delta_seq (k + 1) + ∑ j ∈ Finset.Ico 13 (k + 1), delta_seq j := by
      have h_split : Finset.Ico 13 (k + 1 + 1) = insert (k + 1) (Finset.Ico 13 (k + 1)) := by
        ext; simp [Finset.mem_Ico, Finset.mem_insert]; omega
      have h_no : (k + 1) ∉ Finset.Ico 13 (k + 1) := by simp [Finset.mem_Ico]
      rw [h_split, Finset.sum_insert h_no]
    rw [h_rec_k1, h_split_B, h_split_d]
    -- LHS = A_(k+1) + (1-B_(k+1)) c k - 27/16 = (1-B_(k+1))(c k - 27/16) - delta_(k+1)
    -- (using h_alg).
    -- Goal: this ≥ (1/60)(1 - B_(k+1) - S_B) - delta_(k+1) - S_δ
    -- Equivalently: (1-B_(k+1))(c k - 27/16) ≥ (1/60)(1 - B_(k+1) - S_B) - S_δ.
    -- Using ih' (c k - 27/16 ≥ (1/60)(1 - S_B) - S_δ) and (1 - B_(k+1)) ≥ 0:
    -- (1-B_(k+1))(c k - 27/16) ≥ (1-B_(k+1)) · [(1/60)(1-S_B) - S_δ]
    -- LHS - RHS = B_(k+1) · [(1/60) S_B + S_δ] ≥ 0.
    have hone_minus_B : (0 : ℝ) ≤ 1 - B_lin (k + 1) := by linarith
    have hck_lower : c k - 27 / 16 ≥
        (1 / 60) * (1 - ∑ j ∈ Finset.Ico 13 (k + 1), B_lin j) -
          ∑ j ∈ Finset.Ico 13 (k + 1), delta_seq j := ih'
    nlinarith [h_alg, hB_nn, hSB_nn, hSδ_nn, hone_minus_B, hck_lower,
               mul_nonneg hB_nn hSB_nn, mul_nonneg hB_nn hSδ_nn,
               mul_nonneg hone_minus_B (sub_nonneg.mpr (le_of_eq rfl) :
                 (0 : ℝ) ≤ c k - c k)]

/-! ### §4.3 joint inductive structure

  Lemmas 4.5, 4.6, 4.7 and Proposition 4.8 are proved together by a single
  strong induction on `n` (see the manuscript's joint proof in §4.3):

  ```
    collapse(n)  ←  IH 4.7 + 4.8                 (uses c values < n)
    linear(n)    ←  collapse(n)                  (substitution)
    4.7(n)       ←  linear(n) + alg_id           (polynomial bound)
    4.8(n)       ←  linear(n) + IH 4.7           (polynomial bound)
  ```

  Base cases: `n ∈ {4, 5, 6}` from `c_four`, `c_five`, `c_six`. -/

/-- Helper: `suffMin j n = c k` whenever `c k` is the minimum of `c m` on `[j, n)`. -/
private lemma suffMin_eq_of_min (j n k : ℕ) (hjk : j ≤ k) (hkn : k < n)
    (h_min : ∀ m ∈ Ico j n, c k ≤ c m) :
    suffMin j n = c k := by
  apply le_antisymm
  · unfold suffMin
    rw [dif_pos (lt_of_le_of_lt hjk hkn)]
    exact Finset.inf'_le _ (mem_attach _ ⟨k, mem_Ico.mpr ⟨hjk, hkn⟩⟩)
  · exact suffMin_ge_const j n (lt_of_le_of_lt hjk hkn) (c k) h_min

/-- Helper: under the IH `c k < c (k-1)` for `k ∈ [6, n]`, the c-sequence is
    bounded as `c n ≤ c m` for any `m ∈ [5, n]`. -/
private lemma c_anti_chain (m n : ℕ) (hm : 5 ≤ m) (hmn : m ≤ n)
    (h_dec : ∀ k, 6 ≤ k → k ≤ n → c k < c (k - 1)) :
    c n ≤ c m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ k hmk ih =>
    have h_dec' : ∀ k', 6 ≤ k' → k' ≤ k → c k' < c (k' - 1) :=
      fun k' h1 h2 => h_dec k' h1 (by omega)
    have hih := ih h_dec'
    have hstep := h_dec (k + 1) (by omega) (le_refl _)
    rw [show (k + 1 - 1 : ℕ) = k from by omega] at hstep
    linarith

/-- Joint statement: for `n ≥ 4`, the four manuscript claims at level `n`. -/
theorem joint_step (n : ℕ) (hn : 4 ≤ n) :
    -- (b) lower bound (Lemma 4.6 at n)
    c n ≥ 27 / 16 ∧
    -- (c) strict decrease (Lemma 4.7 at n, valid when n ≥ 6)
    (6 ≤ n → c n < c (n - 1)) ∧
    -- (d) linear recursion (Prop 4.8 at n, valid when n ≥ 7)
    (7 ≤ n → c n = A_lin n + (1 - B_lin n) * c (n - 1)) ∧
    -- (a) collapse (Lemma 4.5 at n, valid when n ≥ 7)
    (7 ≤ n → ∀ j, 1 ≤ j → j < n →
      (j ≤ 3 → suffMin j n = c j) ∧
      (4 ≤ j → suffMin j n = c (n - 1))) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with h | h | h | h_ge_7
    · -- Base case n = 4
      subst h
      refine ⟨?_, fun h => by omega, fun h => by omega, fun h => by omega⟩
      rw [c_four]; norm_num
    · -- Base case n = 5
      subst h
      refine ⟨?_, fun h => by omega, fun h => by omega, fun h => by omega⟩
      rw [c_five]; norm_num
    · -- Base case n = 6
      subst h
      refine ⟨?_, ?_, fun h => by omega, fun h => by omega⟩
      · rw [c_six]; norm_num
      · intro _
        change c 6 < c 5
        rw [c_six, c_five]; norm_num
    · -- Inductive step n ≥ 7
      -- Extract IH parts.
      have ih_b : ∀ m, 4 ≤ m → m < n → c m ≥ 27 / 16 :=
        fun m h1 h2 => (ih m h2 h1).1
      have ih_c : ∀ m, 6 ≤ m → m < n → c m < c (m - 1) :=
        fun m h1 h2 => (ih m h2 (by omega)).2.1 h1
      ----------------------------------------------------------------
      -- (a) Collapse at level n
      ----------------------------------------------------------------
      have h_a : ∀ j, 1 ≤ j → j < n →
          (j ≤ 3 → suffMin j n = c j) ∧
          (4 ≤ j → suffMin j n = c (n - 1)) := by
        intro j hj1 hjn
        refine ⟨?_, ?_⟩
        · -- j ≤ 3: suffMin j n = c j
          intro hj3
          apply suffMin_eq_of_min j n j (le_refl _) hjn
          intro m hm
          have hmr := mem_Ico.mp hm
          rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with hj | hj | hj
          · subst hj; rw [c_one]
            exact c_ge_one_of_ih n ih_b m hmr.1 hmr.2
          · subst hj; rw [c_two]
            exact c_ge_three_halves_of_ih n ih_b m hmr.1 hmr.2
          · subst hj; rw [c_three]
            exact c_ge_27_16_of_ih n ih_b m hmr.1 hmr.2
        · -- j ≥ 4: suffMin j n = c (n - 1)
          intro hj4
          apply suffMin_eq_of_min j n (n - 1) (by omega) (by omega)
          intro m hm
          have hmr := mem_Ico.mp hm
          rcases (show m = 4 ∨ 5 ≤ m by omega) with h_m4 | h_m5
          · -- m = 4: c (n - 1) ≤ c 4 via c_4 > c_6 ≥ c (n-1)
            subst h_m4
            have hc46 : c 6 < c 4 := by rw [c_six, c_four]; norm_num
            have hchain : c (n - 1) ≤ c 6 :=
              c_anti_chain 6 (n - 1) (by omega) (by omega)
                (fun k h1 h2 => ih_c k h1 (by omega))
            linarith
          · -- m ≥ 5: chain via IH(c)
            exact c_anti_chain m (n - 1) h_m5 (by omega)
              (fun k h1 h2 => ih_c k h1 (by omega))
      ----------------------------------------------------------------
      -- (d) Linear recursion at level n
      ----------------------------------------------------------------
      have h_d : c n = A_lin n + (1 - B_lin n) * c (n - 1) := by
        -- Decompose n = m + 2 with m = n - 2 ≥ 5.
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        rw [c_succ m, show (m + 2 - 1 : ℕ) = m + 1 from rfl]
        -- Split Ico 1 (m + 2) at j = 4.
        have hsplit : Ico 1 (m + 2) = ({1, 2, 3} : Finset ℕ) ∪ Ico 4 (m + 2) := by
          ext; simp only [mem_Ico, mem_insert, mem_union, mem_singleton]; omega
        have hd : Disjoint ({1, 2, 3} : Finset ℕ) (Ico 4 (m + 2)) := by
          rw [Finset.disjoint_left]
          intro a ha
          simp only [mem_insert, mem_singleton] at ha
          simp only [mem_Ico]; omega
        rw [hsplit, sum_union hd]
        -- Replace suffMin j (m+2) for j ∈ {1, 2, 3}
        have hsm1 : suffMin 1 (m + 2) = c 1 := (h_a 1 (le_refl _) (by omega)).1 (by omega)
        have hsm2 : suffMin 2 (m + 2) = c 2 := (h_a 2 (by omega) (by omega)).1 (by omega)
        have hsm3 : suffMin 3 (m + 2) = c 3 := (h_a 3 (by omega) (by omega)).1 (by omega)
        rw [show ({1, 2, 3} : Finset ℕ) = insert 1 (insert 2 {3}) from rfl,
            sum_insert (by simp), sum_insert (by simp), sum_singleton]
        rw [hsm1, hsm2, hsm3]
        -- Replace suffMin j (m+2) for j ∈ Ico 4 (m+2)
        have hrest : ∑ j ∈ Ico 4 (m + 2),
            (Nat.choose (m + 2) j : ℝ) * suffMin j (m + 2) =
            c (m + 1) * ∑ j ∈ Ico 4 (m + 2), (Nat.choose (m + 2) j : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjr := mem_Ico.mp hj
          have h_sm : suffMin j (m + 2) = c (m + 1) := by
            have := (h_a j (by omega) hjr.2).2 (by omega)
            rw [show (m + 2 - 1 : ℕ) = m + 1 from rfl] at this
            exact this
          rw [h_sm]; ring
        rw [hrest]
        -- Compute ∑ Ico 4 (m+2) C(m+2, j) = 2^(m+2) - 2 - (m+2) - C(m+2,2) - C(m+2,3)
        have hsum_4 : ∑ j ∈ Ico 4 (m + 2), ((Nat.choose (m + 2) j : ℕ) : ℝ) =
            (2 : ℝ) ^ (m + 2) - 2 - ((m + 2 : ℕ) : ℝ) -
              ((Nat.choose (m + 2) 2 : ℕ) : ℝ) -
              ((Nat.choose (m + 2) 3 : ℕ) : ℝ) := by
          have h_3 := choose_sum_3_to_pred (m + 2) (by omega)
          have h_split : Ico 3 (m + 2) = insert 3 (Ico 4 (m + 2)) := by
            ext; simp only [mem_Ico, mem_insert]; omega
          have h_no3 : 3 ∉ Ico 4 (m + 2) := by simp [mem_Ico]
          rw [h_split, sum_insert h_no3] at h_3
          linarith
        rw [hsum_4]
        -- C(m+2, 1) = m + 2
        rw [show ((Nat.choose (m + 2) 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) from by
              rw [Nat.choose_one_right]]
        -- Final algebra: unfold A_lin, B_lin and ring.
        unfold A_lin B_lin
        rw [show (m + 2 - 1 : ℕ) = m + 1 from rfl]
        have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (m + 2) := by positivity
        have h2pow_pos' : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
        field_simp
        push_cast
        ring
      ----------------------------------------------------------------
      -- (b) Lower bound at level n
      ----------------------------------------------------------------
      have hB_lt : B_lin n < 1 := by
        -- B_n = (2 + n + C(n,2) + C(n,3)) / 2^n. For n ≥ 7 (in fact n ≥ 5)
        -- the numerator is strictly less than 2^n, since the missing terms
        -- C(n, 4), …, C(n, n-1) are all strictly positive.
        unfold B_lin
        rw [div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
        -- Goal: 2 + n + C(n,2) + C(n,3) < 2^n.
        have h_3 := choose_sum_3_to_pred n (by omega)
        have h_split : Ico 3 n = insert 3 (Ico 4 n) := by
          ext; simp only [mem_Ico, mem_insert]; omega
        have h_no3 : 3 ∉ Ico 4 n := by simp [mem_Ico]
        rw [h_split, sum_insert h_no3] at h_3
        -- h_3 : ↑(C n 3) + ∑ Ico 4 n, ↑(C n j) = 2^n - 2 - n - ↑(C n 2)
        have h_sum_pos : (0 : ℝ) < ∑ j ∈ Ico 4 n, ((Nat.choose n j : ℕ) : ℝ) := by
          apply Finset.sum_pos
          · intro j hj
            have hj' := mem_Ico.mp hj
            have : 0 < Nat.choose n j := Nat.choose_pos (by omega)
            exact_mod_cast this
          · exact ⟨4, by simp [mem_Ico]; omega⟩
        linarith [h_sum_pos]
      have hB_pos : 0 < B_lin n := by
        unfold B_lin
        have : (0 : ℝ) < (2 + (n : ℝ) + (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ)) := by
          have h1 : (0 : ℝ) ≤ (Nat.choose n 2 : ℝ) := by exact_mod_cast Nat.zero_le _
          have h2 : (0 : ℝ) ≤ (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.zero_le _
          have h3 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
          linarith
        positivity
      have h_b : c n ≥ 27 / 16 := by
        rcases (show n ≤ 12 ∨ 13 ≤ n by omega) with h_le | h_ge
        · -- n ∈ [7, 12]: A_n - (27/16) B_n ≥ 0 by alg_id + poly bound.
          rw [h_d]
          have h_alg := alg_id n (by omega)
          have hcn1 : c (n - 1) ≥ 27 / 16 := ih_b (n - 1) (by omega) (by omega)
          have h_alg_nn : A_lin n - (27 / 16) * B_lin n ≥ 0 := by
            rw [h_alg]
            have hpoly : ((n : ℝ) ^ 2 - 15 * n + 36) ≤ 0 := by
              have h7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 7 ≤ n by omega)
              have h12 : (n : ℝ) ≤ 12 := by exact_mod_cast h_le
              nlinarith [h7, h12]
            have hpow : (0 : ℝ) < 32 * (2 : ℝ) ^ n := by positivity
            apply div_nonneg
            · linarith
            · linarith
          nlinarith [h_alg_nn, hcn1, hB_lt, hB_pos]
        · -- n ≥ 13: cumulative argument.
          -- Step 1: Derive c_12 explicitly via IH(d) chain back to c_six.
          -- Cast lemmas for choose values used in the chain.
          have h7c2 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by
            exact_mod_cast (by decide : Nat.choose 7 2 = 21)
          have h7c3 : ((Nat.choose 7 3 : ℕ) : ℝ) = 35 := by
            exact_mod_cast (by decide : Nat.choose 7 3 = 35)
          have h8c2 : ((Nat.choose 8 2 : ℕ) : ℝ) = 28 := by
            exact_mod_cast (by decide : Nat.choose 8 2 = 28)
          have h8c3 : ((Nat.choose 8 3 : ℕ) : ℝ) = 56 := by
            exact_mod_cast (by decide : Nat.choose 8 3 = 56)
          have h9c2 : ((Nat.choose 9 2 : ℕ) : ℝ) = 36 := by
            exact_mod_cast (by decide : Nat.choose 9 2 = 36)
          have h9c3 : ((Nat.choose 9 3 : ℕ) : ℝ) = 84 := by
            exact_mod_cast (by decide : Nat.choose 9 3 = 84)
          have hAc2 : ((Nat.choose 10 2 : ℕ) : ℝ) = 45 := by
            exact_mod_cast (by decide : Nat.choose 10 2 = 45)
          have hAc3 : ((Nat.choose 10 3 : ℕ) : ℝ) = 120 := by
            exact_mod_cast (by decide : Nat.choose 10 3 = 120)
          have hBc2 : ((Nat.choose 11 2 : ℕ) : ℝ) = 55 := by
            exact_mod_cast (by decide : Nat.choose 11 2 = 55)
          have hBc3 : ((Nat.choose 11 3 : ℕ) : ℝ) = 165 := by
            exact_mod_cast (by decide : Nat.choose 11 3 = 165)
          have hCc2 : ((Nat.choose 12 2 : ℕ) : ℝ) = 66 := by
            exact_mod_cast (by decide : Nat.choose 12 2 = 66)
          have hCc3 : ((Nat.choose 12 3 : ℕ) : ℝ) = 220 := by
            exact_mod_cast (by decide : Nat.choose 12 3 = 220)
          -- Build the chain h_d7 → h_d12.
          have h_d7 := (ih 7 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (7 - 1 : ℕ) = 6 from rfl, c_six] at h_d7
          unfold A_lin B_lin at h_d7
          rw [c_one, c_two, c_three] at h_d7
          rw [h7c2, h7c3] at h_d7
          have h_d8 := (ih 8 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (8 - 1 : ℕ) = 7 from rfl, h_d7] at h_d8
          unfold A_lin B_lin at h_d8
          rw [c_one, c_two, c_three] at h_d8
          rw [h8c2, h8c3] at h_d8
          have h_d9 := (ih 9 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (9 - 1 : ℕ) = 8 from rfl, h_d8] at h_d9
          unfold A_lin B_lin at h_d9
          rw [c_one, c_two, c_three] at h_d9
          rw [h9c2, h9c3] at h_d9
          have h_d10 := (ih 10 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (10 - 1 : ℕ) = 9 from rfl, h_d9] at h_d10
          unfold A_lin B_lin at h_d10
          rw [c_one, c_two, c_three] at h_d10
          rw [hAc2, hAc3] at h_d10
          have h_d11 := (ih 11 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (11 - 1 : ℕ) = 10 from rfl, h_d10] at h_d11
          unfold A_lin B_lin at h_d11
          rw [c_one, c_two, c_three] at h_d11
          rw [hBc2, hBc3] at h_d11
          have h_d12 := (ih 12 (by omega) (by omega)).2.2.1 (by omega)
          rw [show (12 - 1 : ℕ) = 11 from rfl, h_d11] at h_d12
          unfold A_lin B_lin at h_d12
          rw [c_one, c_two, c_three] at h_d12
          rw [hCc2, hCc3] at h_d12
          -- Step 2: Verify the buffer c_12 ≥ 27/16 + 1/60.
          have h_buffer : c 12 ≥ 27 / 16 + 1 / 60 := by
            rw [h_d12]; norm_num
          -- Step 3: Cumulative argument.
          -- Build the linear-rec function for k ∈ [13, n], using IH(d) at smaller
          -- levels and h_d at level n.
          have h_lin_rec : ∀ k, 13 ≤ k → k ≤ n →
              c k = A_lin k + (1 - B_lin k) * c (k - 1) := by
            intro k hk1 hkn
            rcases (eq_or_lt_of_le hkn) with heq | hlt
            · rw [heq]; exact h_d
            · exact (ih k hlt (by omega)).2.2.1 (by omega)
          have h_buffer' : c 12 - 27 / 16 ≥ 1 / 60 := by linarith
          have h_cum := cum_eps_bound n (by omega) h_buffer' h_lin_rec
          have hB := B_tail_bound (n + 1)
          have hδ := delta_tail_bound (n + 1)
          linarith [h_cum, hB, hδ]
      ----------------------------------------------------------------
      -- (c) Strict decrease at level n
      ----------------------------------------------------------------
      have h_c : c n < c (n - 1) := by
        rcases (show n ≤ 12 ∨ 13 ≤ n by omega) with h_le | h_ge
        · -- n ∈ [7, 12]: per-n numerical.
          -- Approach: substitute c_n via h_d, chain back to c_6 using
          -- IH(d) at smaller levels, plug in c_6 = 113337/65536, and
          -- close numerically.
          rw [h_d]
          rcases (show n = 7 ∨ 8 ≤ n ∧ n ≤ 12 by omega) with hn7 | ⟨hn8, hnle⟩
          · -- n = 7: only need c_6 explicitly.
            subst hn7
            rw [show (7 - 1 : ℕ) = 6 from rfl, c_six]
            unfold A_lin B_lin
            rw [c_one, c_two, c_three]
            have h72 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by
              exact_mod_cast (by decide : Nat.choose 7 2 = 21)
            have h73 : ((Nat.choose 7 3 : ℕ) : ℝ) = 35 := by
              exact_mod_cast (by decide : Nat.choose 7 3 = 35)
            rw [h72, h73]
            norm_num
          · -- n ∈ [8, 12]: chained derivation of c_{n-1} from c_6 via IH(d).
            -- Pre-derive c_7 from IH(d) at 7 + c_six.
            have hc7 : c 7 = 14451591 / 8388608 := by
              have h_d7 := (ih 7 (by omega) (by omega)).2.2.1 (by omega)
              rw [show (7 - 1 : ℕ) = 6 from rfl, c_six] at h_d7
              unfold A_lin B_lin at h_d7
              rw [c_one, c_two, c_three] at h_d7
              have h72 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by
                exact_mod_cast (by decide : Nat.choose 7 2 = 21)
              have h73 : ((Nat.choose 7 3 : ℕ) : ℝ) = 35 := by
                exact_mod_cast (by decide : Nat.choose 7 3 = 35)
              rw [h72, h73] at h_d7
              rw [h_d7]; norm_num
            rcases (show n = 8 ∨ 9 ≤ n ∧ n ≤ 12 by omega) with hn8' | ⟨hn9, hnle9⟩
            · -- n = 8: only need c_7.
              subst hn8'
              rw [show (8 - 1 : ℕ) = 7 from rfl, hc7]
              unfold A_lin B_lin
              rw [c_one, c_two, c_three]
              have h82 : ((Nat.choose 8 2 : ℕ) : ℝ) = 28 := by
                exact_mod_cast (by decide : Nat.choose 8 2 = 28)
              have h83 : ((Nat.choose 8 3 : ℕ) : ℝ) = 56 := by
                exact_mod_cast (by decide : Nat.choose 8 3 = 56)
              rw [h82, h83]
              norm_num
            · -- n ∈ [9, 12]: derive c_8 first.
              have hc8 : c 8 = 1843764663 / 1073741824 := by
                have h_d8 := (ih 8 (by omega) (by omega)).2.2.1 (by omega)
                rw [show (8 - 1 : ℕ) = 7 from rfl, hc7] at h_d8
                unfold A_lin B_lin at h_d8
                rw [c_one, c_two, c_three] at h_d8
                have h82 : ((Nat.choose 8 2 : ℕ) : ℝ) = 28 := by
                  exact_mod_cast (by decide : Nat.choose 8 2 = 28)
                have h83 : ((Nat.choose 8 3 : ℕ) : ℝ) = 56 := by
                  exact_mod_cast (by decide : Nat.choose 8 3 = 56)
                rw [h82, h83] at h_d8
                rw [h_d8]; norm_num
              rcases (show n = 9 ∨ 10 ≤ n ∧ n ≤ 12 by omega) with hn9' | ⟨hn10, hnle10⟩
              · -- n = 9: only need c_8.
                subst hn9'
                rw [show (9 - 1 : ℕ) = 8 from rfl, hc8]
                unfold A_lin B_lin
                rw [c_one, c_two, c_three]
                have h92 : ((Nat.choose 9 2 : ℕ) : ℝ) = 36 := by
                  exact_mod_cast (by decide : Nat.choose 9 2 = 36)
                have h93 : ((Nat.choose 9 3 : ℕ) : ℝ) = 84 := by
                  exact_mod_cast (by decide : Nat.choose 9 3 = 84)
                rw [h92, h93]
                norm_num
              · -- n ∈ [10, 12]: extend the chain by deriving hc9.
                have hc9 : c 9 = 941650327899 / 549755813888 := by
                  have h_d9 := (ih 9 (by omega) (by omega)).2.2.1 (by omega)
                  rw [show (9 - 1 : ℕ) = 8 from rfl, hc8] at h_d9
                  unfold A_lin B_lin at h_d9
                  rw [c_one, c_two, c_three] at h_d9
                  have h92 : ((Nat.choose 9 2 : ℕ) : ℝ) = 36 := by
                    exact_mod_cast (by decide : Nat.choose 9 2 = 36)
                  have h93 : ((Nat.choose 9 3 : ℕ) : ℝ) = 84 := by
                    exact_mod_cast (by decide : Nat.choose 9 3 = 84)
                  rw [h92, h93] at h_d9
                  rw [h_d9]; norm_num
                rcases (show n = 10 ∨ 11 ≤ n ∧ n ≤ 12 by omega) with hn10' | ⟨hn11, hnle11⟩
                · -- n = 10: only need c_9.
                  subst hn10'
                  rw [show (10 - 1 : ℕ) = 9 from rfl, hc9]
                  unfold A_lin B_lin
                  rw [c_one, c_two, c_three]
                  have hA2 : ((Nat.choose 10 2 : ℕ) : ℝ) = 45 := by
                    exact_mod_cast (by decide : Nat.choose 10 2 = 45)
                  have hA3 : ((Nat.choose 10 3 : ℕ) : ℝ) = 120 := by
                    exact_mod_cast (by decide : Nat.choose 10 3 = 120)
                  rw [hA2, hA3]
                  norm_num
                · -- n ∈ [11, 12]: extend the chain by deriving hc10 (symbolically).
                  have h_d10 := (ih 10 (by omega) (by omega)).2.2.1 (by omega)
                  rw [show (10 - 1 : ℕ) = 9 from rfl, hc9] at h_d10
                  unfold A_lin B_lin at h_d10
                  rw [c_one, c_two, c_three] at h_d10
                  have hA2_10 : ((Nat.choose 10 2 : ℕ) : ℝ) = 45 := by
                    exact_mod_cast (by decide : Nat.choose 10 2 = 45)
                  have hA3_10 : ((Nat.choose 10 3 : ℕ) : ℝ) = 120 := by
                    exact_mod_cast (by decide : Nat.choose 10 3 = 120)
                  rw [hA2_10, hA3_10] at h_d10
                  rcases (show n = 11 ∨ n = 12 by omega) with hn11' | hn12
                  · -- n = 11.
                    subst hn11'
                    rw [show (11 - 1 : ℕ) = 10 from rfl, h_d10]
                    unfold A_lin B_lin
                    rw [c_one, c_two, c_three]
                    have hB2 : ((Nat.choose 11 2 : ℕ) : ℝ) = 55 := by
                      exact_mod_cast (by decide : Nat.choose 11 2 = 55)
                    have hB3 : ((Nat.choose 11 3 : ℕ) : ℝ) = 165 := by
                      exact_mod_cast (by decide : Nat.choose 11 3 = 165)
                    rw [hB2, hB3]
                    norm_num
                  · -- n = 12: also derive h_d11 first (symbolic).
                    subst hn12
                    have h_d11 := (ih 11 (by omega) (by omega)).2.2.1 (by omega)
                    rw [show (11 - 1 : ℕ) = 10 from rfl, h_d10] at h_d11
                    unfold A_lin B_lin at h_d11
                    rw [c_one, c_two, c_three] at h_d11
                    have hB2_11 : ((Nat.choose 11 2 : ℕ) : ℝ) = 55 := by
                      exact_mod_cast (by decide : Nat.choose 11 2 = 55)
                    have hB3_11 : ((Nat.choose 11 3 : ℕ) : ℝ) = 165 := by
                      exact_mod_cast (by decide : Nat.choose 11 3 = 165)
                    rw [hB2_11, hB3_11] at h_d11
                    rw [show (12 - 1 : ℕ) = 11 from rfl, h_d11]
                    unfold A_lin B_lin
                    rw [c_one, c_two, c_three]
                    have hC2 : ((Nat.choose 12 2 : ℕ) : ℝ) = 66 := by
                      exact_mod_cast (by decide : Nat.choose 12 2 = 66)
                    have hC3 : ((Nat.choose 12 3 : ℕ) : ℝ) = 220 := by
                      exact_mod_cast (by decide : Nat.choose 12 3 = 220)
                    rw [hC2, hC3]
                    norm_num
        · -- n ≥ 13: A_n - (27/16) B_n < 0 by alg_id, so c_n < c_{n-1}.
          rw [h_d]
          have h_alg := alg_id n (by omega)
          have hcn1 : c (n - 1) ≥ 27 / 16 := ih_b (n - 1) (by omega) (by omega)
          have h_alg_neg : A_lin n - (27 / 16) * B_lin n < 0 := by
            rw [h_alg]
            have hpoly : ((n : ℝ) ^ 2 - 15 * n + 36) > 0 := by
              have h13 : (13 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_ge
              nlinarith [h13]
            have hpow : (0 : ℝ) < 32 * (2 : ℝ) ^ n := by positivity
            apply div_neg_of_neg_of_pos
            · linarith
            · linarith
          nlinarith [h_alg_neg, hcn1, hB_pos]
      exact ⟨h_b, fun _ => h_c, fun _ => h_d, fun _ => h_a⟩

/-- Lemma 4.6 (full): `c m ≥ 27/16` for every `m ≥ 4`.
    Corollary of `joint_step.1`. -/
theorem c_ge_27_16_full : ∀ m : ℕ, 4 ≤ m → c m ≥ 27 / 16 :=
  fun m hm => (joint_step m hm).1

/-- Lemma 4.7: the sequence `(c n)_{n ≥ 5}` is strictly decreasing.
    Corollary of `joint_step.2.1`. -/
theorem c_strict_anti_from_five : ∀ n : ℕ, 5 ≤ n → c (n + 1) < c n := by
  intro n hn
  have h := (joint_step (n + 1) (by omega)).2.1 (by omega)
  rwa [show (n + 1) - 1 = n from by omega] at h

/-- Proposition 4.8: the linear recursion for `n ≥ 7`.
    Corollary of `joint_step.2.2.1`. -/
theorem c_linear_rec (n : ℕ) (h : 7 ≤ n) :
    c n = A_lin n + (1 - B_lin n) * c (n - 1) :=
  (joint_step n (by omega)).2.2.1 h

/-- Lemma 4.5 (collapse) — low part: for `n ≥ 7` and `j ∈ {1, 2, 3}`,
    `suffMin j n = c j`. Corollary of `joint_step.2.2.2`. -/
theorem suffMin_collapse_low (n j : ℕ) (hn : 7 ≤ n) (h1 : 1 ≤ j) (h3 : j ≤ 3) :
    suffMin j n = c j :=
  (((joint_step n (by omega)).2.2.2 hn) j h1 (by omega)).1 h3

/-- Lemma 4.5 (collapse) — high part: for `n ≥ 7` and `j ∈ {4, …, n−1}`,
    `suffMin j n = c (n − 1)`. Corollary of `joint_step.2.2.2`. -/
theorem suffMin_collapse_high (n j : ℕ) (hn : 7 ≤ n) (h4 : 4 ≤ j) (hjn : j < n) :
    suffMin j n = c (n - 1) :=
  (((joint_step n (by omega)).2.2.2 hn) j (by omega) hjn).2 h4

/-- Theorem 4.10: the limit `L = lim c_n` exists.

    Proof: shift the sequence by 5 to obtain `f n := c (n + 5)`, which is
    antitone (by `c_strict_anti_from_five`) and bounded below by `27/16`
    (by `c_ge_27_16_full`). Mathlib's `Antitone.tendsto_atTop_iInf` gives
    convergence; transfer back to `c` via eventual equality. -/
theorem c_limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L) := by
  let f : ℕ → ℝ := fun n => c (n + 5)
  -- f is antitone: `c (n+1+5) ≤ c (n+5)` from `c_strict_anti_from_five`.
  have h_anti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    have h := c_strict_anti_from_five (n + 5) (by omega)
    show c (n + 1 + 5) ≤ c (n + 5)
    rw [show n + 1 + 5 = n + 5 + 1 from by omega]
    exact h.le
  -- f is bounded below by 27/16.
  have h_bdd : BddBelow (Set.range f) := by
    refine ⟨27 / 16, ?_⟩
    rintro x ⟨n, rfl⟩
    exact c_ge_27_16_full (n + 5) (by omega)
  -- Apply Mathlib's antitone-tends-to-infimum.
  have h_f_tendsto : Filter.Tendsto f Filter.atTop (nhds (⨅ x, f x)) :=
    tendsto_atTop_ciInf h_anti h_bdd
  refine ⟨⨅ x, f x, ?_⟩
  -- `c =ᶠ[atTop] (fun n => f (n - 5))`, and the shift `(· - 5)` is `Tendsto atTop atTop`.
  have h_shift : Filter.Tendsto (fun n : ℕ => n - 5) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨b + 5, fun a ha => ?_⟩
    omega
  have h_comp : Filter.Tendsto (fun n => f (n - 5)) Filter.atTop (nhds (⨅ x, f x)) :=
    h_f_tendsto.comp h_shift
  have h_eq : (fun n => c n) =ᶠ[Filter.atTop] (fun n => f (n - 5)) := by
    filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    show c n = c (n - 5 + 5)
    congr 1; omega
  exact Filter.Tendsto.congr' h_eq.symm h_comp

/-- Finite iteration of the linear recursion: for `n ≥ n₀ ≥ 7`,
    `c n = c (n₀ - 1) · ∏_{m=n₀}^n (1 - B_m) + ∑_{k=n₀}^n A_k · ∏_{m=k+1}^n (1 - B_m)`. -/
private lemma c_iterate (n₀ : ℕ) (hn₀ : 7 ≤ n₀) :
    ∀ n, n₀ ≤ n →
      c n = c (n₀ - 1) * ∏ m ∈ Finset.Ico n₀ (n + 1), (1 - B_lin m) +
            ∑ k ∈ Finset.Ico n₀ (n + 1),
              A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), (1 - B_lin m) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    -- n = n₀: c n₀ = c (n₀-1) · (1 - B_{n₀}) + A_{n₀} · (empty product = 1).
    have h_rec : c n₀ = A_lin n₀ + (1 - B_lin n₀) * c (n₀ - 1) := c_linear_rec n₀ hn₀
    have h_Ico_sing : Finset.Ico n₀ (n₀ + 1) = ({n₀} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [h_Ico_sing, Finset.prod_singleton, Finset.sum_singleton, Finset.Ico_self,
        Finset.prod_empty, mul_one]
    linarith [h_rec]
  | succ m hm ih =>
    -- Step: c (m + 1) = A_{m+1} + (1 - B_{m+1}) · c m.
    have h_rec : c (m + 1) = A_lin (m + 1) + (1 - B_lin (m + 1)) * c m :=
      c_linear_rec (m + 1) (by omega)
    -- Split the new Ico ranges at m + 1.
    have h_split_prod : Finset.Ico n₀ (m + 1 + 1) = insert (m + 1) (Finset.Ico n₀ (m + 1)) := by
      ext; simp [Finset.mem_Ico, Finset.mem_insert]; omega
    have h_no : (m + 1) ∉ Finset.Ico n₀ (m + 1) := by simp [Finset.mem_Ico]
    have h_split_sum : Finset.Ico n₀ (m + 1 + 1) = insert (m + 1) (Finset.Ico n₀ (m + 1)) := h_split_prod
    -- Transform the product `∏ Ico n₀ (m+2) (1-B_m) = (1 - B_{m+1}) * ∏ Ico n₀ (m+1) (1-B_m)`.
    have h_prod_eq : ∏ l ∈ Finset.Ico n₀ (m + 1 + 1), (1 - B_lin l) =
        (1 - B_lin (m + 1)) * ∏ l ∈ Finset.Ico n₀ (m + 1), (1 - B_lin l) := by
      rw [h_split_prod, Finset.prod_insert h_no]
    -- Transform each inner product in the sum for k ∈ Ico n₀ (m+1):
    -- `∏ Ico (k+1) (m+2) (1-B) = (1 - B_{m+1}) * ∏ Ico (k+1) (m+1) (1-B)`
    -- (since (m+1) ∉ Ico (k+1) (m+1), and Ico (k+1) (m+2) = insert (m+1) (Ico (k+1) (m+1))
    -- when k+1 ≤ m+1, i.e., k ≤ m).
    have h_inner_prod : ∀ k, n₀ ≤ k → k ≤ m →
        ∏ l ∈ Finset.Ico (k + 1) (m + 1 + 1), (1 - B_lin l) =
        (1 - B_lin (m + 1)) * ∏ l ∈ Finset.Ico (k + 1) (m + 1), (1 - B_lin l) := by
      intro k _ hk
      have h_split_k : Finset.Ico (k + 1) (m + 1 + 1) =
          insert (m + 1) (Finset.Ico (k + 1) (m + 1)) := by
        ext; simp [Finset.mem_Ico, Finset.mem_insert]; omega
      have h_no_k : (m + 1) ∉ Finset.Ico (k + 1) (m + 1) := by simp [Finset.mem_Ico]
      rw [h_split_k, Finset.prod_insert h_no_k]
    -- The new term at k = m + 1 in the sum has ∏ over empty = 1.
    have h_new_term_prod : ∏ l ∈ Finset.Ico (m + 1 + 1) (m + 1 + 1), (1 - B_lin l) = 1 := by
      simp [Finset.Ico_self]
    -- Rewrite sum over insert at m+1:
    have h_sum_eq : ∑ k ∈ Finset.Ico n₀ (m + 1 + 1),
        A_lin k * ∏ l ∈ Finset.Ico (k + 1) (m + 1 + 1), (1 - B_lin l) =
        A_lin (m + 1) +
        (1 - B_lin (m + 1)) *
          ∑ k ∈ Finset.Ico n₀ (m + 1),
            A_lin k * ∏ l ∈ Finset.Ico (k + 1) (m + 1), (1 - B_lin l) := by
      rw [h_split_sum, Finset.sum_insert h_no, h_new_term_prod, mul_one]
      rw [Finset.mul_sum]
      apply congr_arg (A_lin (m + 1) + ·)
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      rw [h_inner_prod k hk'.1 (by omega)]
      ring
    rw [h_prod_eq, h_sum_eq, h_rec, ih]
    ring

/-- Summability of B_lin over all of ℕ. -/
private lemma summable_B_lin : Summable B_lin := by
  apply summable_of_sum_range_le (c := ∑ k ∈ Finset.range 13, B_lin k + 1/8)
  · intro i; unfold B_lin; positivity
  · intro N
    rcases Nat.lt_or_ge N 13 with hN | hN
    · -- N ≤ 13: finite sum bounded by the full sum up to 13, plus 1/8.
      have h_sub : Finset.range N ⊆ Finset.range 13 := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      calc ∑ k ∈ Finset.range N, B_lin k
          ≤ ∑ k ∈ Finset.range 13, B_lin k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
            intro i _ _; unfold B_lin; positivity
        _ ≤ ∑ k ∈ Finset.range 13, B_lin k + 1 / 8 := by norm_num
    · -- N ≥ 13: split at 13, use B_tail_bound on the second piece.
      have h_split : Finset.range N = Finset.range 13 ∪ Finset.Ico 13 N := by
        ext x
        simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
        omega
      have h_disj : Disjoint (Finset.range 13) (Finset.Ico 13 N) := by
        rw [Finset.disjoint_left]
        intro a h1 h2
        simp [Finset.mem_range] at h1
        simp [Finset.mem_Ico] at h2
        omega
      rw [h_split, Finset.sum_union h_disj]
      have h_tail := B_tail_bound N
      linarith

/-- `Multipliable (fun m : {m // n₀ ≤ m} => 1 - B_lin m)` for any `n₀ ≥ 7`.
    Uses `Real.multipliable_one_add_of_summable` with `f = -B_lin`. -/
private lemma multipliable_one_minus_B (n₀ : ℕ) :
    Multipliable (fun m : {m : ℕ // n₀ ≤ m} => (1 : ℝ) - B_lin m.val) := by
  have h_sub : Summable (fun m : {m : ℕ // n₀ ≤ m} => B_lin m.val) :=
    summable_B_lin.comp_injective Subtype.val_injective
  have h_neg : Summable (fun m : {m : ℕ // n₀ ≤ m} => -B_lin m.val) := h_sub.neg
  have h := Real.multipliable_one_add_of_summable h_neg
  -- h : Multipliable (fun i => 1 + -B_lin i.val)
  simpa [sub_eq_add_neg] using h

/-- Equivalence between `ℕ` and the subtype `{m // n₀ ≤ m}` via the shift
    `j ↦ n₀ + j`. -/
private def shiftEquiv (n₀ : ℕ) : ℕ ≃ {m : ℕ // n₀ ≤ m} where
  toFun j := ⟨n₀ + j, Nat.le_add_right _ _⟩
  invFun m := m.val - n₀
  left_inv j := by simp
  right_inv m := by
    obtain ⟨m, hm⟩ := m
    ext
    dsimp
    omega

/-- The shifted sequence `g j := 1 - B_lin (n₀ + j)` is multipliable on ℕ. -/
private lemma multipliable_one_minus_B_shifted (n₀ : ℕ) :
    Multipliable (fun j : ℕ => (1 : ℝ) - B_lin (n₀ + j)) := by
  have h_sub := multipliable_one_minus_B n₀
  -- Transfer along the equivalence `shiftEquiv n₀ : ℕ ≃ {m // n₀ ≤ m}`.
  have h_iff := (shiftEquiv n₀).multipliable_iff
    (f := fun m : {m // n₀ ≤ m} => (1 : ℝ) - B_lin m.val)
  -- h_iff : Multipliable ((fun m => 1 - B_lin m.val) ∘ shiftEquiv n₀) ↔
  --         Multipliable (fun m => 1 - B_lin m.val)
  exact h_iff.mpr h_sub

/-- The tprod over the subtype equals the tprod over ℕ via the shift. -/
private lemma tprod_subtype_eq_tprod_shifted (n₀ : ℕ) :
    ∏' m : {m : ℕ // n₀ ≤ m}, ((1 : ℝ) - B_lin m.val) =
      ∏' j : ℕ, (1 - B_lin (n₀ + j)) := by
  have := (shiftEquiv n₀).tprod_eq (fun m : {m // n₀ ≤ m} => (1 : ℝ) - B_lin m.val)
  -- this : ∏' j, (1 - B_lin (shiftEquiv n₀ j).val) = ∏' m, (1 - B_lin m.val)
  exact this.symm

/-- Product convergence: as `n → ∞`, the finite product over `Ico n₀ (n+1)`
    tends to the tprod over `{m // n₀ ≤ m}`. -/
private lemma tendsto_prod_Ico_B (n₀ : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => ∏ m ∈ Finset.Ico n₀ (n + 1), ((1 : ℝ) - B_lin m))
      Filter.atTop
      (nhds (∏' m : {m : ℕ // n₀ ≤ m}, (1 - B_lin m.val))) := by
  set g : ℕ → ℝ := fun j => 1 - B_lin (n₀ + j) with hg_def
  -- Rewrite target using shift.
  rw [tprod_subtype_eq_tprod_shifted n₀]
  -- Now target is nhds (∏' j, g j).
  -- Multipliable g implies tendsto of partial products.
  have h_mul_g : Multipliable g := multipliable_one_minus_B_shifted n₀
  have h_tendsto_range : Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, g j)
      Filter.atTop (nhds (∏' j : ℕ, g j)) :=
    h_mul_g.hasProd.tendsto_prod_nat
  -- Shift n ↦ n + 1 - n₀ tends to atTop.
  have h_shift : Filter.Tendsto (fun n : ℕ => n + 1 - n₀) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨b + n₀, ?_⟩
    intro a ha
    omega
  have h_comp : Filter.Tendsto (fun n : ℕ => ∏ j ∈ Finset.range (n + 1 - n₀), g j)
      Filter.atTop (nhds (∏' j : ℕ, g j)) :=
    h_tendsto_range.comp h_shift
  have h_ev : (fun n : ℕ => ∏ m ∈ Finset.Ico n₀ (n + 1), ((1 : ℝ) - B_lin m)) =ᶠ[Filter.atTop]
      (fun n : ℕ => ∏ j ∈ Finset.range (n + 1 - n₀), g j) := by
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    show ∏ m ∈ Finset.Ico n₀ (n + 1), ((1 : ℝ) - B_lin m) =
         ∏ j ∈ Finset.range (n + 1 - n₀), g j
    rw [Finset.prod_Ico_eq_prod_range]
  exact Filter.Tendsto.congr' h_ev.symm h_comp

/-- `A_lin n` is non-negative (all four summands are products of non-negative
    quantities, since `c 1 = 1`, `c 2 = 3/2`, `c 3 = 27/16`). -/
private lemma A_lin_nonneg (n : ℕ) : 0 ≤ A_lin n := by
  unfold A_lin
  have hc1 : (0 : ℝ) ≤ c 1 := by rw [c_one]; norm_num
  have hc2 : (0 : ℝ) ≤ c 2 := by rw [c_two]; norm_num
  have hc3 : (0 : ℝ) ≤ c 3 := by rw [c_three]; norm_num
  positivity

/-- `B_lin n > 0` for all `n ≥ 0` (numerator and denominator both positive). -/
private lemma B_lin_pos (n : ℕ) : 0 < B_lin n := by
  unfold B_lin
  have h1 : (0 : ℝ) ≤ (Nat.choose n 2 : ℝ) := by exact_mod_cast Nat.zero_le _
  have h2 : (0 : ℝ) ≤ (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.zero_le _
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
  have hnum : (0 : ℝ) < (2 + (n : ℝ) + (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ)) := by
    linarith
  positivity

/-- `B_lin n < 1` for `n ≥ 7`: the numerator `2 + n + C(n,2) + C(n,3)` is
    strictly less than `2^n` because the missing binomial terms
    `C(n, 4), ..., C(n, n-1)` are strictly positive. -/
private lemma B_lin_lt_one {n : ℕ} (hn : 7 ≤ n) : B_lin n < 1 := by
  unfold B_lin
  rw [div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
  -- Goal: 2 + n + C(n,2) + C(n,3) < 2^n.
  have h_3 := choose_sum_3_to_pred n (by omega)
  have h_split : Finset.Ico 3 n = insert 3 (Finset.Ico 4 n) := by
    ext; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h_no3 : 3 ∉ Finset.Ico 4 n := by simp [Finset.mem_Ico]
  rw [h_split, Finset.sum_insert h_no3] at h_3
  have h_sum_pos : (0 : ℝ) < ∑ j ∈ Finset.Ico 4 n, ((Nat.choose n j : ℕ) : ℝ) := by
    apply Finset.sum_pos
    · intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have : 0 < Nat.choose n j := Nat.choose_pos (by omega)
      exact_mod_cast this
    · exact ⟨4, by simp [Finset.mem_Ico]; omega⟩
  linarith [h_sum_pos]

/-- For `m ≥ 7`: `0 < 1 - B_lin m` (so the factor in the infinite product is positive). -/
private lemma one_minus_B_pos {m : ℕ} (hm : 7 ≤ m) : 0 < 1 - B_lin m := by
  linarith [B_lin_lt_one hm]

/-- For `m ≥ 7`: `1 - B_lin m ≤ 1` (so the factor is ≤ 1). -/
private lemma one_minus_B_le_one (m : ℕ) : 1 - B_lin m ≤ 1 := by
  linarith [B_lin_pos m]

/-- Uniform bound on finite partial products: for any `k`, `n` and `n₀`,
    if `n₀ ≥ 7` and every `m ∈ Ico (k+1) (n+1)` satisfies `m ≥ n₀`, then
    `0 ≤ ∏ m ∈ Ico (k+1) (n+1), (1 - B_lin m) ≤ 1`. -/
private lemma prod_Ico_one_minus_B_in_unit_interval (k n : ℕ) (hk : 7 ≤ k + 1) :
    0 ≤ ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m) ∧
      ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m) ≤ 1 := by
  refine ⟨Finset.prod_nonneg ?_, ?_⟩
  · intro m hm
    have hm' := (Finset.mem_Ico.mp hm).1
    linarith [(one_minus_B_pos (by omega : 7 ≤ m)).le]
  · -- Product of terms each ≤ 1 and ≥ 0 is ≤ 1.
    have h_nn : ∀ m ∈ Finset.Ico (k + 1) (n + 1), (0 : ℝ) ≤ 1 - B_lin m := by
      intro m hm
      have hm' := (Finset.mem_Ico.mp hm).1
      linarith [(one_minus_B_pos (by omega : 7 ≤ m)).le]
    have h_le : ∀ m ∈ Finset.Ico (k + 1) (n + 1), (1 : ℝ) - B_lin m ≤ 1 := by
      intro m _; exact one_minus_B_le_one m
    calc ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m)
        ≤ ∏ _ ∈ Finset.Ico (k + 1) (n + 1), (1 : ℝ) := Finset.prod_le_prod h_nn h_le
      _ = 1 := Finset.prod_const_one

/-- Bound on the first summand `n / 2^(n-1)` of `A_lin`: it equals `2n / 2^n`
    for `n ≥ 1` and `0` at `n = 0`. In both cases it is `≤ 2(n+1) / 2^n`. -/
private lemma n_div_pow_pred_le (n : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ (n - 1) ≤ 2 * ((n : ℝ) + 1) / (2 : ℝ) ^ n := by
  match n with
  | 0 => simp
  | k + 1 =>
    rw [show (k + 1 : ℕ) - 1 = k from by omega]
    rw [show ((2 : ℝ) ^ (k + 1) : ℝ) = (2 : ℝ) ^ k * 2 from pow_succ 2 k]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- Summability of `n · (1/2)^n` on ℕ. -/
private lemma summable_n_half_pow :
    Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)
  simpa using h

/-- Summability of `n² · (1/2)^n` on ℕ. -/
private lemma summable_n_sq_half_pow :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) :=
  summable_pow_mul_geometric_of_norm_lt_one 2
    (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)

/-- Summability of `n³ · (1/2)^n` on ℕ. -/
private lemma summable_n_cube_half_pow :
    Summable (fun n : ℕ => (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n) :=
  summable_pow_mul_geometric_of_norm_lt_one 3
    (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)

/-- Summability of `(1/2)^n` on ℕ. -/
private lemma summable_half_pow :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_norm_lt_one
    (show ‖(1 / 2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; norm_num)

/-- The four-term upper bound for `A_lin n` used to show summability.
    Equivalent to
    `A_lin n ≤ 2(n+1)·(1/2)^n + c₁·n·(1/2)^n + c₂·n²·(1/2)^n + c₃·n³·(1/2)^n`. -/
private noncomputable def A_lin_bound (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n
    + c 1 * (n : ℝ) * (1 / 2 : ℝ) ^ n
    + c 2 * ((n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ n
    + c 3 * ((n : ℝ) ^ 3) * (1 / 2 : ℝ) ^ n

private lemma summable_A_lin_bound : Summable A_lin_bound := by
  unfold A_lin_bound
  have h1 : Summable (fun n : ℕ => 2 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    have : (fun n : ℕ => 2 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => 2 * ((n : ℝ) * (1 / 2) ^ n) + 2 * ((1 / 2 : ℝ) ^ n) := by
      ext n; ring
    rw [this]
    exact (summable_n_half_pow.mul_left 2).add (summable_half_pow.mul_left 2)
  have h2 : Summable (fun n : ℕ => c 1 * (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    have : (fun n : ℕ => c 1 * (n : ℝ) * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => c 1 * ((n : ℝ) * (1 / 2) ^ n) := by ext; ring
    rw [this]; exact summable_n_half_pow.mul_left _
  have h3 : Summable (fun n : ℕ => c 2 * ((n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ n) := by
    have : (fun n : ℕ => c 2 * ((n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => c 2 * ((n : ℝ) ^ 2 * (1 / 2) ^ n) := by ext; ring
    rw [this]; exact summable_n_sq_half_pow.mul_left _
  have h4 : Summable (fun n : ℕ => c 3 * ((n : ℝ) ^ 3) * (1 / 2 : ℝ) ^ n) := by
    have : (fun n : ℕ => c 3 * ((n : ℝ) ^ 3) * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => c 3 * ((n : ℝ) ^ 3 * (1 / 2) ^ n) := by ext; ring
    rw [this]; exact summable_n_cube_half_pow.mul_left _
  exact ((h1.add h2).add h3).add h4

/-- Pointwise bound `A_lin n ≤ A_lin_bound n` for all n. Broken into per-term
    sub-bounds to avoid cubic nlinarith timeouts. -/
private lemma A_lin_le_bound (n : ℕ) : A_lin n ≤ A_lin_bound n := by
  unfold A_lin A_lin_bound
  rw [Nat.cast_choose_two ℝ, cast_choose_three n]
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc1 : (0 : ℝ) ≤ c 1 := by rw [c_one]; norm_num
  have hc2 : (0 : ℝ) ≤ c 2 := by rw [c_two]; norm_num
  have hc3 : (0 : ℝ) ≤ c 3 := by rw [c_three]; norm_num
  have h_pow : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
  rw [h_pow]
  -- Term 1: n / 2^(n-1) ≤ 2(n+1) · 1/2^n.
  have hT1 : (n : ℝ) / (2 : ℝ) ^ (n - 1) ≤ 2 * ((n : ℝ) + 1) * (1 / (2 : ℝ) ^ n) := by
    have := n_div_pow_pred_le n
    rwa [mul_one_div]
  -- Term 2: n · c 1 / 2^n ≤ c 1 · n · 1/2^n.
  have hT2 : (n : ℝ) * c 1 / (2 : ℝ) ^ n ≤ c 1 * (n : ℝ) * (1 / (2 : ℝ) ^ n) := by
    have h_eq : (n : ℝ) * c 1 / (2 : ℝ) ^ n = c 1 * (n : ℝ) * (1 / (2 : ℝ) ^ n) := by
      rw [mul_one_div]; ring
    linarith [h_eq]
  -- Term 3: n(n-1)/2 · c 2 / 2^n ≤ c 2 · n² · 1/2^n, from n(n-1) ≤ n² (for n ≥ 0).
  have hT3 : (n : ℝ) * ((n : ℝ) - 1) / 2 * c 2 / (2 : ℝ) ^ n
      ≤ c 2 * ((n : ℝ) ^ 2) * (1 / (2 : ℝ) ^ n) := by
    rw [mul_one_div, div_le_div_iff_of_pos_right hp_pos]
    -- n(n-1) ≤ n² (since n ≥ 0).
    have h_quad : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith [hn_nn]
    nlinarith [h_quad, hc2, hn_nn, sq_nonneg (n : ℝ)]
  -- Term 4: n(n-1)(n-2)/6 · c 3 / 2^n ≤ c 3 · n³ · 1/2^n.
  have hT4 : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 * c 3 / (2 : ℝ) ^ n
      ≤ c 3 * ((n : ℝ) ^ 3) * (1 / (2 : ℝ) ^ n) := by
    rw [mul_one_div, div_le_div_iff_of_pos_right hp_pos]
    -- n(n-1)(n-2) ≤ n³ for n ≥ 0 : follows from n³ - n(n-1)(n-2) = 3n² - 2n ≥ 0.
    have h_cube : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ≤ (n : ℝ) ^ 3 := by
      have h_id : (n : ℝ) ^ 3 - (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
          3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) := by ring
      suffices h_pos : 0 ≤ 3 * (n : ℝ) ^ 2 - 2 * (n : ℝ) by linarith
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith [this]
    nlinarith [h_cube, hc3, mul_nonneg hn_nn hn_nn,
               mul_nonneg (mul_nonneg hn_nn hn_nn) hn_nn]
  -- Put it together: A_lin n = n/2^(n-1) + (n·c1 + n(n-1)/2·c2 + n(n-1)(n-2)/6·c3)/2^n.
  rw [add_div, add_div]
  linarith [hT1, hT2, hT3, hT4]

/-- Summability of `A_lin` on ℕ. Uses the bound `A_lin n ≤ A_lin_bound n`. -/
private lemma summable_A_lin : Summable A_lin := by
  apply summable_A_lin_bound.of_norm_bounded_eventually_nat
  filter_upwards with n
  rw [Real.norm_eq_abs, abs_of_nonneg (A_lin_nonneg n)]
  exact A_lin_le_bound n

/-- Summability of `|A_lin|` on ℕ. Since A_lin ≥ 0, this equals `summable_A_lin`. -/
private lemma summable_A_lin_abs : Summable (fun n : ℕ => |A_lin n|) := by
  have h := summable_A_lin
  have h_eq : (fun n : ℕ => |A_lin n|) = A_lin := by
    ext n; exact abs_of_nonneg (A_lin_nonneg n)
  rw [h_eq]; exact h

/-- For each fixed `k ≥ 6`, the finite inner product converges as `n → ∞`
    to the tprod over `{m // k < m}`. Specialisation of `tendsto_prod_Ico_B`. -/
private lemma tendsto_inner_prod_for_k (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m))
      Filter.atTop
      (nhds (∏' m : {m : ℕ // k < m}, (1 - B_lin m.val))) := by
  have h := tendsto_prod_Ico_B (k + 1)
  -- h tends to `∏' m : {m // k + 1 ≤ m}, (1 - B_lin m.val)`, which equals the
  -- target since `k < m ↔ k + 1 ≤ m` on ℕ (definitionally).
  exact h

/-- Summability of `A_lin` on the subtype `{k // n₀ ≤ k}`. -/
private lemma summable_A_lin_subtype (n₀ : ℕ) :
    Summable (fun k : {k : ℕ // n₀ ≤ k} => A_lin k.val) :=
  summable_A_lin.comp_injective Subtype.val_injective

/-- Summability of `fun j => A_lin (n₀ + j)` on ℕ (shifted). -/
private lemma summable_A_lin_shifted (n₀ : ℕ) :
    Summable (fun j : ℕ => A_lin (n₀ + j)) := by
  have h := (summable_nat_add_iff n₀).mpr summable_A_lin
  -- h : Summable (fun n => A_lin (n + n₀))
  convert h using 1
  ext j; rw [add_comm]

/-- Convert ℕ tsum to subtype tsum (via shiftEquiv). -/
private lemma tsum_shifted_eq_subtype (n₀ : ℕ) (h : ℕ → ℝ) :
    ∑' j : ℕ, h (n₀ + j) =
      ∑' k : {k : ℕ // n₀ ≤ k}, h k.val := by
  have := (shiftEquiv n₀).tsum_eq (fun k : {k // n₀ ≤ k} => h k.val)
  -- this : ∑' j, h ((shiftEquiv n₀ j).val) = ∑' k, h k.val
  -- (shiftEquiv n₀ j).val = n₀ + j
  simpa using this

/-- Sum convergence: as `n → ∞`, the finite double-sum from `c_iterate`
    converges to the infinite series over the subtype. Uses Tannery's theorem
    (`tendsto_tsum_of_dominated_convergence`) with ℕ indexing (via shiftEquiv). -/
private lemma tendsto_sum_Ico_A_prod (n₀ : ℕ) (hn₀ : 7 ≤ n₀) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Ico n₀ (n + 1),
        A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m))
      Filter.atTop
      (nhds (∑' k : {k : ℕ // n₀ ≤ k},
        A_lin k * ∏' m : {m : ℕ // k.val < m}, (1 - B_lin m.val))) := by
  -- Define shifted functions (indexed by j ∈ ℕ, via k = n₀ + j).
  set f : ℕ → ℕ → ℝ := fun n j =>
    if n₀ + j ≤ n
    then A_lin (n₀ + j) * ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m)
    else 0 with hf_def
  set g : ℕ → ℝ := fun j =>
    A_lin (n₀ + j) * ∏' m : {m : ℕ // n₀ + j < m}, (1 - B_lin m.val) with hg_def
  set bound : ℕ → ℝ := fun j => A_lin (n₀ + j) with hb_def
  -- Hypothesis 1: Summable bound.
  have h_sum : Summable bound := summable_A_lin_shifted n₀
  -- Hypothesis 2: Pointwise convergence f n j → g j.
  have h_ptw : ∀ j : ℕ, Filter.Tendsto (fun n => f n j) Filter.atTop (nhds (g j)) := by
    intro j
    have h_inner := tendsto_inner_prod_for_k (n₀ + j)
    have h_scale : Filter.Tendsto
        (fun n : ℕ => A_lin (n₀ + j) *
            ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m))
        Filter.atTop (nhds (g j)) := h_inner.const_mul (A_lin (n₀ + j))
    have h_ev : (fun n => f n j) =ᶠ[Filter.atTop]
        (fun n : ℕ => A_lin (n₀ + j) *
            ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m)) := by
      filter_upwards [Filter.eventually_ge_atTop (n₀ + j)] with n hn
      show f n j = _
      rw [hf_def]; dsimp only
      rw [if_pos hn]
    exact Filter.Tendsto.congr' h_ev.symm h_scale
  -- Hypothesis 3: uniform bound ‖f n j‖ ≤ bound j.
  have h_bnd : ∀ᶠ n in Filter.atTop, ∀ j : ℕ, ‖f n j‖ ≤ bound j := by
    filter_upwards with n j
    show ‖f n j‖ ≤ bound j
    rw [hf_def, hb_def]; dsimp only
    by_cases hnj : n₀ + j ≤ n
    · rw [if_pos hnj]
      have hA_nn := A_lin_nonneg (n₀ + j)
      have hk7 : 7 ≤ n₀ + j + 1 := by omega
      have h_prod_bound := prod_Ico_one_minus_B_in_unit_interval (n₀ + j) n hk7
      have h_mul_nn : (0 : ℝ) ≤ A_lin (n₀ + j) *
          ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m) :=
        mul_nonneg hA_nn h_prod_bound.1
      rw [Real.norm_eq_abs, abs_of_nonneg h_mul_nn]
      calc A_lin (n₀ + j) * ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m)
          ≤ A_lin (n₀ + j) * 1 :=
            mul_le_mul_of_nonneg_left h_prod_bound.2 hA_nn
        _ = A_lin (n₀ + j) := by ring
    · rw [if_neg hnj]
      simp [A_lin_nonneg (n₀ + j)]
  -- Apply Tannery.
  have h_tannery : Filter.Tendsto (fun n : ℕ => ∑' j : ℕ, f n j) Filter.atTop
      (nhds (∑' j : ℕ, g j)) :=
    tendsto_tsum_of_dominated_convergence h_sum h_ptw h_bnd
  -- Convert LHS: ∑' j : ℕ, f n j = ∑ k ∈ Ico n₀ (n+1), A_lin k * (finite prod).
  have h_lhs : (fun n : ℕ => ∑' j : ℕ, f n j) =ᶠ[Filter.atTop]
      (fun n : ℕ => ∑ k ∈ Finset.Ico n₀ (n + 1),
        A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m)) := by
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    -- Support of j ↦ f n j is {j | n₀ + j ≤ n}; outside `range (n + 1 - n₀)`, f = 0.
    have h_tsum_eq : ∑' j : ℕ, f n j =
        ∑ j ∈ Finset.range (n + 1 - n₀), f n j := by
      apply tsum_eq_sum
      intro j hj
      show f n j = 0
      rw [hf_def]; dsimp only
      rw [if_neg]
      intro h_le
      apply hj
      simp only [Finset.mem_range]
      omega
    rw [h_tsum_eq]
    -- Each term in range: f n j = A_lin (n₀+j) * (finite prod).
    have h_term_eq : ∀ j ∈ Finset.range (n + 1 - n₀), f n j =
        A_lin (n₀ + j) * ∏ m ∈ Finset.Ico (n₀ + j + 1) (n + 1), (1 - B_lin m) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      show f n j = _
      rw [hf_def]; dsimp only
      rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl h_term_eq]
    -- Reindex: ∑ j ∈ range (n+1-n₀), h (n₀+j) = ∑ k ∈ Ico n₀ (n+1), h k,
    -- by reverse direction of Finset.sum_Ico_eq_sum_range.
    exact (Finset.sum_Ico_eq_sum_range
      (fun k => A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), ((1 : ℝ) - B_lin m))
      n₀ (n + 1)).symm
  -- Convert RHS: ∑' j : ℕ, g j = ∑' k : subtype, ...
  have h_rhs : ∑' j : ℕ, g j =
      ∑' k : {k : ℕ // n₀ ≤ k},
        A_lin k * ∏' m : {m : ℕ // k.val < m}, (1 - B_lin m.val) := by
    show ∑' j : ℕ, _ = _
    rw [hg_def]
    have := (shiftEquiv n₀).tsum_eq (fun k : {k // n₀ ≤ k} =>
      A_lin k.val * ∏' m : {m : ℕ // k.val < m}, (1 - B_lin m.val))
    simpa using this
  rw [← h_rhs]
  exact Filter.Tendsto.congr' h_lhs h_tannery

/-- Theorem 4.10 (explicit form): for any `n₀ ≥ 7`, the limit is given by
    `L = c_{n₀-1} · ∏_{m ≥ n₀} (1 - B_m) + ∑_{k ≥ n₀} A_k · ∏_{m > k} (1 - B_m)`.
    Proved by taking the limit of `c_iterate`: the finite identity
    `c n = c (n₀-1) · P_n + S_n` passes to the limit by `tendsto_prod_Ico_B`
    and `tendsto_sum_Ico_A_prod`. Combined with `c_limit_exists` via
    uniqueness of limits. -/
theorem c_limit_formula (n₀ : ℕ) (hn₀ : 7 ≤ n₀) :
    ∃ L : ℝ, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L) ∧
      L = c (n₀ - 1) * ∏' m : {m : ℕ // n₀ ≤ m}, (1 - B_lin m.val) +
          ∑' k : {k : ℕ // n₀ ≤ k},
            A_lin k * ∏' m : {m : ℕ // k.val < m}, (1 - B_lin m.val) := by
  obtain ⟨L, hL⟩ := c_limit_exists
  refine ⟨L, hL, ?_⟩
  -- The finite iteration identity.
  have h_c_eq : ∀ n, n₀ ≤ n →
      c n = c (n₀ - 1) * (∏ m ∈ Finset.Ico n₀ (n + 1), (1 - B_lin m)) +
            ∑ k ∈ Finset.Ico n₀ (n + 1),
              A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), (1 - B_lin m) :=
    c_iterate n₀ hn₀
  -- Product part converges.
  have h_prod_tendsto := tendsto_prod_Ico_B n₀
  -- Sum part converges.
  have h_sum_tendsto := tendsto_sum_Ico_A_prod n₀ hn₀
  -- Combined: the RHS of c_iterate converges.
  have h_comb_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          c (n₀ - 1) * (∏ m ∈ Finset.Ico n₀ (n + 1), ((1 : ℝ) - B_lin m)) +
            ∑ k ∈ Finset.Ico n₀ (n + 1),
              A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), (1 - B_lin m))
        Filter.atTop
        (nhds
          (c (n₀ - 1) * (∏' m : {m : ℕ // n₀ ≤ m}, ((1 : ℝ) - B_lin m.val)) +
            ∑' k : {k : ℕ // n₀ ≤ k},
              A_lin k * ∏' m : {m : ℕ // k.val < m}, (1 - B_lin m.val))) :=
    (h_prod_tendsto.const_mul (c (n₀ - 1))).add h_sum_tendsto
  -- `c` agrees eventually with the combined expression.
  have h_ev : (fun n => c n) =ᶠ[Filter.atTop]
      (fun n => c (n₀ - 1) * (∏ m ∈ Finset.Ico n₀ (n + 1), ((1 : ℝ) - B_lin m)) +
                ∑ k ∈ Finset.Ico n₀ (n + 1),
                  A_lin k * ∏ m ∈ Finset.Ico (k + 1) (n + 1), (1 - B_lin m)) := by
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    exact h_c_eq n hn
  -- Transfer and apply uniqueness.
  have h_lim := Filter.Tendsto.congr' h_ev.symm h_comb_tendsto
  exact tendsto_nhds_unique hL h_lim

/-! ### Bridge from `Δ` to `c` (Proposition 4.3)

  We need to show that `c n` is the first-order coefficient of
  `Δ_{n, 1/2 − δ}` as `δ → 0⁺`. This bridges the standalone
  `c`-recursion to the actual deficit.

  The proof is by strong induction on `n`. For `n ≥ 2` it uses
  `deficit_succ` together with a Taylor estimate for the constant
  term and a perturbation bound for the suffix-min.

  We currently prove the base case `n = 1` (an exact identity);
  the general case is sketched with sub-sorries identifying the
  remaining real-analysis lemmas. -/

/-- Base case n = 1 of Proposition 4.3: `Δ_{1, 1/2 − δ} = c_1 · δ` (exactly,
    not just to first order). Indeed `w(1/2 − δ, 1) = 1/2 − δ` and `c_1 = 1`. -/
theorem deficit_first_order_one (δ : ℝ) : deficit (1/2 - δ) 1 = c 1 * δ := by
  unfold deficit
  rw [w_one, c_one]
  ring

/-! Sub-lemmas needed for the inductive step (all proved below):

  1. **Taylor bound for the constant term.** For each `n ≥ 1`, there exist
     `M₁ δ₁ > 0` such that for `δ ∈ (0, δ₁)`:
     `|((1/2 + δ)^n − (1/2 − δ)^n)/2 − n·δ/2^(n−1)| ≤ M₁ · δ²`.
     The bound comes from binomial expansion: only odd-`k` terms survive,
     and terms with `k ≥ 3` contribute `O(δ³)`.

  2. **Binomial weight perturbation.** For `n ≥ 1`, `j ∈ [1, n−1]`, there
     exist `M₂` such that for small `δ`:
     `|C(n,j) (1/2 − δ)^(n−j) (1/2 + δ)^j − C(n,j)/2^n| ≤ M₂ · δ`.

  3. **Suffix-min perturbation.** Under the IH, for each `j` with
     `1 ≤ j < n`, `suffMinDelta (1/2 − δ) j n = (suffMin j n) · δ + O(δ²)`.
     Uses the fact that `min` is `1`-Lipschitz: if each `|Δ_m − c_m·δ| ≤ M·δ²`,
     then `|min Δ_m − (min c_m)·δ| ≤ M·δ²`. -/

/-- Lipschitz bound on `a^k - b^k` for `|a|, |b| ≤ 1`. (Placed here as it is
    used by both `constant_term_taylor` and `binom_weight_perturb` below.) -/
private lemma pow_sub_pow_bound (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ k * |a - b| := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h_rec : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h_rec]
    have habk : |b ^ n| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hb
    have hadd : |a * (a ^ n - b ^ n) + (a - b) * b ^ n|
        ≤ |a * (a ^ n - b ^ n)| + |(a - b) * b ^ n| := abs_add_le _ _
    have hsum_le : |a * (a ^ n - b ^ n)| + |(a - b) * b ^ n|
        ≤ ((n : ℝ) + 1) * |a - b| := by
      rw [abs_mul, abs_mul]
      have h1 : |a| * |a ^ n - b ^ n| ≤ 1 * ((n : ℝ) * |a - b|) :=
        mul_le_mul ha ih (abs_nonneg _) (by norm_num)
      have h2 : |a - b| * |b ^ n| ≤ |a - b| * 1 :=
        mul_le_mul_of_nonneg_left habk (abs_nonneg _)
      linarith
    have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h_cast]
    linarith

/-- Sub-lemma 1: Taylor bound for the constant term.
    Uses `geom_sum₂_mul`: `(∑ (1/2+δ)^i (1/2-δ)^(n-1-i)) · 2δ = (1/2+δ)^n - (1/2-δ)^n`.
    Divide by 2 to get `f(δ) = δ · ∑ (1/2+δ)^i (1/2-δ)^(n-1-i)`. At δ=0 the sum is
    `n · (1/2)^(n-1) = n / 2^(n-1)`, so `f(δ) - n·δ/2^(n-1) = δ · ∑ [...]` where each
    summand is bounded by `(n-1)·δ` (Lipschitz of `A·B − C·D`). Total: `n(n-1)·δ²`. -/
private lemma constant_term_taylor (n : ℕ) (hn : 1 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |((1/2 + δ) ^ n - (1/2 - δ) ^ n) / 2 - (n : ℝ) * δ / (2 : ℝ) ^ (n - 1)|
        ≤ M * δ ^ 2 := by
  refine ⟨(n : ℝ) * (n - 1), 1/2, by norm_num, ?_⟩
  intro δ hδ_pos hδ_lt
  -- Apply geom_sum₂_mul.
  have h_geom := geom_sum₂_mul ((1/2 : ℝ) + δ) ((1/2 : ℝ) - δ) n
  -- h_geom : (∑ i ∈ range n, (1/2+δ)^i · (1/2-δ)^(n-1-i)) · ((1/2+δ) - (1/2-δ)) =
  --         (1/2+δ)^n - (1/2-δ)^n
  have h_sub : ((1/2 : ℝ) + δ) - (1/2 - δ) = 2 * δ := by ring
  rw [h_sub] at h_geom
  -- h_geom : (∑ ...) · (2δ) = (1/2+δ)^n - (1/2-δ)^n
  -- Divide by 2: f(δ) := ((1/2+δ)^n - (1/2-δ)^n)/2 = δ · (∑ ...)
  have h_f_form : ((1/2 : ℝ) + δ) ^ n - (1 / 2 - δ) ^ n =
      2 * δ * ∑ i ∈ Finset.range n,
        ((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) := by linarith
  -- Rewrite the goal.
  have h_f_half : ((1/2 : ℝ) + δ) ^ n / 2 - (1/2 - δ) ^ n / 2 =
      δ * ∑ i ∈ Finset.range n,
        ((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) := by linarith
  -- Also: n δ / 2^(n-1) = δ · n · (1/2)^(n-1) = δ · ∑ i, (1/2)^(n-1).
  have h_constant : (n : ℝ) * δ / (2 : ℝ) ^ (n - 1) = δ * ∑ _ ∈ Finset.range n,
      ((1/2 : ℝ) ^ (n - 1)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (1/2 : ℝ) ^ (n - 1) = 1 / 2^(n - 1) := by rw [div_pow, one_pow]
    rw [this]; ring
  -- Compute the goal.
  have h_diff : ((1/2 : ℝ) + δ) ^ n / 2 - (1/2 - δ) ^ n / 2 -
      (n : ℝ) * δ / (2 : ℝ) ^ (n - 1) =
      δ * ∑ i ∈ Finset.range n,
        (((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1)) := by
    rw [h_f_half, h_constant, ← mul_sub, ← Finset.sum_sub_distrib]
  have h_goal_eq : ((1/2 : ℝ) + δ) ^ n / 2 - (1/2 - δ) ^ n / 2 -
      (n : ℝ) * δ / (2 : ℝ) ^ (n - 1) =
      (((1/2 : ℝ) + δ) ^ n - (1/2 - δ) ^ n) / 2 - (n : ℝ) * δ / (2 : ℝ) ^ (n - 1) := by
    ring
  -- The main goal: |((1/2+δ)^n - (1/2-δ)^n)/2 - n δ/2^(n-1)| ≤ n(n-1) δ²
  rw [← h_goal_eq, h_diff, abs_mul, abs_of_pos hδ_pos]
  -- Goal: δ * |∑ ...| ≤ n(n-1) δ²
  -- Bound the sum: each term is ≤ (n-1) δ.
  have h_sum_bound : |∑ i ∈ Finset.range n,
      (((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1))| ≤
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) * δ := by
    have h_term_bound : ∀ i ∈ Finset.range n,
        |((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1)| ≤
          ((n - 1 : ℕ) : ℝ) * δ := by
      intro i hi
      have hi_lt_n := Finset.mem_range.mp hi
      -- (1/2)^(n-1) = (1/2)^i · (1/2)^(n-1-i) for i ≤ n-1.
      have h_split : (1/2 : ℝ) ^ (n - 1) = (1/2 : ℝ) ^ i * (1/2 : ℝ) ^ (n - 1 - i) := by
        rw [← pow_add]
        congr 1; omega
      rw [h_split]
      -- Now: |((1/2+δ)^i (1/2-δ)^(n-1-i) - (1/2)^i (1/2)^(n-1-i)|.
      -- Apply A·B - C·D = (A-C)·B + C·(B-D).
      have h_factor : ((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) -
            (1/2 : ℝ) ^ i * (1/2 : ℝ) ^ (n - 1 - i) =
          (((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i) * (1/2 - δ) ^ (n - 1 - i) +
          (1/2 : ℝ) ^ i * ((1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i)) := by ring
      rw [h_factor]
      have h_half : |(1/2 : ℝ)| ≤ 1 := by norm_num
      have h_half_plus : |(1/2 + δ : ℝ)| ≤ 1 := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 1/2 + δ)]; linarith
      have h_half_minus : |(1/2 - δ : ℝ)| ≤ 1 := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < 1/2 - δ)]; linarith
      -- Bound each factor.
      have hp1 : |((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i| ≤ (i : ℝ) * δ := by
        have := pow_sub_pow_bound (1/2 + δ) (1/2 : ℝ) h_half_plus h_half i
        have h_abs : |((1/2 : ℝ) + δ) - 1/2| = δ := by
          rw [show ((1/2 : ℝ) + δ - 1/2) = δ from by ring, abs_of_pos hδ_pos]
        rw [h_abs] at this; exact this
      have hp2 : |((1/2 : ℝ) - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i)| ≤
            ((n - 1 - i : ℕ) : ℝ) * δ := by
        have := pow_sub_pow_bound (1/2 - δ) (1/2 : ℝ) h_half_minus h_half (n - 1 - i)
        have h_abs : |((1/2 : ℝ) - δ) - 1/2| = δ := by
          rw [show ((1/2 : ℝ) - δ - 1/2) = -δ from by ring, abs_neg, abs_of_pos hδ_pos]
        rw [h_abs] at this; exact this
      have h_sum_le : |(((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i) * (1/2 - δ) ^ (n - 1 - i) +
            (1/2 : ℝ) ^ i * ((1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i))| ≤
          ((i : ℝ) * δ) * 1 + 1 * (((n - 1 - i : ℕ) : ℝ) * δ) := by
        have h_triangle := abs_add_le
          ((((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i) * (1/2 - δ) ^ (n - 1 - i))
          ((1/2 : ℝ) ^ i * ((1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i)))
        have h_eq : |(((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i) * (1/2 - δ) ^ (n - 1 - i)| +
                    |(1/2 : ℝ) ^ i * ((1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i))| =
                    |((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i| * |(1/2 - δ) ^ (n - 1 - i)| +
                    |(1/2 : ℝ) ^ i| * |(1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i)| := by
          rw [abs_mul, abs_mul]
        have h_prod_B : |(1/2 - δ : ℝ) ^ (n - 1 - i)| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h_half_minus
        have h_prod_C : |(1/2 : ℝ) ^ i| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h_half
        have h_idδ_nn : (0 : ℝ) ≤ (i : ℝ) * δ := by positivity
        have hp1' : |((1/2 : ℝ) + δ) ^ i - (1/2 : ℝ) ^ i| * |(1/2 - δ) ^ (n - 1 - i)| ≤
            (i : ℝ) * δ * 1 :=
          mul_le_mul hp1 h_prod_B (abs_nonneg _) h_idδ_nn
        have hp2' : |(1/2 : ℝ) ^ i| * |(1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1 - i)| ≤
            1 * (((n - 1 - i : ℕ) : ℝ) * δ) :=
          mul_le_mul h_prod_C hp2 (abs_nonneg _) (by norm_num)
        linarith
      have h_cast : ((i : ℝ) * δ) * 1 + 1 * (((n - 1 - i : ℕ) : ℝ) * δ) =
          ((n - 1 : ℕ) : ℝ) * δ := by
        have h_sum_cast : (i : ℝ) + ((n - 1 - i : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
          have h_nat : (n - 1 - i : ℕ) + i = n - 1 := by omega
          have h_cast_eq := congrArg (Nat.cast (R := ℝ)) h_nat
          push_cast at h_cast_eq
          linarith
        have : ((i : ℝ) * δ) * 1 + 1 * (((n - 1 - i : ℕ) : ℝ) * δ) =
            ((i : ℝ) + ((n - 1 - i : ℕ) : ℝ)) * δ := by ring
        rw [this, h_sum_cast]
      linarith
    -- Sum the per-term bounds.
    calc |∑ i ∈ Finset.range n,
          (((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1))|
        ≤ ∑ i ∈ Finset.range n,
            |((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range n, ((n - 1 : ℕ) : ℝ) * δ := Finset.sum_le_sum h_term_bound
      _ = (n : ℝ) * (((n - 1 : ℕ) : ℝ) * δ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * δ := by ring
  -- Final bound.
  have hn_sub_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h : (n - 1 : ℕ) + 1 = n := by omega
    have h_cast_eq := congrArg (Nat.cast (R := ℝ)) h
    push_cast at h_cast_eq
    linarith
  have : δ * |∑ i ∈ Finset.range n,
          (((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1))|
      ≤ δ * ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * δ) :=
    mul_le_mul_of_nonneg_left h_sum_bound (le_of_lt hδ_pos)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnn1 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc δ * |∑ i ∈ Finset.range n,
          (((1/2 : ℝ) + δ) ^ i * (1/2 - δ) ^ (n - 1 - i) - (1/2 : ℝ) ^ (n - 1))|
      ≤ δ * ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * δ) := this
    _ = δ * ((n : ℝ) * ((n : ℝ) - 1) * δ) := by rw [hn_sub_cast]
    _ = (n : ℝ) * ((n : ℝ) - 1) * δ ^ 2 := by ring

/-- Sub-lemma 2: Binomial weight perturbation. Using the identity
    `A·B − C·D = (A−C)·B + C·(B−D)` and the Lipschitz bound on powers. -/
private lemma binom_weight_perturb (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |(Nat.choose n j : ℝ) * (1/2 - δ) ^ (n - j) * (1/2 + δ) ^ j -
        (Nat.choose n j : ℝ) / (2 : ℝ) ^ n| ≤ M * δ := by
  -- n ≥ 2 since j ≥ 1 and j ≤ n - 1.
  have hn2 : 2 ≤ n := by omega
  refine ⟨(Nat.choose n j : ℝ) * n, 1/2, by norm_num, ?_⟩
  intro δ hδ_pos hδ_lt
  have hC_nn : (0 : ℝ) ≤ (Nat.choose n j : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Split (1/2)^n = (1/2)^(n-j) · (1/2)^j.
  have h_pow_split : (1/2 : ℝ) ^ n = (1/2 : ℝ) ^ (n - j) * (1/2 : ℝ) ^ j := by
    rw [← pow_add]
    congr 1; omega
  have h_div_eq : (1 : ℝ) / (2 : ℝ) ^ n = (1/2 : ℝ) ^ n := by
    rw [one_div, ← inv_pow, show ((2 : ℝ)⁻¹ : ℝ) = (1/2 : ℝ) from by norm_num]
  -- Factor the difference.
  have h_factor : (Nat.choose n j : ℝ) * (1/2 - δ) ^ (n - j) * (1/2 + δ) ^ j -
        (Nat.choose n j : ℝ) / (2 : ℝ) ^ n =
      (Nat.choose n j : ℝ) *
        (((1/2 - δ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j +
         (1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)) := by
    have : (Nat.choose n j : ℝ) / (2 : ℝ) ^ n =
        (Nat.choose n j : ℝ) * ((1/2 : ℝ) ^ (n - j) * (1/2 : ℝ) ^ j) := by
      rw [show ((Nat.choose n j : ℝ) / (2 : ℝ) ^ n) = (Nat.choose n j : ℝ) * (1 / (2 : ℝ)^n) from
        by ring]
      rw [h_div_eq, h_pow_split]
    rw [this]; ring
  rw [h_factor, abs_mul, abs_of_nonneg hC_nn]
  -- Bound the inner expression.
  have h_half : |(1/2 : ℝ)| ≤ 1 := by norm_num
  have h_half_plus : |(1/2 + δ : ℝ)| ≤ 1 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1/2 + δ)]; linarith
  have h_half_minus : |(1/2 - δ : ℝ)| ≤ 1 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1/2 - δ)]; linarith
  -- Bound on power differences.
  have h_diff1 : |(1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)| ≤ ((n - j : ℕ) : ℝ) * δ := by
    have h := pow_sub_pow_bound (1/2 - δ) (1/2 : ℝ) h_half_minus h_half (n - j)
    have h_abs : |(1/2 - δ : ℝ) - 1/2| = δ := by
      rw [show ((1/2 : ℝ) - δ - 1/2) = -δ from by ring, abs_neg, abs_of_pos hδ_pos]
    rw [h_abs] at h
    exact h
  have h_diff2 : |(1/2 + δ : ℝ) ^ j - (1/2 : ℝ) ^ j| ≤ j * δ := by
    have h := pow_sub_pow_bound (1/2 + δ) (1/2 : ℝ) h_half_plus h_half j
    have h_abs : |(1/2 + δ : ℝ) - 1/2| = δ := by
      rw [show ((1/2 : ℝ) + δ - 1/2) = δ from by ring, abs_of_pos hδ_pos]
    rw [h_abs] at h
    exact h
  -- Assemble.
  have h_halfpow_le : |(1/2 + δ : ℝ) ^ j| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h_half_plus
  have h_halfpow_le' : |(1/2 : ℝ) ^ (n - j)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h_half
  have h_inner_bound : |((1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j +
        (1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)| ≤ (n : ℝ) * δ := by
    have h_triangle : |((1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j +
          (1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)|
        ≤ |((1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j| +
          |(1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)| := abs_add_le _ _
    have h_eq_mul : |((1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j| +
        |(1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)| =
        |(1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j| +
        |(1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j - (1/2 : ℝ) ^ j| := by
      rw [abs_mul, abs_mul]
    have h_term_bound : |(1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j| +
        |(1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j - (1/2 : ℝ) ^ j| ≤
        ((n - j : ℕ) : ℝ) * δ * 1 + 1 * ((j : ℝ) * δ) := by
      have hδ_nn : (0 : ℝ) ≤ δ := le_of_lt hδ_pos
      have hnj_nn : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) * δ := by positivity
      have hp1 : |(1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j| ≤
          ((n - j : ℕ) : ℝ) * δ * 1 :=
        mul_le_mul h_diff1 h_halfpow_le (abs_nonneg _) hnj_nn
      have hp2 : |(1/2 : ℝ) ^ (n - j)| * |(1/2 + δ) ^ j - (1/2 : ℝ) ^ j| ≤
          1 * ((j : ℝ) * δ) :=
        mul_le_mul h_halfpow_le' h_diff2 (abs_nonneg _) (by norm_num)
      linarith
    have h_sum_cast : ((n - j : ℕ) : ℝ) + (j : ℝ) = (n : ℝ) := by
      have h : ((n - j : ℕ) + j : ℕ) = n := by omega
      have := congrArg (Nat.cast (R := ℝ)) h
      push_cast at this
      linarith
    have h_final_eq : ((n - j : ℕ) : ℝ) * δ * 1 + 1 * ((j : ℝ) * δ) = (n : ℝ) * δ := by
      have : ((n - j : ℕ) : ℝ) * δ * 1 + 1 * ((j : ℝ) * δ) =
          (((n - j : ℕ) : ℝ) + (j : ℝ)) * δ := by ring
      rw [this, h_sum_cast]
    linarith
  calc (Nat.choose n j : ℝ) * |((1/2 - δ : ℝ) ^ (n - j) - (1/2 : ℝ) ^ (n - j)) * (1/2 + δ) ^ j +
        (1/2 : ℝ) ^ (n - j) * ((1/2 + δ) ^ j - (1/2 : ℝ) ^ j)|
      ≤ (Nat.choose n j : ℝ) * ((n : ℝ) * δ) := by
        apply mul_le_mul_of_nonneg_left h_inner_bound hC_nn
    _ = (Nat.choose n j : ℝ) * n * δ := by ring

/-- Lipschitz of `Finset.inf'`: if `|f m - g m| ≤ K` pointwise, then
    `|inf' f - inf' g| ≤ K`. -/
private lemma finset_inf'_lipschitz {β : Type*} {s : Finset β} (hs : s.Nonempty)
    (f g : β → ℝ) (K : ℝ) (h : ∀ m ∈ s, |f m - g m| ≤ K) :
    |s.inf' hs f - s.inf' hs g| ≤ K := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- -K ≤ inf' f - inf' g, i.e., inf' g - K ≤ inf' f.
    rw [neg_le, neg_sub]
    -- Goal: inf' g - inf' f ≤ K, equivalently inf' g ≤ inf' f + K.
    obtain ⟨m, hm, h_eq⟩ := Finset.exists_mem_eq_inf' hs f
    have h_bd := h m hm
    rw [abs_le] at h_bd
    have h_g_le : s.inf' hs g ≤ g m := Finset.inf'_le _ hm
    linarith
  · -- inf' f - inf' g ≤ K.
    obtain ⟨m, hm, h_eq⟩ := Finset.exists_mem_eq_inf' hs g
    have h_bd := h m hm
    rw [abs_le] at h_bd
    have h_f_le : s.inf' hs f ≤ f m := Finset.inf'_le _ hm
    linarith

/-- Scalar multiplication and `Finset.inf'`: for `δ > 0`,
    `(s.inf' H f) * δ = s.inf' H (fun m => f m * δ)`. -/
private lemma finset_inf'_mul_pos {β : Type*} {s : Finset β} (hs : s.Nonempty)
    (f : β → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    s.inf' hs f * δ = s.inf' hs (fun m => f m * δ) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro m hm
    have h := Finset.inf'_le f hm
    exact mul_le_mul_of_nonneg_right h (le_of_lt hδ)
  · obtain ⟨m₀, hm₀, h_eq⟩ := Finset.exists_mem_eq_inf' hs f
    -- s.inf' hs f = f m₀.
    rw [h_eq]
    -- Goal: s.inf' hs (fun m => f m * δ) ≤ f m₀ * δ.
    exact Finset.inf'_le (fun m => f m * δ) hm₀

/-- Sub-lemma 3: Suffix-min perturbation under the IH. -/
private lemma suffMinDelta_first_order (n j : ℕ) (hn : 2 ≤ n) (hj : 1 ≤ j) (hjn : j < n)
    (h_ih : ∀ m, 1 ≤ m → m < n →
      ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
        |deficit (1/2 - δ) m - c m * δ| ≤ M * δ ^ 2) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |suffMinDelta (1/2 - δ) j n - suffMin j n * δ| ≤ M * δ ^ 2 := by
  -- Extract IH data per m ∈ [j, n).
  have hmem_props : ∀ m, m ∈ Finset.Ico j n → 1 ≤ m ∧ m < n := by
    intro m hm
    have := Finset.mem_Ico.mp hm
    exact ⟨by omega, this.2⟩
  choose! M_fn δ_fn hM_data using
    fun m (hm : m ∈ Finset.Ico j n) => h_ih m (hmem_props m hm).1 (hmem_props m hm).2
  have h_ne : (Finset.Ico j n).Nonempty := ⟨j, Finset.mem_Ico.mpr ⟨le_refl _, hjn⟩⟩
  have h_ne_att : (Finset.Ico j n).attach.Nonempty := ⟨⟨j, Finset.mem_Ico.mpr ⟨le_refl _, hjn⟩⟩,
    Finset.mem_attach _ _⟩
  set M_max : ℝ := (Finset.Ico j n).attach.sup' h_ne_att (fun m => M_fn m.val) with hM_def
  set δ_min : ℝ := (Finset.Ico j n).attach.inf' h_ne_att (fun m => δ_fn m.val) with hδ_def
  have hδ_min_pos : 0 < δ_min := by
    rw [hδ_def]
    obtain ⟨m₀, _, h_eq⟩ :=
      Finset.exists_mem_eq_inf' h_ne_att (fun m : {x // x ∈ Finset.Ico j n} => δ_fn m.val)
    rw [h_eq]
    exact (hM_data m₀.val m₀.property).1
  refine ⟨M_max, δ_min, hδ_min_pos, ?_⟩
  intro δ hδ_pos hδ_lt
  -- Each m's bound applies for this δ.
  have h_per_m : ∀ m ∈ (Finset.Ico j n).attach,
      |deficit (1 / 2 - δ) m.val - c m.val * δ| ≤ M_max * δ ^ 2 := by
    intro m hm_att
    have hδ_m : δ < δ_fn m.val := by
      have h_le : δ_min ≤ δ_fn m.val :=
        Finset.inf'_le (fun m : {x // x ∈ Finset.Ico j n} => δ_fn m.val) hm_att
      linarith
    have h_bound : |deficit (1 / 2 - δ) m.val - c m.val * δ| ≤ M_fn m.val * δ ^ 2 :=
      (hM_data m.val m.property).2 δ hδ_pos hδ_m
    have h_M_le : M_fn m.val ≤ M_max := by
      rw [hM_def]
      exact Finset.le_sup' (fun m : {x // x ∈ Finset.Ico j n} => M_fn m.val) hm_att
    have h_δ_sq_nn : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg δ
    calc |deficit (1 / 2 - δ) m.val - c m.val * δ|
        ≤ M_fn m.val * δ ^ 2 := h_bound
      _ ≤ M_max * δ ^ 2 := mul_le_mul_of_nonneg_right h_M_le h_δ_sq_nn
  -- Unfold the min definitions.
  unfold suffMinDelta suffMin
  rw [dif_pos hjn, dif_pos hjn]
  -- Goal: |inf' (deficit (1/2-δ) m) - inf' (c m) · δ| ≤ M_max · δ².
  -- Move δ inside inf'.
  rw [finset_inf'_mul_pos _ _ hδ_pos]
  -- Goal: |inf' (deficit (1/2-δ) m) - inf' (c m · δ)| ≤ M_max · δ².
  exact finset_inf'_lipschitz _ _ _ (M_max * δ ^ 2) h_per_m

/-- Proposition 4.3 (first-order coefficient): `c n` is the first-order
    coefficient of `Δ_{n, 1/2 - δ}` as `δ → 0⁺`.
    Base case `n = 1` is `deficit_first_order_one`; the inductive step
    combines `constant_term_taylor`, `binom_weight_perturb`, and
    `suffMinDelta_first_order`. -/
theorem deficit_first_order (n : ℕ) (hn : 1 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |deficit (1/2 - δ) n - c n * δ| ≤ M * δ ^ 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ =>
      -- Base case: exact identity, M = 1, δ₀ = 1.
      refine ⟨1, 1, by norm_num, ?_⟩
      intro δ _ _
      rw [deficit_first_order_one]
      have heq : c 1 * δ - c 1 * δ = 0 := by ring
      rw [heq, abs_zero]
      positivity
    | n + 2, _ =>
      -- Apply the three sub-lemmas.
      have hn2 : 2 ≤ n + 2 := by omega
      -- Sub-lemma 1: Taylor bound for the constant term.
      obtain ⟨M₁, δ₁, hδ₁_pos, h₁_bound⟩ := constant_term_taylor (n + 2) (by omega)
      -- For each j ∈ [1, n+2), combine sub-lemmas 2 and 3 into a per-j O(δ²) bound.
      have h_per_j : ∀ j, 1 ≤ j → j < n + 2 →
          ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
            |(Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ|
              ≤ M * δ ^ 2 := by
        intro j hj1 hj_lt
        obtain ⟨M_b, δ_b, hδ_b_pos, h_b⟩ :=
          binom_weight_perturb (n + 2) j hj1 (by omega : j ≤ n + 2 - 1)
        obtain ⟨M_s, δ_s, hδ_s_pos, h_s⟩ :=
          suffMinDelta_first_order (n + 2) j hn2 hj1 hj_lt
            (fun m hm1 hmlt => ih m hmlt hm1)
        -- Bound on |suffMin j (n+2)|: ≤ c j (by inf' ≤ elem).
        have h_suffMin_bd : |suffMin j (n + 2)| ≤ |c j| := by
          have h_ne_att : (Finset.Ico j (n + 2)).attach.Nonempty :=
            ⟨⟨j, Finset.mem_Ico.mpr ⟨le_refl _, hj_lt⟩⟩, Finset.mem_attach _ _⟩
          unfold suffMin
          rw [dif_pos hj_lt]
          -- suffMin ≤ c j
          have h_le : (Finset.Ico j (n + 2)).attach.inf' h_ne_att
              (fun m => c m.val) ≤ c j := by
            exact Finset.inf'_le (fun m : {x // x ∈ Finset.Ico j (n + 2)} => c m.val)
              (Finset.mem_attach _ ⟨j, Finset.mem_Ico.mpr ⟨le_refl _, hj_lt⟩⟩)
          -- suffMin ≥ 0 (c ≥ 0 for all m).
          have h_nn : 0 ≤ (Finset.Ico j (n + 2)).attach.inf' h_ne_att
              (fun m => c m.val) := by
            apply Finset.le_inf'
            intro m _
            have hmr := Finset.mem_Ico.mp m.property
            exact c_pos m.val (by omega : 1 ≤ m.val) |>.le
          rw [abs_of_nonneg h_nn]
          exact h_le.trans (le_abs_self _)
        -- Decompose via A·B - C·D = A·(B - D) + (A - C)·D.
        refine ⟨(Nat.choose (n + 2) j : ℝ) * M_s + M_b * |c j|, min δ_b (min δ_s (1/2)),
          lt_min hδ_b_pos (lt_min hδ_s_pos (by norm_num)), ?_⟩
        intro δ hδ_pos hδ_lt
        have hδ_lt_b : δ < δ_b := lt_of_lt_of_le hδ_lt (min_le_left _ _)
        have hδ_lt_s : δ < δ_s := lt_of_lt_of_le hδ_lt
          (le_trans (min_le_right _ _) (min_le_left _ _))
        have hδ_lt_half : δ < 1/2 := lt_of_lt_of_le hδ_lt
          (le_trans (min_le_right _ _) (min_le_right _ _))
        have hb := h_b δ hδ_pos hδ_lt_b
        have hs := h_s δ hδ_pos hδ_lt_s
        -- Abbreviate:
        set A : ℝ := (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j with hA_def
        set C : ℝ := 1 / (2 : ℝ) ^ (n + 2) with hC_def
        set B : ℝ := suffMinDelta (1/2 - δ) j (n + 2) with hB_def
        set D : ℝ := suffMin j (n + 2) * δ with hD_def
        -- Goal: |C(n+2,j) · A · B - (C(n+2,j) / 2^(n+2)) · suffMin · δ| ≤ M · δ².
        -- Note: (C(n+2,j) / 2^(n+2)) · suffMin · δ = C(n+2,j) · C · D.
        have h_goal_form :
            (Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ =
            (Nat.choose (n + 2) j : ℝ) * (A * B - C * D) := by
          rw [hA_def, hB_def, hC_def, hD_def]; ring
        rw [h_goal_form]
        rw [abs_mul]
        have hC_nj_nn : (0 : ℝ) ≤ (Nat.choose (n + 2) j : ℝ) :=
          by exact_mod_cast Nat.zero_le _
        rw [abs_of_nonneg hC_nj_nn]
        -- Goal: C(n+2,j) · |A·B - C·D| ≤ (C(n+2,j) · M_s + M_b · |c j|) · δ².
        -- Use A·B - C·D = A·(B - D) + (A - C)·D.
        have h_decomp : A * B - C * D = A * (B - D) + (A - C) * D := by ring
        rw [h_decomp]
        -- Bound:
        --   C(n+2,j) · |A·(B - D) + (A - C)·D|
        -- ≤ C(n+2,j) · |A| · |B - D| + C(n+2,j) · |A - C| · |D|.
        have h_A_bound : |A| ≤ 1 := by
          rw [hA_def, abs_mul, abs_pow, abs_pow]
          have h1 : |(1/2 - δ : ℝ)| ≤ 1 := by
            have h_pos : (0 : ℝ) < 1/2 - δ := by linarith
            rw [abs_of_pos h_pos]; linarith
          have h2 : |(1/2 + δ : ℝ)| ≤ 1 := by
            have h_pos : (0 : ℝ) < 1/2 + δ := by linarith
            rw [abs_of_pos h_pos]; linarith
          have h1p : |(1/2 - δ : ℝ)| ^ (n + 2 - j) ≤ 1 :=
            pow_le_one₀ (abs_nonneg _) h1
          have h2p : |(1/2 + δ : ℝ)| ^ j ≤ 1 :=
            pow_le_one₀ (abs_nonneg _) h2
          have h2p_nn : 0 ≤ |(1/2 + δ : ℝ)| ^ j := pow_nonneg (abs_nonneg _) j
          exact mul_le_one₀ h1p h2p_nn h2p
        have h_D_eq : |D| = |suffMin j (n + 2)| * δ := by
          rw [hD_def, abs_mul, abs_of_pos hδ_pos]
        have h_A_sub_C : |(Nat.choose (n + 2) j : ℝ)| * |A - C| ≤ M_b * δ := by
          have h_expand : (Nat.choose (n + 2) j : ℝ) * A - (Nat.choose (n + 2) j : ℝ) * C =
              (Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) := by
            rw [hA_def, hC_def]; ring
          have := hb
          rw [← h_expand, ← mul_sub, abs_mul] at this
          exact this
        have h_triangle : |A * (B - D) + (A - C) * D| ≤ |A| * |B - D| + |A - C| * |D| := by
          calc |A * (B - D) + (A - C) * D|
              ≤ |A * (B - D)| + |(A - C) * D| := abs_add_le _ _
            _ = |A| * |B - D| + |A - C| * |D| := by simp only [abs_mul]
        have h_nn_cnj : (0 : ℝ) ≤ (Nat.choose (n + 2) j : ℝ) := hC_nj_nn
        have h_mul_bound :
            (Nat.choose (n + 2) j : ℝ) * (|A| * |B - D| + |A - C| * |D|) ≤
            (Nat.choose (n + 2) j : ℝ) * (1 * (M_s * δ^2)) +
            M_b * δ * (|suffMin j (n + 2)| * δ) := by
          have h_A_BD : (Nat.choose (n + 2) j : ℝ) * (|A| * |B - D|) ≤
              (Nat.choose (n + 2) j : ℝ) * (1 * (M_s * δ^2)) := by
            apply mul_le_mul_of_nonneg_left _ h_nn_cnj
            apply mul_le_mul h_A_bound hs (abs_nonneg _) (by norm_num)
          have h_AC_D : (Nat.choose (n + 2) j : ℝ) * (|A - C| * |D|) ≤
              M_b * δ * (|suffMin j (n + 2)| * δ) := by
            rw [h_D_eq, ← mul_assoc]
            have h_abs_nj : |(Nat.choose (n + 2) j : ℝ)| = (Nat.choose (n + 2) j : ℝ) :=
              abs_of_nonneg h_nn_cnj
            calc (Nat.choose (n + 2) j : ℝ) * |A - C| * (|suffMin j (n + 2)| * δ)
                = (|(Nat.choose (n + 2) j : ℝ)| * |A - C|) * (|suffMin j (n + 2)| * δ) := by
                  rw [h_abs_nj]
              _ ≤ (M_b * δ) * (|suffMin j (n + 2)| * δ) := by
                  apply mul_le_mul_of_nonneg_right h_A_sub_C
                  exact mul_nonneg (abs_nonneg _) (le_of_lt hδ_pos)
              _ = M_b * δ * (|suffMin j (n + 2)| * δ) := by ring
          have h_combine : (Nat.choose (n + 2) j : ℝ) * (|A| * |B - D| + |A - C| * |D|) =
              (Nat.choose (n + 2) j : ℝ) * (|A| * |B - D|) +
              (Nat.choose (n + 2) j : ℝ) * (|A - C| * |D|) := by ring
          rw [h_combine]
          linarith
        -- Final bound combining.
        have h_final : (Nat.choose (n + 2) j : ℝ) * (1 * (M_s * δ ^ 2)) +
              M_b * δ * (|suffMin j (n + 2)| * δ) ≤
            ((Nat.choose (n + 2) j : ℝ) * M_s + M_b * |c j|) * δ ^ 2 := by
          have h_p1 : (Nat.choose (n + 2) j : ℝ) * (1 * (M_s * δ ^ 2)) =
              (Nat.choose (n + 2) j : ℝ) * M_s * δ ^ 2 := by ring
          have h_p2 : M_b * δ * (|suffMin j (n + 2)| * δ) =
              M_b * |suffMin j (n + 2)| * δ ^ 2 := by ring
          rw [h_p1, h_p2]
          have h_sfM_le_c : M_b * |suffMin j (n + 2)| * δ ^ 2 ≤ M_b * |c j| * δ ^ 2 := by
            have h_δ_sq_nn : (0 : ℝ) ≤ δ ^ 2 := sq_nonneg δ
            -- need M_b ≥ 0: from binom_weight_perturb M_b := C(n+2,j)·(n+2), non-neg.
            have h_Mb_nn : 0 ≤ M_b := by
              -- h_b holds for all δ ∈ (0, δ_b), and |...| ≥ 0, so M_b must be ≥ 0.
              -- Alternative: pick δ small, e.g., δ = δ_b/2.
              by_contra h_neg
              push_neg at h_neg
              have hδ_small : (0 : ℝ) < δ_b / 2 := by linarith
              have hδ_small_lt : δ_b / 2 < δ_b := by linarith
              have := h_b (δ_b / 2) hδ_small hδ_small_lt
              have h_abs_nn : 0 ≤ |(Nat.choose (n + 2) j : ℝ) *
                  (1/2 - δ_b / 2) ^ (n + 2 - j) * (1/2 + δ_b / 2) ^ j -
                  (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2)| := abs_nonneg _
              have : M_b * (δ_b / 2) < 0 := by
                have : 0 < δ_b / 2 := hδ_small
                nlinarith [h_neg]
              linarith
            have h_base : M_b * |suffMin j (n + 2)| ≤ M_b * |c j| :=
              mul_le_mul_of_nonneg_left h_suffMin_bd h_Mb_nn
            exact mul_le_mul_of_nonneg_right h_base h_δ_sq_nn
          linarith
        calc (Nat.choose (n + 2) j : ℝ) * |A * (B - D) + (A - C) * D|
            ≤ (Nat.choose (n + 2) j : ℝ) * (|A| * |B - D| + |A - C| * |D|) :=
              mul_le_mul_of_nonneg_left h_triangle h_nn_cnj
          _ ≤ (Nat.choose (n + 2) j : ℝ) * (1 * (M_s * δ ^ 2)) +
              M_b * δ * (|suffMin j (n + 2)| * δ) := h_mul_bound
          _ ≤ ((Nat.choose (n + 2) j : ℝ) * M_s + M_b * |c j|) * δ ^ 2 := h_final
      -- Extract per-j data.
      choose! M_fn δ_fn hM_data using h_per_j
      -- Set global M and δ₀.
      -- Sum over j ∈ [1, n+2) for M, min for δ.
      set M_sum : ℝ := ∑ j ∈ Finset.Ico 1 (n + 2), M_fn j with hM_sum_def
      have h_Ico_ne : (Finset.Ico 1 (n + 2)).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩⟩
      have h_Ico_attach_ne : (Finset.Ico 1 (n + 2)).attach.Nonempty :=
        ⟨⟨1, Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩⟩, Finset.mem_attach _ _⟩
      set δ_j_min : ℝ := (Finset.Ico 1 (n + 2)).attach.inf' h_Ico_attach_ne
        (fun j => δ_fn j.val) with hδ_j_min_def
      have hδ_j_min_pos : 0 < δ_j_min := by
        rw [hδ_j_min_def]
        obtain ⟨j₀, _, h_eq⟩ :=
          Finset.exists_mem_eq_inf' h_Ico_attach_ne
            (fun j : {x // x ∈ Finset.Ico 1 (n + 2)} => δ_fn j.val)
        rw [h_eq]
        have hj₀ := Finset.mem_Ico.mp j₀.property
        exact (hM_data j₀.val hj₀.1 hj₀.2).1
      refine ⟨M₁ + M_sum, min δ₁ δ_j_min, lt_min hδ₁_pos hδ_j_min_pos, ?_⟩
      intro δ hδ_pos hδ_lt
      have hδ_lt₁ : δ < δ₁ := lt_of_lt_of_le hδ_lt (min_le_left _ _)
      have hδ_lt_j : δ < δ_j_min := lt_of_lt_of_le hδ_lt (min_le_right _ _)
      -- Apply deficit_succ'.
      rw [show deficit (1 / 2 - δ) (n + 2) =
            ((1 - (1/2 - δ)) ^ (n + 2) - (1/2 - δ) ^ (n + 2)) / 2 +
              ∑ j ∈ Finset.Ico 1 (n + 2),
                (Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) *
                  (1 - (1/2 - δ)) ^ j * suffMinDelta (1/2 - δ) j (n + 2) from
          deficit_succ' (1/2 - δ) (n + 1)]
      rw [show (1 - (1/2 - δ) : ℝ) = 1/2 + δ from by ring]
      -- Apply c_succ.
      rw [show c (n + 2) =
            ((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) +
              (1 / (2 : ℝ) ^ (n + 2)) *
              ∑ j ∈ Finset.Ico 1 (n + 2),
                (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2) from c_succ n]
      -- Rewrite: (a + ∑ fⱼ) - ((b + c·∑ gⱼ)·δ) = (a - b·δ) + (∑ fⱼ - c·δ·∑ gⱼ)
      --                                       = (a - b·δ) + ∑ (fⱼ - c·gⱼ·δ).
      have h_expand_rhs : (((n + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) +
              1 / (2 : ℝ) ^ (n + 2) *
                ∑ j ∈ Finset.Ico 1 (n + 2),
                  (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2)) * δ =
            ((n + 2 : ℕ) : ℝ) * δ / (2 : ℝ) ^ (n + 1) +
            ∑ j ∈ Finset.Ico 1 (n + 2),
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) *
                suffMin j (n + 2) * δ := by
        have h_factor : (∑ j ∈ Finset.Ico 1 (n + 2),
            (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ) =
            δ * (1 / (2 : ℝ) ^ (n + 2) *
              ∑ j ∈ Finset.Ico 1 (n + 2),
                (Nat.choose (n + 2) j : ℝ) * suffMin j (n + 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intros j _
          ring
        rw [h_factor]
        ring
      rw [h_expand_rhs]
      -- Now split into the two bounds.
      have h_diff_eq :
          ((1/2 + δ : ℝ) ^ (n + 2) - (1/2 - δ) ^ (n + 2)) / 2 +
              ∑ j ∈ Finset.Ico 1 (n + 2),
                (Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                  suffMinDelta (1/2 - δ) j (n + 2) -
            (((n + 2 : ℕ) : ℝ) * δ / (2 : ℝ) ^ (n + 1) +
              ∑ j ∈ Finset.Ico 1 (n + 2),
                (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ) =
          (((1/2 + δ : ℝ) ^ (n + 2) - (1/2 - δ) ^ (n + 2)) / 2 -
              ((n + 2 : ℕ) : ℝ) * δ / (2 : ℝ) ^ (n + 1)) +
          ∑ j ∈ Finset.Ico 1 (n + 2),
            ((Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
              suffMinDelta (1/2 - δ) j (n + 2) -
            (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ) := by
        rw [Finset.sum_sub_distrib]; ring
      rw [h_diff_eq]
      -- Apply the two bounds.
      have h_tri_sum : ∀ j ∈ Finset.Ico 1 (n + 2),
          |(Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
              suffMinDelta (1/2 - δ) j (n + 2) -
            (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ|
          ≤ M_fn j * δ ^ 2 := by
        intro j hj
        have hjr := Finset.mem_Ico.mp hj
        have hδ_lt_j' : δ < δ_fn j := by
          have h_le : δ_j_min ≤ δ_fn j := by
            rw [hδ_j_min_def]
            exact Finset.inf'_le
              (fun j' : {x // x ∈ Finset.Ico 1 (n + 2)} => δ_fn j'.val)
              (Finset.mem_attach _ ⟨j, hj⟩)
          linarith
        exact (hM_data j hjr.1 hjr.2).2 δ hδ_pos hδ_lt_j'
      have h_sum_abs : |∑ j ∈ Finset.Ico 1 (n + 2),
            ((Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
              suffMinDelta (1/2 - δ) j (n + 2) -
            (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ)|
          ≤ M_sum * δ ^ 2 := by
        calc |∑ j ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ)|
            ≤ ∑ j ∈ Finset.Ico 1 (n + 2),
              |(Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.Ico 1 (n + 2), M_fn j * δ ^ 2 := Finset.sum_le_sum h_tri_sum
          _ = M_sum * δ ^ 2 := by
              rw [hM_sum_def, ← Finset.sum_mul]
      -- Combine.
      calc |(((1/2 + δ : ℝ) ^ (n + 2) - (1/2 - δ) ^ (n + 2)) / 2 -
              ((n + 2 : ℕ) : ℝ) * δ / (2 : ℝ) ^ (n + 1)) +
            ∑ j ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ)|
          ≤ |((1/2 + δ : ℝ) ^ (n + 2) - (1/2 - δ) ^ (n + 2)) / 2 -
              ((n + 2 : ℕ) : ℝ) * δ / (2 : ℝ) ^ (n + 1)|
            + |∑ j ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose (n + 2) j : ℝ) * (1/2 - δ) ^ (n + 2 - j) * (1/2 + δ) ^ j *
                suffMinDelta (1/2 - δ) j (n + 2) -
              (Nat.choose (n + 2) j : ℝ) / (2 : ℝ) ^ (n + 2) * suffMin j (n + 2) * δ)| :=
            abs_add_le _ _
        _ ≤ M₁ * δ ^ 2 + M_sum * δ ^ 2 :=
            add_le_add (h₁_bound δ hδ_pos hδ_lt₁) h_sum_abs
        _ = (M₁ + M_sum) * δ ^ 2 := by ring

/-- Corollary 4.11 (i): the gap `w(p, n-1) - w(p, n)` has first-order
    coefficient `c_n - c_{n-1}` as `p = 1/2 - δ`, `δ → 0⁺`.
    Reduces to `deficit_first_order` applied to `n` and `n-1`. -/
theorem w_gap_first_order (n : ℕ) (hn : 2 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |w (1/2 - δ) (n - 1) - w (1/2 - δ) n - (c n - c (n - 1)) * δ| ≤
        M * δ ^ 2 := by
  obtain ⟨M₁, δ₁, hδ₁_pos, h₁⟩ := deficit_first_order n (by omega : 1 ≤ n)
  obtain ⟨M₂, δ₂, hδ₂_pos, h₂⟩ := deficit_first_order (n - 1) (by omega : 1 ≤ n - 1)
  refine ⟨M₁ + M₂, min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, ?_⟩
  intro δ hδ_pos hδ_lt
  have hδ_lt₁ : δ < δ₁ := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have hδ_lt₂ : δ < δ₂ := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  have b1 := h₁ δ hδ_pos hδ_lt₁
  have b2 := h₂ δ hδ_pos hδ_lt₂
  -- w p n = 1/2 - deficit p n, so w p (n-1) - w p n = deficit p n - deficit p (n-1).
  have hw_rel : w (1 / 2 - δ) (n - 1) - w (1 / 2 - δ) n =
      deficit (1 / 2 - δ) n - deficit (1 / 2 - δ) (n - 1) := by
    unfold deficit
    ring
  rw [hw_rel]
  -- (Δ_n - Δ_{n-1}) - (c_n - c_{n-1}) δ = (Δ_n - c_n δ) - (Δ_{n-1} - c_{n-1} δ).
  have h_eq : deficit (1 / 2 - δ) n - deficit (1 / 2 - δ) (n - 1) -
        (c n - c (n - 1)) * δ =
      (deficit (1 / 2 - δ) n - c n * δ) -
      (deficit (1 / 2 - δ) (n - 1) - c (n - 1) * δ) := by ring
  rw [h_eq]
  calc |deficit (1 / 2 - δ) n - c n * δ -
          (deficit (1 / 2 - δ) (n - 1) - c (n - 1) * δ)|
      ≤ |deficit (1 / 2 - δ) n - c n * δ| +
        |deficit (1 / 2 - δ) (n - 1) - c (n - 1) * δ| :=
        abs_sub _ _
    _ ≤ M₁ * δ ^ 2 + M₂ * δ ^ 2 := add_le_add b1 b2
    _ = (M₁ + M₂) * δ ^ 2 := by ring

/-- Corollary 4.11 (ii): to first order, `n = 5` is a strict local minimum
    of `n ↦ w(1/2 - δ, n)`. Uses `w_gap_first_order` at `n = 5` (where
    `c_5 > c_4`) and at `n = 6` (where `c_5 > c_6` from
    `c_strict_anti_from_five`). -/
theorem w_local_min_at_five :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) 5 < w (1/2 - δ) 4 ∧ w (1/2 - δ) 5 < w (1/2 - δ) 6 := by
  obtain ⟨M₁, δ₁, hδ₁_pos, h₁⟩ := w_gap_first_order 5 (by omega)
  obtain ⟨M₂, δ₂, hδ₂_pos, h₂⟩ := w_gap_first_order 6 (by omega)
  -- (5 - 1 = 4). Gap at n=5: |w_4 - w_5 - (c_5 - c_4) δ| ≤ M₁ δ².
  -- Gap at n=6: |w_5 - w_6 - (c_6 - c_5) δ| ≤ M₂ δ².
  have h_gap5 : c 5 - c 4 > 0 := by linarith [c_four_lt_five]
  have h_gap6 : c 5 - c 6 > 0 := by
    have := c_strict_anti_from_five 5 (by norm_num)
    -- c (5+1) < c 5, i.e., c 6 < c 5.
    linarith
  -- Choose δ₀ small enough: δ₀ ≤ min(δ₁, δ₂, (c_5-c_4)/(2(|M₁|+1)), (c_5-c_6)/(2(|M₂|+1))).
  set ε1 : ℝ := (c 5 - c 4) / (2 * (|M₁| + 1))
  set ε2 : ℝ := (c 5 - c 6) / (2 * (|M₂| + 1))
  have hε1_pos : 0 < ε1 := by
    apply div_pos h_gap5; positivity
  have hε2_pos : 0 < ε2 := by
    apply div_pos h_gap6; positivity
  refine ⟨min (min δ₁ δ₂) (min ε1 ε2),
    lt_min (lt_min hδ₁_pos hδ₂_pos) (lt_min hε1_pos hε2_pos), ?_⟩
  intro δ hδ_pos hδ_lt
  have hδ_lt₁ : δ < δ₁ := lt_of_lt_of_le hδ_lt
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_lt₂ : δ < δ₂ := lt_of_lt_of_le hδ_lt
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_lt_ε1 : δ < ε1 := lt_of_lt_of_le hδ_lt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_lt_ε2 : δ < ε2 := lt_of_lt_of_le hδ_lt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have bd1 := h₁ δ hδ_pos hδ_lt₁
  have bd2 := h₂ δ hδ_pos hδ_lt₂
  -- For each part, unfold |...| into a bound.
  refine ⟨?_, ?_⟩
  · -- w_5 < w_4, i.e., w_4 - w_5 > 0.
    -- bd1 : |w_4 - w_5 - (c_5 - c_4) δ| ≤ M₁ δ²
    -- so w_4 - w_5 ≥ (c_5 - c_4) δ - M₁ δ²
    have bd_lb : w (1/2 - δ) 4 - w (1/2 - δ) 5 ≥ (c 5 - c 4) * δ - M₁ * δ^2 := by
      have := abs_le.mp bd1
      have : -(M₁ * δ^2) ≤ w (1/2 - δ) (5 - 1) - w (1/2 - δ) 5 - (c 5 - c (5 - 1)) * δ :=
        this.1
      have hfive : (5 : ℕ) - 1 = 4 := by norm_num
      rw [hfive] at this
      linarith
    -- M₁ δ² ≤ |M₁| δ² ≤ (|M₁| + 1) δ² < δ · ε1 · (|M₁| + 1) = δ · (c_5 - c_4)/2.
    have hM₁_bound : M₁ * δ^2 < (c 5 - c 4) / 2 * δ := by
      have hM₁_le : M₁ * δ^2 ≤ |M₁| * δ^2 := by
        have := le_abs_self M₁; nlinarith [sq_nonneg δ]
      have : |M₁| * δ^2 < (c 5 - c 4) / 2 * δ := by
        have h_abs_nn : 0 ≤ |M₁| := abs_nonneg M₁
        have h_one_nn : (0 : ℝ) ≤ |M₁| + 1 := by linarith
        have h_pos : (0 : ℝ) < 2 * (|M₁| + 1) := by linarith
        have h1 : |M₁| * δ^2 ≤ (|M₁| + 1) * δ * δ := by nlinarith [sq_nonneg δ, hδ_pos]
        have h2 : (|M₁| + 1) * δ * δ < (|M₁| + 1) * ε1 * δ := by
          apply mul_lt_mul_of_pos_right _ hδ_pos
          apply mul_lt_mul_of_pos_left hδ_lt_ε1
          linarith
        have h3 : (|M₁| + 1) * ε1 * δ = (c 5 - c 4) / 2 * δ := by
          rw [show ε1 = (c 5 - c 4) / (2 * (|M₁| + 1)) from rfl]
          field_simp
        linarith
      linarith
    have : (c 5 - c 4) * δ - M₁ * δ^2 > (c 5 - c 4) * δ - (c 5 - c 4) / 2 * δ := by
      linarith
    have : (c 5 - c 4) * δ - M₁ * δ^2 > 0 := by
      have : (c 5 - c 4) * δ - (c 5 - c 4) / 2 * δ = (c 5 - c 4) / 2 * δ := by ring
      nlinarith [h_gap5, hδ_pos]
    linarith [bd_lb]
  · -- w_5 < w_6, i.e., w_6 - w_5 > 0. From gap at n=6:
    -- bd2 : |w_5 - w_6 - (c_6 - c_5) δ| ≤ M₂ δ²
    -- so (c_6 - c_5) δ - M₂ δ² ≤ w_5 - w_6 ≤ (c_6 - c_5) δ + M₂ δ²
    -- w_6 - w_5 ≥ -(c_6 - c_5) δ - M₂ δ² = (c_5 - c_6) δ - M₂ δ².
    have bd_lb : w (1/2 - δ) 6 - w (1/2 - δ) 5 ≥ (c 5 - c 6) * δ - M₂ * δ^2 := by
      have := abs_le.mp bd2
      have h6 : (6 : ℕ) - 1 = 5 := by norm_num
      rw [h6] at this
      linarith [this.2]
    -- Analogous to above: M₂ δ² < (c_5 - c_6)/2 · δ.
    have hM₂_bound : M₂ * δ^2 < (c 5 - c 6) / 2 * δ := by
      have hM₂_le : M₂ * δ^2 ≤ |M₂| * δ^2 := by
        have := le_abs_self M₂; nlinarith [sq_nonneg δ]
      have : |M₂| * δ^2 < (c 5 - c 6) / 2 * δ := by
        have h_abs_nn : 0 ≤ |M₂| := abs_nonneg M₂
        have h_pos : (0 : ℝ) < 2 * (|M₂| + 1) := by linarith
        have h1 : |M₂| * δ^2 ≤ (|M₂| + 1) * δ * δ := by nlinarith [sq_nonneg δ, hδ_pos]
        have h2 : (|M₂| + 1) * δ * δ < (|M₂| + 1) * ε2 * δ := by
          apply mul_lt_mul_of_pos_right _ hδ_pos
          apply mul_lt_mul_of_pos_left hδ_lt_ε2
          linarith
        have h3 : (|M₂| + 1) * ε2 * δ = (c 5 - c 6) / 2 * δ := by
          rw [show ε2 = (c 5 - c 6) / (2 * (|M₂| + 1)) from rfl]
          field_simp
        linarith
      linarith
    have : (c 5 - c 6) * δ - M₂ * δ^2 > 0 := by
      nlinarith [h_gap6, hδ_pos, hM₂_bound]
    linarith [bd_lb]

/-- Corollary 4.11 (iii): there is no local maximum at first order;
    `c_n` is eventually decreasing, so `w(1/2 - δ, n)` is eventually increasing
    in `n`. Uses `w_gap_first_order` at `n+1` plus `c_strict_anti_from_five`. -/
theorem no_first_order_local_max :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) n < w (1/2 - δ) (n + 1) := by
  refine ⟨5, ?_⟩
  intro n hn
  obtain ⟨M, δ_max, hδ_pos, hbd⟩ := w_gap_first_order (n + 1) (by omega)
  have h_anti : c (n + 1) < c n := c_strict_anti_from_five n hn
  have h_pos_gap : 0 < c n - c (n + 1) := by linarith
  set ε : ℝ := (c n - c (n + 1)) / (2 * (|M| + 1))
  have hε_pos : 0 < ε := by
    apply div_pos h_pos_gap; positivity
  refine ⟨min δ_max ε, lt_min hδ_pos hε_pos, ?_⟩
  intro δ hδ_p hδ_lt
  have hδ_lt_max : δ < δ_max := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have hδ_lt_ε : δ < ε := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  have bd := hbd δ hδ_p hδ_lt_max
  have h_eq : (n + 1 : ℕ) - 1 = n := by omega
  rw [h_eq] at bd
  -- bd : |w n - w (n+1) - (c (n+1) - c n) δ| ≤ M δ²
  -- From upper bound: w n - w (n+1) ≤ (c (n+1) - c n) δ + M δ² = -(c_n - c_{n+1}) δ + M δ².
  have bd_ub : w (1/2 - δ) n - w (1/2 - δ) (n + 1) ≤
      (c (n + 1) - c n) * δ + M * δ^2 := by
    have := abs_le.mp bd; linarith [this.2]
  have hM_bd : M * δ^2 < (c n - c (n + 1)) / 2 * δ := by
    have hM_le : M * δ^2 ≤ |M| * δ^2 := by
      have := le_abs_self M; nlinarith [sq_nonneg δ]
    have : |M| * δ^2 < (c n - c (n + 1)) / 2 * δ := by
      have h_abs_nn : 0 ≤ |M| := abs_nonneg M
      have h_pos : (0 : ℝ) < 2 * (|M| + 1) := by linarith
      have h1 : |M| * δ^2 ≤ (|M| + 1) * δ * δ := by nlinarith [sq_nonneg δ, hδ_p]
      have h2 : (|M| + 1) * δ * δ < (|M| + 1) * ε * δ := by
        apply mul_lt_mul_of_pos_right _ hδ_p
        apply mul_lt_mul_of_pos_left hδ_lt_ε
        linarith
      have h3 : (|M| + 1) * ε * δ = (c n - c (n + 1)) / 2 * δ := by
        rw [show ε = (c n - c (n + 1)) / (2 * (|M| + 1)) from rfl]
        field_simp
      linarith
    linarith
  nlinarith [bd_ub, hM_bd, h_pos_gap, hδ_p]

/-- Numerical buffer at `n = 12`: `c 12 − 27/16 ≥ 1/60`.

    This is the starting value used in the cumulative argument for
    `n ≥ 13` in the joint proof of §4.3.  Computed by chaining
    `c_linear_rec` from `c 6 = 113337/65536` up through
    `c 7, c 8, …, c 12`. -/
theorem c_twelve_buffer : c 12 - 27 / 16 ≥ 1 / 60 := by
  -- Cast lemmas for the binomial coefficients used in A_lin / B_lin.
  have h7c2 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 :=
    by exact_mod_cast (by decide : Nat.choose 7 2 = 21)
  have h7c3 : ((Nat.choose 7 3 : ℕ) : ℝ) = 35 :=
    by exact_mod_cast (by decide : Nat.choose 7 3 = 35)
  have h8c2 : ((Nat.choose 8 2 : ℕ) : ℝ) = 28 :=
    by exact_mod_cast (by decide : Nat.choose 8 2 = 28)
  have h8c3 : ((Nat.choose 8 3 : ℕ) : ℝ) = 56 :=
    by exact_mod_cast (by decide : Nat.choose 8 3 = 56)
  have h9c2 : ((Nat.choose 9 2 : ℕ) : ℝ) = 36 :=
    by exact_mod_cast (by decide : Nat.choose 9 2 = 36)
  have h9c3 : ((Nat.choose 9 3 : ℕ) : ℝ) = 84 :=
    by exact_mod_cast (by decide : Nat.choose 9 3 = 84)
  have hAc2 : ((Nat.choose 10 2 : ℕ) : ℝ) = 45 :=
    by exact_mod_cast (by decide : Nat.choose 10 2 = 45)
  have hAc3 : ((Nat.choose 10 3 : ℕ) : ℝ) = 120 :=
    by exact_mod_cast (by decide : Nat.choose 10 3 = 120)
  have hBc2 : ((Nat.choose 11 2 : ℕ) : ℝ) = 55 :=
    by exact_mod_cast (by decide : Nat.choose 11 2 = 55)
  have hBc3 : ((Nat.choose 11 3 : ℕ) : ℝ) = 165 :=
    by exact_mod_cast (by decide : Nat.choose 11 3 = 165)
  have hCc2 : ((Nat.choose 12 2 : ℕ) : ℝ) = 66 :=
    by exact_mod_cast (by decide : Nat.choose 12 2 = 66)
  have hCc3 : ((Nat.choose 12 3 : ℕ) : ℝ) = 220 :=
    by exact_mod_cast (by decide : Nat.choose 12 3 = 220)
  -- Chain the linear recursion from c_6 up to c_12.
  have h_d7 := c_linear_rec 7 (by omega)
  rw [show (7 - 1 : ℕ) = 6 from rfl, c_six] at h_d7
  unfold A_lin B_lin at h_d7
  rw [c_one, c_two, c_three] at h_d7
  rw [h7c2, h7c3] at h_d7
  have h_d8 := c_linear_rec 8 (by omega)
  rw [show (8 - 1 : ℕ) = 7 from rfl, h_d7] at h_d8
  unfold A_lin B_lin at h_d8
  rw [c_one, c_two, c_three] at h_d8
  rw [h8c2, h8c3] at h_d8
  have h_d9 := c_linear_rec 9 (by omega)
  rw [show (9 - 1 : ℕ) = 8 from rfl, h_d8] at h_d9
  unfold A_lin B_lin at h_d9
  rw [c_one, c_two, c_three] at h_d9
  rw [h9c2, h9c3] at h_d9
  have h_d10 := c_linear_rec 10 (by omega)
  rw [show (10 - 1 : ℕ) = 9 from rfl, h_d9] at h_d10
  unfold A_lin B_lin at h_d10
  rw [c_one, c_two, c_three] at h_d10
  rw [hAc2, hAc3] at h_d10
  have h_d11 := c_linear_rec 11 (by omega)
  rw [show (11 - 1 : ℕ) = 10 from rfl, h_d10] at h_d11
  unfold A_lin B_lin at h_d11
  rw [c_one, c_two, c_three] at h_d11
  rw [hBc2, hBc3] at h_d11
  have h_d12 := c_linear_rec 12 (by omega)
  rw [show (12 - 1 : ℕ) = 11 from rfl, h_d11] at h_d12
  unfold A_lin B_lin at h_d12
  rw [c_one, c_two, c_three] at h_d12
  rw [hCc2, hCc3] at h_d12
  -- h_d12 is now an equation `c 12 = (specific rational)`. Conclude by norm_num.
  rw [h_d12]; norm_num
