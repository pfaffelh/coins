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

/-! ### Lemma 4.7: lower bound c_m ≥ 27/16 for m ≥ 4

  The full lemma in the manuscript holds for every m ≥ 4. The proof uses the
  linear recursion (Prop 4.9), which itself relies on the collapse lemma (4.6),
  which in turn relies on Lemma 4.7 — the circle is broken in the manuscript by
  proving the polynomial bound  A_m − (27/16)·B_m  ≥ 0 directly for m ∈ {3,…,12}
  and treating m ≥ 13 with a contraction argument.

  Below we prove the two cases that follow trivially from the values computed in
  Example 4.5; the inductive bound for m ∈ {6,…,12} and the asymptotic case
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

/-! Strict monotonicity of `c` on `{1, …, 5}` (Example 4.5). -/

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

/-- Lemma 4.7 for `n ∈ {4, …, 12}`. -/
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
    - `c_ge_27_16_full` (Lemma 4.7) — uses `c_linear_rec` for `m ≥ 13` and
      direct computation for `m ∈ {4, …, 12}` (already done in
      `c_ge_27_16_le_12`).
    - `c_strict_anti_from_five` (Lemma 4.8) — uses `c_linear_rec` and
      `c_ge_27_16_full`.
    - `suffMin_collapse_*` (Lemma 4.6) — uses Lemmas 4.7 and 4.8.
    - `c_linear_rec` (Prop 4.9) — uses Lemma 4.6 (collapse).
    - `c_limit_exists` (Thm 4.10) — uses Prop 4.9.
    - `deficit_first_order` (Prop 4.4) — independent (asymptotic claim).
    - `w_*` (Cor 4.11) — uses Prop 4.4 + properties of `c`. -/

/-- The constant `A_n` from the linear recursion (Prop 4.9, eq:AB). -/
noncomputable def A_lin (n : ℕ) : ℝ :=
  (n : ℝ) / (2 : ℝ) ^ (n - 1) +
    ((n : ℝ) * c 1 + (Nat.choose n 2 : ℝ) * c 2 + (Nat.choose n 3 : ℝ) * c 3) /
      (2 : ℝ) ^ n

/-- The constant `B_n` from the linear recursion (Prop 4.9, eq:AB). -/
noncomputable def B_lin (n : ℕ) : ℝ :=
  (2 + (n : ℝ) + (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ)) / (2 : ℝ) ^ n

/-- Lemma 4.7 (full): `c m ≥ 27/16` for every `m ≥ 4`. -/
theorem c_ge_27_16_full : ∀ m : ℕ, 4 ≤ m → c m ≥ 27/16 := by
  sorry

/-- Lemma 4.8: the sequence `(c n)_{n ≥ 5}` is strictly decreasing. -/
theorem c_strict_anti_from_five : ∀ n : ℕ, 5 ≤ n → c (n + 1) < c n := by
  sorry

/-- Lemma 4.6 (collapse) — low part: for `n ≥ 7` and `j ∈ {1, 2, 3}`,
    the suffix-min of `c` over `[j, n)` equals `c j`. -/
theorem suffMin_collapse_low (n j : ℕ) (hn : 7 ≤ n) (h1 : 1 ≤ j) (h3 : j ≤ 3) :
    suffMin j n = c j := by
  sorry

/-- Lemma 4.6 (collapse) — high part: for `n ≥ 7` and `j ∈ {4, …, n-1}`,
    the suffix-min of `c` over `[j, n)` equals `c (n - 1)`. -/
theorem suffMin_collapse_high (n j : ℕ) (hn : 7 ≤ n) (h4 : 4 ≤ j) (hjn : j < n) :
    suffMin j n = c (n - 1) := by
  sorry

/-- Proposition 4.9: the linear recursion for `n ≥ 7`. -/
theorem c_linear_rec (n : ℕ) (h : 7 ≤ n) :
    c n = A_lin n + (1 - B_lin n) * c (n - 1) := by
  sorry

/-- Theorem 4.10: the limit `L = lim c_n` exists. -/
theorem c_limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L) := by
  sorry

/-- Theorem 4.10 (explicit form): for any `n₀ ≥ 7`, the limit is given by
    `L = c_{n₀-1} · ∏_{m ≥ n₀} (1 - B_m) + ∑_{k ≥ n₀} A_k · ∏_{m > k} (1 - B_m)`.
    (Convergence at geometric rate from `A_n, B_n = O(n³ / 2^n)`.) -/
theorem c_limit_formula (n₀ : ℕ) (hn₀ : 7 ≤ n₀) :
    ∃ L : ℝ, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L) ∧
      L = c (n₀ - 1) * ∏' m : {m : ℕ // n₀ ≤ m}, (1 - B_lin m) +
          ∑' k : {k : ℕ // n₀ ≤ k},
            A_lin k * ∏' m : {m : ℕ // k < m}, (1 - B_lin m) := by
  sorry

/-- Proposition 4.4 (first-order coefficient): `c n` is the first-order
    coefficient of `Δ_{n, 1/2 - δ}` as `δ → 0⁺`. -/
theorem deficit_first_order (n : ℕ) (hn : 1 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |deficit (1/2 - δ) n - c n * δ| ≤ M * δ ^ 2 := by
  sorry

/-- Corollary 4.11 (i): the gap `w(p, n-1) - w(p, n)` has first-order
    coefficient `c_n - c_{n-1}` as `p = 1/2 - δ`, `δ → 0⁺`. -/
theorem w_gap_first_order (n : ℕ) (hn : 2 ≤ n) :
    ∃ M δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      |w (1/2 - δ) (n - 1) - w (1/2 - δ) n - (c n - c (n - 1)) * δ| ≤
        M * δ ^ 2 := by
  sorry

/-- Corollary 4.11 (ii): to first order, `n = 5` is a strict local minimum
    of `n ↦ w(1/2 - δ, n)`. -/
theorem w_local_min_at_five :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) 5 < w (1/2 - δ) 4 ∧ w (1/2 - δ) 5 < w (1/2 - δ) 6 := by
  sorry

/-- Corollary 4.11 (iii): there is no local maximum at first order;
    `c_n` is eventually decreasing, so `w(1/2 - δ, n)` is eventually increasing
    in `n`. -/
theorem no_first_order_local_max :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      w (1/2 - δ) n < w (1/2 - δ) (n + 1) := by
  sorry
