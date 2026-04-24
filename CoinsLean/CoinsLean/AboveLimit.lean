/-
  AboveLimit.lean — §3.1 of the manuscript.

  For p > 1/2 we prove:
  - the Bellman recursion for w collapses to a linear recursion
    (Corollary 3.2 of the manuscript):
        w(p, n) = p^n + (1 - p^n - q^n) · w(p, n-1),   q := 1 - p,
    valid for every n ≥ 1;
  - the limit W(p) := lim w(p, n) exists (Weierstrass);
  - W(p) ≥ p > 1/2.
-/
import Mathlib
import CoinsLean.Above

open Finset BigOperators Nat

/-- `p^n + (1-p)^n ≤ 1` for `p ∈ [0,1]` and `n ≥ 1`.  Elementary:
    both powers are in `[0,1]`, and the sum is ≤ `p + (1-p) = 1`
    because powering by `n ≥ 1` is a contraction on `[0,1]`. -/
private lemma pow_plus_one_sub_pow_le_one (p : ℝ) (hp_nn : 0 ≤ p)
    (hp_le : p ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    p ^ n + (1 - p) ^ n ≤ 1 := by
  have hq_nn : 0 ≤ 1 - p := by linarith
  have hq_le : 1 - p ≤ 1 := by linarith
  have hpn : p ^ n ≤ p := by
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]; simp
    · calc p ^ n = p ^ 1 * p ^ (n - 1) := by
            rw [← pow_add]; congr 1; omega
        _ = p * p ^ (n - 1) := by rw [pow_one]
        _ ≤ p * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp_nn
            exact pow_le_one₀ hp_nn hp_le
        _ = p := by ring
  have hqn : (1 - p) ^ n ≤ 1 - p := by
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]; simp
    · calc (1 - p) ^ n = (1 - p) ^ 1 * (1 - p) ^ (n - 1) := by
            rw [← pow_add]; congr 1; omega
        _ = (1 - p) * (1 - p) ^ (n - 1) := by rw [pow_one]
        _ ≤ (1 - p) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hq_nn
            exact pow_le_one₀ hq_nn hq_le
        _ = 1 - p := by ring
  linarith

/-- `a p n ≤ 1` for every `p ∈ [0,1]` and `n`. -/
private lemma a_le_one (p : ℝ) (hp_nn : 0 ≤ p) (hp_le : p ≤ 1) :
    ∀ n : ℕ, a p n ≤ 1 := by
  intro n
  induction n with
  | zero => rw [a_zero]
  | succ k ih =>
    rw [a_succ]
    have hq_nn : 0 ≤ 1 - p := by linarith
    have hpn : 0 ≤ p ^ (k + 1) := pow_nonneg hp_nn _
    have hqn : 0 ≤ (1 - p) ^ (k + 1) := pow_nonneg hq_nn _
    have h_pq : p ^ (k + 1) + (1 - p) ^ (k + 1) ≤ 1 :=
      pow_plus_one_sub_pow_le_one p hp_nn hp_le (k + 1) (by omega)
    have hcoeff_nn : 0 ≤ 1 - p ^ (k + 1) - (1 - p) ^ (k + 1) := by linarith
    have h_prod_le : (1 - p ^ (k + 1) - (1 - p) ^ (k + 1)) * a p k
        ≤ (1 - p ^ (k + 1) - (1 - p) ^ (k + 1)) * 1 :=
      mul_le_mul_of_nonneg_left ih hcoeff_nn
    have : p ^ (k + 1) + (1 - p ^ (k + 1) - (1 - p) ^ (k + 1)) * 1
        = 1 - (1 - p) ^ (k + 1) := by ring
    linarith

/-- **Corollary 3.2** (Linear recursion above 1/2).
    For `p > 1/2` and every `n ≥ 1`:
    `w p n = p^n + (1 - p^n - (1-p)^n) * w p (n-1)`. -/
theorem above_linear_rec (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    w p n = p ^ n + (1 - p ^ n - (1 - p) ^ n) * w p (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show (m + 1 - 1 : ℕ) = m from by omega]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [w_one, w_zero]; simp
  · have h_wa_succ : w p (m + 1) = a p (m + 1) :=
      (above_half p hp hp_lt (m + 1) (by omega)).2.2
    have h_wa : w p m = a p m := by
      rcases Nat.eq_or_lt_of_le hm with h | h
      · rw [← h, w_one]; exact (a_one p).symm
      · exact (above_half p hp hp_lt m h).2.2
    rw [h_wa_succ, a_succ, h_wa]

/-- **Theorem 3.3** (existence of `W(p)`): for `p > 1/2`, the limit
    `W(p) := lim w(p, n)` exists. -/
theorem above_limit_exists (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1) :
    ∃ W : ℝ, Filter.Tendsto (fun n => w p n) Filter.atTop (nhds W) := by
  have hp_nn : 0 ≤ p := by linarith
  have hp_le : p ≤ 1 := le_of_lt hp_lt
  -- Shift by 1: f n := w p (n + 1). f is monotone and bounded.
  let f : ℕ → ℝ := fun n => w p (n + 1)
  have h_mono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro n
    show w p (n + 1) ≤ w p (n + 1 + 1)
    have h := (above_half p hp hp_lt (n + 2) (by omega)).1
    rw [show (n + 2 - 1 : ℕ) = n + 1 from by omega] at h
    exact h.le
  -- f is bounded above by 1: w p n = a p n for n ≥ 1, and a ≤ 1.
  have h_bdd : ∀ n, w p (n + 1) ≤ 1 := by
    intro n
    have h_wa : w p (n + 1) = a p (n + 1) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [w_one, a_one]
      · exact (above_half p hp hp_lt (n + 1) (by omega)).2.2
    rw [h_wa]
    exact a_le_one p hp_nn hp_le (n + 1)
  have h_bdd_set : BddAbove (Set.range f) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact h_bdd n
  have h_f_tendsto : Filter.Tendsto f Filter.atTop (nhds (⨆ n, f n)) :=
    tendsto_atTop_ciSup h_mono h_bdd_set
  refine ⟨⨆ n, f n, ?_⟩
  have h_shift : Filter.Tendsto (fun n : ℕ => n - 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨b + 1, fun a ha => ?_⟩
    omega
  have h_comp : Filter.Tendsto (fun n : ℕ => f (n - 1)) Filter.atTop (nhds (⨆ n, f n)) :=
    h_f_tendsto.comp h_shift
  have h_eq : (fun n => w p n) =ᶠ[Filter.atTop] (fun n : ℕ => f (n - 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    show w p n = w p (n - 1 + 1)
    congr 1; omega
  exact Filter.Tendsto.congr' h_eq.symm h_comp

/-- **Theorem 3.3 (lower bound)**: for `p > 1/2`, the limit `W(p) ≥ p`,
    hence `W(p) > 1/2`. -/
theorem above_limit_ge (p : ℝ) (hp : (1 : ℝ) / 2 < p) (hp_lt : p < 1) :
    ∀ W : ℝ, Filter.Tendsto (fun n => w p n) Filter.atTop (nhds W) →
      p ≤ W := by
  intro W hW
  have h_mono : ∀ n, 1 ≤ n → p ≤ w p n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [w_one]
    | succ m hm ih =>
      have h := (above_half p hp hp_lt (m + 1) (by omega)).1
      rw [show (m + 1 - 1 : ℕ) = m from by omega] at h
      linarith
  exact ge_of_tendsto hW (Filter.eventually_atTop.mpr ⟨1, h_mono⟩)
