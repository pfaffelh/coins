/-
  Defs.lean — Shared kernel definitions used by both `Challenge.lean`
  (the trusted statement surface for the Lean comparator) and the
  proof modules (`Strategies.lean`, `Optimal.lean`, `Perturbation.lean`).

  Hosting the definitions in a single module guarantees that there is
  exactly one kernel-level constant for each of `a`, `w`, `c`,
  `deficit`, `suffMin`, `A_lin`, `B_lin`, and that the comparator
  cannot see two slightly different elaborations.
-/
import Mathlib

open Finset BigOperators Nat

/-! ## Strategy values -/

/-- Strategy ONE value `a(p, n)` (eq:a-rec): keep one head per round
    (and all heads when every coin shows heads). -/
noncomputable def a (p : ℝ) : ℕ → ℝ
  | 0     => 1
  | n + 1 => p ^ (n + 1) + (1 - p ^ (n + 1) - (1 - p) ^ (n + 1)) * a p n

/-- Optimal winning probability `w(p, n)` defined by the Bellman
    equation (Definition 1.1, eq:bellman). -/
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

/-! ## Perturbation expansion -/

/-- Deficit (Definition 4.1): `Δ_{n,p} := 1/2 − w(p, n)`. -/
noncomputable def deficit (p : ℝ) (n : ℕ) : ℝ := 1/2 - w p n

/-- First-order coefficient `c_n` of `Δ_{n, 1/2 − δ}` as `δ → 0⁺`,
    defined directly via the Bellman-like recursion of Proposition 4.3. -/
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

/-- Suffix-minimum of `c` over indices `[j, n)`; returns `0` when `j ≥ n`. -/
noncomputable def suffMin (j n : ℕ) : ℝ :=
  if h : j < n then
    (Ico j n).attach.inf'
      ⟨⟨j, mem_Ico.mpr ⟨le_refl _, h⟩⟩, mem_attach _ _⟩
      (fun m => c m.val)
  else 0

/-- Constant `A_n` from Proposition 4.8 (eq:AB):
    `A_n = n / 2^{n−1} + (n c_1 + C(n,2) c_2 + C(n,3) c_3) / 2^n`. -/
noncomputable def A_lin (n : ℕ) : ℝ :=
  (n : ℝ) / (2 : ℝ) ^ (n - 1) +
    ((n : ℝ) * c 1 + (Nat.choose n 2 : ℝ) * c 2 + (Nat.choose n 3 : ℝ) * c 3) /
      (2 : ℝ) ^ n

/-- Constant `B_n` from Proposition 4.8 (eq:AB):
    `B_n = (2 + n + C(n,2) + C(n,3)) / 2^n`. -/
noncomputable def B_lin (n : ℕ) : ℝ :=
  (2 + (n : ℝ) + (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ)) / (2 : ℝ) ^ n
