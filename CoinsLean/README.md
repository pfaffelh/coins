# CoinsLean — Lean 4 formalization

This directory contains the Lean 4 / Mathlib formalization accompanying the
paper *Optimal strategies in the all-heads coin game* by Peter Pfaffelhuber.
Every numbered theorem, proposition, lemma, and corollary of the paper is
stated and proved in Lean; the exact line-by-line correspondence is given
in Appendix A of the paper.

This file is a reviewer's guide. It assumes you know mathematics but not
necessarily Lean 4 or Mathlib, and walks you through downloading, building,
and spot-checking the formalization in about **15 minutes on a normal
laptop** (the bulk is a single one-shot Mathlib cache download).

---

## What you will verify

By running the steps below, you will independently reproduce three facts:

1. **The Lean kernel accepts every proof in the repository.**
   (Command: `lake build`. Output: `Build completed successfully`.)
2. **No proof uses `sorry`** (unfinished placeholder) **and no
   user-defined `axiom` is introduced** — so the formalization does not
   silently assume the theorems.
   (Command: `grep sorry axiom` on the sources; output: no hits beyond
   stylistic mentions in comments.)
3. **The main theorems of the paper have the stated types and depend
   only on Lean's three standard foundational axioms.**
   (Command: `lake env lean CoinsLean/Summary.lean`. Output: the type of
   each main theorem, plus `axioms: [propext, Classical.choice, Quot.sound]`
   for each.)

Together these confirm that the mathematical content of the paper is
machine-checked at the level of Lean 4 + Mathlib.

---

## Step 0 — Prerequisites

You need only one tool: **`elan`**, the Lean 4 version manager. It
installs and manages the correct Lean toolchain automatically.

On Linux / macOS:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

On Windows, see https://leanprover-community.github.io/get_started.html.

Once `elan` is installed, the rest is automatic: when you enter a Lean
project directory, the correct Lean toolchain is downloaded on first use.

> The project pins `leanprover/lean4:v4.29.1` and Mathlib release tag
> `v4.29.1`.  `elan` reads this from `lean-toolchain` and
> `lake-manifest.json`; you do not need to match versions by hand.

## Step 1 — Get the source

Clone the repository and enter the Lean subdirectory:

```bash
git clone https://github.com/pfaffelh/coins.git
cd coins/CoinsLean
```

## Step 2 — Download the pre-built Mathlib cache

**This step is essential.**  Building Mathlib from scratch takes many
hours.  Mathlib publishes a pre-built cache; downloading it takes 1–5
minutes on a good connection.

```bash
lake exe cache get
```

Expected output: a progress bar, then something like
`Unpacked …`, ending without errors.  If `lake` prompts you to install
the toolchain, answer yes — that is `elan` doing its job.

## Step 3 — Build the project

```bash
lake build
```

Expected output (elided): a stream of `[k/N] Built …` lines, then

```
Build completed successfully (8258 jobs).
```

Typical wall-clock time: **30 seconds to 2 minutes** (most jobs are
skipped because they are already cached).  If you see `warning: …
declaration uses 'sorry'`, please flag it — every proof in the paper
should be complete, and the expected output contains **no such
warnings**.

## Step 4 — Confirm there is no sorry or custom axiom

```bash
grep -rn "^axiom\|^\s*axiom\b" CoinsLean/
grep -rn "\bsorry\b\|\bnative_decide\b\|\bunsafe\b\|\bopaque\b" CoinsLean/
```

Expected output: none of the first; only two hits of the second, both
inside **docstring comments** (the string `sorry` appearing in prose,
not in a proof).  No `native_decide`, no `unsafe`, no `opaque`.

## Step 5 — Inspect the main results

Run the one-page summary file:

```bash
lake env lean CoinsLean/Summary.lean
```

Expected output: the **types of all main definitions and theorems** of
the paper, followed by a list of axioms each one depends on:

```
w : ℝ → ℕ → ℝ
deficit : ℝ → ℕ → ℝ
c : ℕ → ℝ
…
c_limit_exists : ∃ L, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L)
c_limit_formula : ∀ (n₀ : ℕ), 7 ≤ n₀ → ∃ L, … L = c (n₀-1) * ∏' … + ∑' … * ∏' …
…
'c_limit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'c_limit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
…
```

The three axioms (`propext`, `Classical.choice`, `Quot.sound`) are the
only ones built into Lean / Mathlib and are used throughout mainstream
mathematics; no additional axioms appear.

Cross-check the printed types against the statements in the paper.
Appendix A provides a direct `Manuscript → Lean theorem` table with
clickable GitHub links to the exact source line of every theorem.

## Step 6 (optional) — Spot-check an individual proof

To jump to a specific theorem, open the relevant file and line in any
text editor:

```bash
sed -n '2065,2130p' CoinsLean/Perturbation.lean   # c_limit_formula
sed -n '1495,1510p' CoinsLean/Perturbation.lean   # c_linear_rec
sed -n '71,120p'    CoinsLean/AboveLimit.lean     # above_linear_rec
```

For interactive browsing, you can use any editor with a Lean extension
(VS Code with `leanprover/vscode-lean4`, or Emacs `lean4-mode`); this is
not required for verification.

---

## Directory layout

```
CoinsLean/
├── README.md                 (this file)
├── lakefile.toml             build configuration
├── lean-toolchain            pinned Lean version
├── lake-manifest.json        pinned Mathlib version
├── CoinsLean.lean            root module (imports everything)
└── CoinsLean/
    ├── Basic.lean            (template stub — ignore)
    ├── Bellman.lean          strategy-ALL value b(p,n)
    ├── HalfP.lean            b(1/2, n) = 1/2 for all n
    ├── Strategies.lean       strategy-ONE value a(p,n)
    ├── Optimal.lean          w(p,n) by the Bellman equation; w(1/2,n) = 1/2
    ├── Above.lean            Theorem 3.1 of the paper (p > 1/2)
    ├── AboveLimit.lean       §3.1 of the paper: linear recursion and limit W(p)
    ├── Perturbation.lean     §4 of the paper: perturbation theory, c_n,
                              limit L, Corollary 4.11
    └── Summary.lean          one-page tour with #check / #print statements
```

## Common questions

**Q: The build takes forever on my machine.**
A: Did you run `lake exe cache get`?  Without the cache, Mathlib builds
from source (many hours).  With the cache, the entire project builds in
under two minutes.

**Q: `lake` is not found.**
A: Install `elan` (Step 0).  `lake` is installed with the Lean
toolchain, which `elan` will fetch automatically once you enter the
project directory.

**Q: I see a lot of `warning:` lines during `lake build`.**
A: Most are stylistic (line length, unused `simp` arguments, etc.).
The build is successful iff the final line is
`Build completed successfully`.  The only warnings that would concern a
reviewer are `declaration uses 'sorry'` — and there should be none.

**Q: I don't want to install Lean just to verify.**
A: The GitHub repository triggers the same build remotely: the file
`.github/workflows/` (if present) shows the status of CI builds.  You
can also click through the hyperlinks in Appendix A of the paper; each
link opens the exact source line on GitHub, and GitHub performs minimal
syntactic highlighting even without Lean installed.

## License

The Lean code in this directory is released under the Apache License,
Version 2.0 (see `../LICENSE`).  Mathlib, a dependency, is also
Apache 2.0.  The research manuscript is separately licensed under
CC BY 4.0 (see `../Manuscript/LICENSE`).
