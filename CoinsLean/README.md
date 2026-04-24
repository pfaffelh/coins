# CoinsLean — Lean 4 formalization

This directory contains the Lean 4 / Mathlib formalization accompanying the
paper *Optimal strategies in the all-heads coin game* by Peter Pfaffelhuber.
Every numbered theorem, proposition, lemma, and corollary of the paper is
stated and proved in Lean; the exact line-by-line correspondence is given
in Appendix A of the paper.

This file is a reviewer's guide. It assumes you know mathematics but not
necessarily Lean 4 or Mathlib, and walks you through downloading and
verifying the formalization interactively in **Visual Studio Code**.
Allow about **15 minutes** on a normal laptop with internet (most of that
is a one-shot Mathlib cache download).

---

## What you will verify

By following the steps below you will independently reproduce three facts:

1. **The Lean kernel accepts every proof** in the repository.
2. **No proof uses `sorry`** (unfinished placeholder) **and no
   user-defined `axiom` is introduced** — so the formalization does not
   silently assume the theorems.
3. **The main theorems have the stated types and depend only on Lean's
   three standard foundational axioms** (`propext`, `Classical.choice`,
   `Quot.sound`, all used throughout mainstream mathematics).

Together these confirm that the mathematical content of the paper is
machine-checked at the level of Lean 4 + Mathlib.

---

## Recommended path — Visual Studio Code

### Step 0 — Install prerequisites

Two pieces of software:

- **Visual Studio Code**
  (https://code.visualstudio.com/, free).

- **`elan`**, the Lean version manager.  On Linux / macOS:

  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

  On Windows see https://leanprover-community.github.io/get_started.html.

  `elan` will automatically download the correct Lean toolchain when you
  open the project.

### Step 1 — Install the Lean 4 extension in VS Code

Open VS Code → left sidebar → *Extensions* → search for
**`lean4`** (publisher *leanprover*) → *Install*.

This single extension gives you syntax highlighting, an interactive
InfoView pane, hover documentation, and go-to-definition.

### Step 2 — Open the project folder

```bash
git clone https://github.com/pfaffelh/coins.git
```

In VS Code: *File → Open Folder...* → select
`coins/CoinsLean`.

The first time you open a Lean file in the project, the extension will
detect the pinned toolchain (`lean-toolchain` file) and, if needed,
prompt `elan` to download it.  Accept the prompt; this takes 30–60
seconds.

### Step 3 — Download the pre-built Mathlib cache

**This step is essential.**  Without it, Mathlib builds from scratch
(many hours).  With it, compilation is nearly instant.

From VS Code's terminal (*Terminal → New Terminal*, which opens inside
`CoinsLean/`), run

```bash
lake exe cache get
```

Expected output: a progress bar followed by `Unpacked …`.  Download
size is a few GB; time is 1–5 minutes on a good connection.

### Step 4 — Open `Summary.lean` and watch Lean check it

In the VS Code file tree, open `CoinsLean/Summary.lean`.

A second pane titled *Lean InfoView* opens on the right (if it does not,
use the command palette: *View → Command Palette* →
`Lean 4: Infoview: Toggle`).

As Lean processes the file (a loading spinner appears briefly in the
bottom status bar — this may take 30–90 seconds the first time), the
InfoView pane progressively fills with the outputs of the `#check` and
`#print axioms` statements in the file.  You should see:

```
w : ℝ → ℕ → ℝ
deficit : ℝ → ℕ → ℝ
c : ℕ → ℝ
c_limit_exists : ∃ L, Filter.Tendsto (fun n => c n) Filter.atTop (nhds L)
c_limit_formula : ∀ (n₀ : ℕ), 7 ≤ n₀ → ∃ L, … L = c (n₀-1) * ∏' … + ∑' … * ∏' …
…
'c_limit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'c_limit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
…
```

Compare the printed types to the statements in the paper; Appendix A
provides a direct `Manuscript → Lean theorem` table.

**What to look for:**

- **No red underlines** anywhere in the file (red would indicate an
  error or incomplete proof).
- **No `sorry` warnings** in the *Problems* tab at the bottom.
- The **axiom list** shows only `[propext, Classical.choice, Quot.sound]`
  — the three foundational Lean axioms.  Any other axiom name would
  indicate a user-added assumption; there should be none.

### Step 5 — Browse a specific proof (optional but recommended)

Click on a theorem name in `Summary.lean` — for instance `c_limit_formula`
— and press `F12` (or right-click → *Go to Definition*).  VS Code jumps
to the exact line of the theorem's proof in `Perturbation.lean`.

Click anywhere inside the proof; the InfoView pane on the right shows
the **current proof state** at that point: the hypotheses known and the
goal remaining.  Moving the cursor through the proof shows Lean's
step-by-step reasoning.

Files worth opening:

- `CoinsLean/Perturbation.lean` — §4 of the paper (perturbation theory,
  `c_n`, limit `L`, Corollary 4.11); roughly 3000 lines.
- `CoinsLean/AboveLimit.lean` — §3.1 of the paper (linear recursion and
  limit `W(p)` for `p > 1/2`).
- `CoinsLean/Above.lean` — Theorem 3.1.
- `CoinsLean/Optimal.lean` — Theorem 2.1.

### Step 6 — Build the whole project (optional)

If you want a single summary confirming that *everything* compiles,
open a terminal (inside `CoinsLean/`) and run

```bash
lake build
```

Expected output: a stream of `[k/N] Built …` lines, ending with

```
Build completed successfully (8258 jobs).
```

Typical wall-clock time: 30 seconds to 2 minutes (cached).  If the
output contains any line of the form `warning: … declaration uses
'sorry'`, please flag it — the expected output contains **none**.

---

## Command-line alternative (no VS Code)

If you prefer a terminal-only workflow or are running in a CI
environment:

```bash
git clone https://github.com/pfaffelh/coins.git
cd coins/CoinsLean
lake exe cache get        # fetch pre-built Mathlib (1–5 min)
lake build                # verify everything (30 s – 2 min)
lake env lean CoinsLean/Summary.lean    # print types + axioms
```

A successful run ends with `Build completed successfully`.  To grep for
suspicious constructs:

```bash
grep -rn "^axiom\|^\s*axiom\b" CoinsLean/
grep -rn "\bsorry\b\|\bnative_decide\b\|\bunsafe\b\|\bopaque\b" CoinsLean/
```

Expected output: the first command yields nothing; the second yields
only two hits, both inside **docstring comments** (the literal string
`sorry` appearing in prose, not in a proof).  No `native_decide`, no
`unsafe`, no `opaque` in the code.

---

## Directory layout

```
CoinsLean/
├── README.md                 (this file)
├── lakefile.toml             build configuration
├── lean-toolchain            pinned Lean version (v4.29.1)
├── lake-manifest.json        pinned Mathlib version (v4.29.1)
├── CoinsLean.lean            root module (imports everything)
└── CoinsLean/
    ├── Basic.lean            template stub — ignore
    ├── Bellman.lean          strategy-ALL value b(p,n)
    ├── HalfP.lean            b(1/2, n) = 1/2 for all n
    ├── Strategies.lean       strategy-ONE value a(p,n)
    ├── Optimal.lean          w(p,n) by the Bellman equation; Theorem 2.1
    ├── Above.lean            Theorem 3.1 of the paper (p > 1/2)
    ├── AboveLimit.lean       §3.1: linear recursion and limit W(p)
    ├── Perturbation.lean     §4: perturbation theory, c_n, limit L,
                              Corollary 4.11
    └── Summary.lean          one-page tour with #check / #print statements
```

## Troubleshooting

**The build takes forever.**  Did you run `lake exe cache get` first?
Without the cache, Mathlib builds from source (many hours).  With the
cache, the entire project builds in under two minutes.

**The VS Code InfoView pane does not appear.**  Command palette
(*Ctrl/Cmd + Shift + P*) → `Lean 4: Infoview: Toggle`.

**`lake` is not found (from the terminal).**  Install `elan` (Step 0).
It places `lake` and `lean` in your `PATH` once you open the project.
You may need to restart your shell after installing `elan`.

**Red underlines or errors in files other than those listed above.**
Please report this — the main-branch build should be fully green
(confirmed by GitHub Actions on every push to `main`).

**I don't want to install anything.**  Every theorem has a direct
GitHub hyperlink in Appendix A of the paper.  Clicking opens the exact
source line in your browser; GitHub's syntax highlighter lets you read
the Lean code without running it.

## License

The Lean code in this directory is released under the Apache License,
Version 2.0 (see `../LICENSE`).  Mathlib, a dependency, is also
Apache 2.0.  The research manuscript is separately licensed under
CC BY 4.0 (see `../Manuscript/LICENSE`).
