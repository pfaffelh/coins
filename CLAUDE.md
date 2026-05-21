# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A research project on the **all-heads coin game** (start with `n` coins, each
heads with probability `p`; each round set aside ≥1 coin; win iff every coin
set aside shows heads). It contains three parallel deliverables that must stay
mutually consistent:

- `Manuscript/` — LaTeX source of the paper *Optimal strategies in the
  all-heads coin game* (Pfaffelhuber). `manuscript.tex` is the main file;
  the others (`halfp.tex`, `localmaximum.tex`, `strategy_all_asymptotics.tex`,
  …) are standalone working notes. Figures live in `Manuscript/figures/`.
- `CoinsLean/` — Lean 4 / Mathlib formalization verifying *every* numbered
  result of the paper.
- `simulation/` — Python scripts that compute the game's quantities
  numerically and regenerate the manuscript figures.

The mathematical core everywhere is the **Bellman recursion for `w(p, n)`**
(optimal winning probability). Every result is a statement about this
recursion and its perturbation expansion around the fair coin `p = 1/2`.

## Build & test commands

### Lean (run inside `CoinsLean/`)

```bash
lake exe cache get   # one-time: fetch pre-built Mathlib (required; else builds for hours)
lake build           # verify the whole project; must end "Build completed successfully"
lake env lean CoinsLean/Summary.lean   # print the main results' types + axioms
lake env lean CoinsLean/CoinsLean/Perturbation.lean   # check a single module
```

Toolchain is **pinned to Lean v4.29.0 / Mathlib v4.29.0** (`lean-toolchain`,
`lake-manifest.json`). Do not bump these casually.

### Python simulations

A virtualenv already exists at `.venv` (numpy, mpmath, matplotlib). Activate
it before running anything — never install packages system-wide:

```bash
source .venv/bin/activate
python3 simulation/plot_for_paper.py   # regenerates figures into Manuscript/figures/
```

### Manuscript

```bash
cd Manuscript && pdflatex manuscript.tex   # (+ bibtex / second pass as needed)
```

## CoinsLean architecture

`CoinsLean/CoinsLean/` holds the development; `CoinsLean.lean` is the root
module importing everything. Mapping to the paper:

| Module | Paper content |
|---|---|
| `Defs.lean` | The 7 shared definitions: `a`, `w`, `c`, `deficit`, `suffMin`, `A_lin`, `B_lin` |
| `Bellman.lean` / `Strategies.lean` | strategy-ALL `b(p,n)`, strategy-ONE `a(p,n)` |
| `HalfP.lean` | `w(1/2, n) = 1/2` for all `n` (Thm 2.1) |
| `Optimal.lean` | `w(p,n)` via the Bellman equation |
| `Above.lean` / `AboveLimit.lean` | §3: `p > 1/2`, linear recursion, limit `W(p)` |
| `Perturbation.lean` | §4: perturbation theory, `c_n`, limit `L`, Cor. 4.11 (~3000 lines, the bulk) |
| `Summary.lean` | one-page `#check` / `#print axioms` tour |

### The comparator harness — keep these in sync

The project is set up for the **Lean comparator**. Three files form a
contract that must agree:

- `Defs.lean` — the **single** kernel-level definition of each of the 7
  constants. Both the trusted statements and the proofs import it, so there
  is no risk of two divergent elaborations. Change a definition here only
  with great care.
- `Challenge.lean` — the *trusted statement surface*: 16 headline theorems
  stated with `sorry` proofs. This is what a verifier reads against the
  manuscript. The `sorry`s here are **intentional** and must remain.
- `Solution.lean` — just `import CoinsLean`; re-exports the real proofs.
- `config.json` — lists the 16 `theorem_names` and the permitted axioms.

If you add, rename, or restate a headline theorem in a proof module, you
must update `Challenge.lean` and `config.json/theorem_names` to match.

### Hard invariants (the formalization's whole point)

- **No `sorry`** anywhere except the deliberate ones in `Challenge.lean`.
- **No user-defined `axiom`**; only `propext`, `Classical.choice`,
  `Quot.sound` may appear in `#print axioms` output.
- **No `native_decide`, `unsafe`, `opaque`.**
- The `main`-branch build must stay green (CI checks it). After any Lean
  change, run `lake build` and confirm zero `sorry` warnings.

`CoinsLean/README.md` is a reviewer's guide (for non-Lean experts);
Appendix A of the paper gives the line-by-line `manuscript ↔ Lean` table.

## Provenance

This is author-directed research. `journal.md` (thematic commentary tied to
each commit) and `CONVERSATION_LOG.md` (prompt-by-prompt collaboration log)
are the provenance trail referenced in the paper's authorship note — update
`journal.md` when making substantive mathematical changes, consistent with
the existing `Journal: <date> session N` commit pattern.

## Licensing split

Code (`CoinsLean/`, `simulation/`, top-level build files) is Apache 2.0
(`LICENSE`). The manuscript and figures (`Manuscript/`) are under the
arXiv.org non-exclusive license (`Manuscript/LICENSE`). See `NOTICE`.
