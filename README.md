# coins

Mathematical analysis, numerical experiments, and a complete Lean 4 /
Mathlib formalization of the all-heads coin game studied in the paper

> **Optimal strategies in the all-heads coin game**
> Peter Pfaffelhuber

## Contents

| Directory / file | Description |
|---|---|
| [`Manuscript/manuscript.tex`](Manuscript/manuscript.tex) | LaTeX source of the paper (14 pages, including Appendix A). |
| [`Manuscript/manuscript.pdf`](Manuscript/manuscript.pdf) | Compiled PDF. |
| [`Manuscript/figures/`](Manuscript/figures/) | Figures for §5 (Numerical experiments). |
| [`CoinsLean/`](CoinsLean/) | Lean 4 project with the full formalization. |
| [`CoinsLean/CoinsLean/Summary.lean`](CoinsLean/CoinsLean/Summary.lean) | One-page `#check` / `#print` tour of the main results. |
| [`simulation/`](simulation/) | Python scripts computing `w_{n,p}` via the exact Bellman recursion. |
| [`journal.md`](journal.md) | Thematic development commentary, tied to each commit. |
| [`claude.md`](claude.md) | Prompt-by-prompt log of the author–Claude collaboration. |

## The Lean formalization

Every numbered result of the paper — including Theorem 4.10 and
Corollary 4.11 — has been formally verified in Lean 4 with Mathlib.
The formalization uses only the three standard Lean foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no
custom axioms, no `native_decide`, no `unsafe`, no `opaque`.

To build:

```
cd CoinsLean
lake build
```

To view the one-page summary of types and definitions:

```
cd CoinsLean
lake env lean CoinsLean/Summary.lean
```

A line-by-line correspondence between the manuscript and the Lean
theorems appears in Appendix A of the paper.

## Authorship

See the *note on authorship* in §1 of the paper, the *development
history* paragraph in Appendix A, and [`journal.md`](journal.md) for
the full provenance trail. In brief: the research question, the
mathematical ideas, the first-order perturbation strategy, and the
decision to formally verify are the author's. The drafting of prose,
proof tactics, Mathlib lemma selection, and debugging were done by
Anthropic's Claude (Opus 4.6 and 4.7) under the author's direction
and review. The author reviewed every edit and takes responsibility
for any remaining errors.

## License

This repository uses two licenses for different parts of the tree:

- **Source code** (`CoinsLean/`, `simulation/`, top-level build
  files) is released under the
  [Apache License, Version 2.0](LICENSE). The Mathlib dependency
  is also Apache 2.0.
- **Research manuscript and figures** (`Manuscript/`) are released
  under the
  [Creative Commons Attribution 4.0 International License](Manuscript/LICENSE)
  (CC BY 4.0).

See [`NOTICE`](NOTICE) for the full split and attribution details.
