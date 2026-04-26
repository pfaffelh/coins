/-
  Summary.lean — DEPRECATED.

  Earlier versions of this project used `Summary.lean` as a one-page
  tour of the headline definitions and theorems via `#check` and
  `#print axioms`.  Since then a stronger, fully mechanical check has
  become available: the **Lean comparator**
  (https://github.com/leanprover/comparator).

  Verifying the formalization with the comparator gives the same
  guarantees that running `Summary.lean` did, *and more*:

  * The theorem statements actually checked are listed in
    `CoinsLean/Challenge.lean` together with the seven shared
    definitions (`a`, `w`, `c`, `deficit`, `suffMin`, `A_lin`,
    `B_lin`) imported from `CoinsLean/Defs.lean`.  These two files
    are the entire trust surface; a referee only has to read them.
  * The comparator builds `Challenge.lean` and `Solution.lean`
    inside a `landrun` sandbox, exports both environments via
    `lean4export`, replays the proof terms in the Lean kernel, and
    verifies that every theorem named in `config.json` proves
    *exactly* the statement declared in `Challenge.lean` and uses
    only the three foundational axioms `propext`, `Quot.sound`,
    `Classical.choice`.

  Concretely, a referee runs (from inside `CoinsLean/`)

      rm -rf .lake/build
      lake env comparator config.json

  after installing the three external binaries `landrun`,
  `lean4export`, and `comparator` (build instructions in the paper's
  Appendix~A and in `README.md`).  A successful run guarantees
  points (1)–(3) above without any need to audit the proof modules.

  This file is retained only so that links from older preprints
  continue to resolve; it will be removed in a future cleanup.
-/
