/-
  Solution.lean — solution module for the Lean comparator.

  Re-exports the entire `CoinsLean/` development.  The comparator
  configuration (`config.json`) loads this module and verifies that the
  theorems listed in `Challenge.lean` are actually proved here, using
  only the permitted axioms.
-/
import CoinsLean
