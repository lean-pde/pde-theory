import Mathlib

/-!
# Hello world

The smallest possible module that confirms `PDETheory` builds against mathlib.
The `example` below type-checks only if the mathlib dependency is wired up correctly.
-/

/-- The canonical greeting. -/
def hello : String := "world"

/-- Sanity check: exercise the mathlib dependency at elaboration time. -/
example : (2 : ℝ) + 2 = 4 := by norm_num
