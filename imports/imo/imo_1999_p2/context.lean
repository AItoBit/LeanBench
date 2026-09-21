open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1999 Problem 2

Let `n ≥ 2` be a fixed integer.

* (a) Find the least constant `C` such that for all nonnegative reals `x 1, …, x n`,
  `∑_{i < j} x i * x j * (x i ^ 2 + x j ^ 2) ≤ C * (∑ i, x i) ^ 4`.
* (b) Determine when equality occurs for this value of `C`.

The answer to (a) is `C = 1 / 8`, and equality in (b) holds exactly when two of the `x i`
are equal to each other and all the other `x i` are zero.
-/

namespace Imo1999P2

open Finset

variable {n : ℕ}

/-- The sum of the squares of the coordinates. -/
noncomputable def sumSq (x : Fin n → ℝ) : ℝ := ∑ k, x k ^ 2

/-- The sum of the pairwise products `x i * x j` over `i < j`. -/
noncomputable def pairSum (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j

/-- The left-hand side of the problem: `∑_{i < j} x i * x j * (x i ^ 2 + x j ^ 2)`. -/
noncomputable def lhsSum (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2)
