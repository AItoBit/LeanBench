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

/-!
# IMO 1976, Problem 3

A rectangular box with integer edge lengths `a`, `b`, `c` can be completely filled with unit cubes.
If one places into it, with edges parallel to the edges of the box, as many cubes of volume `2` as
possible (each such cube has edge length `∛2`), then exactly `40 %` of the volume of the box is
filled.  Determine all possible dimensions of the box.

The number of cubes of edge `∛2` that fit is `⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋`, so the hypothesis reads
`2 * ⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋ = (2/5) * a * b * c`.

The answer is `{a, b, c} = {2, 3, 5}` or `{a, b, c} = {2, 5, 6}` (as unordered triples).
-/

namespace Imo1976P3

/-- The real number `∛2`, the edge length of a cube of volume `2`. -/
noncomputable def cbrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)
