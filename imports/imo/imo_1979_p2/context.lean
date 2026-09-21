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

namespace Imo1979P2

/-!
# IMO 1979, Problem 2

We consider a prism whose upper and lower bases are the pentagons `A₁A₂A₃A₄A₅` and
`B₁B₂B₃B₄B₅`.  Each of the ten sides of the two pentagons and each of the twenty-five
segments `AᵢBⱼ` is coloured red or blue.  Assume that in every triangle all of whose
sides are coloured, there is a red side and a blue side.  Then all ten sides of the two
pentagons have the same colour.

Formalisation.  Colours are modelled by `Bool`.

* `a i` is the colour of the pentagon side `Aᵢ Aᵢ₊₁`,
* `b j` is the colour of the pentagon side `Bⱼ Bⱼ₊₁`,
* `c i j` is the colour of the segment `Aᵢ Bⱼ`,

with indices in `Fin 5`, so that `i + 1` is the cyclic successor.  The triangles all of
whose sides are coloured are exactly the triangles `Aᵢ Aᵢ₊₁ Bⱼ` (with sides `a i`,
`c i j`, `c (i+1) j`) and `Aᵢ Bⱼ Bⱼ₊₁` (with sides `b j`, `c i j`, `c i (j+1)`); the
hypothesis says that these are not monochromatic.
-/

variable {a b : Fin 5 → Bool} {c : Fin 5 → Fin 5 → Bool}
