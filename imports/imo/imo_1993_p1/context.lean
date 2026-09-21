open Polynomial

namespace Imo1993P1

/-- The polynomial `X^(m+2) + 5X^(m+1) + 3` over `ℤ`. -/
noncomputable def f (m : ℕ) : ℤ[X] := X ^ (m + 2) + C 5 * X ^ (m + 1) + C 3
