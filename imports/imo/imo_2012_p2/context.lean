namespace IMO2012P2

open Finset

open scoped BigOperators

/-!
## Coefficients
-/

/--
The coefficient appearing in the source's AM-GM inequality:

    k^k / (k-1)^(k-1).
-/
noncomputable def coeff (k : ℕ) : ℝ :=
  ((k : ℝ) ^ k) /
    (((k - 1 : ℕ) : ℝ) ^ (k - 1))
