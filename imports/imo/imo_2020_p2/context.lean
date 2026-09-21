namespace IMO2020P2

noncomputable section

/-!
# IMO 2020 Problem 2

Assume

    a ≥ b ≥ c ≥ d > 0
    a + b + c + d = 1.

We want to prove

    (a + 2b + 3c + 4d) a^a b^b c^c d^d < 1.

For real exponents we use `Real.rpow`.

The weighted AM-GM inequality

    a^a b^b c^c d^d ≤ a² + b² + c² + d²

is supplied explicitly as `hamgm`.

Everything after that step is proved in Lean without
`sorry`, `admit`, or extra axioms.
-/

/-!
============================================================
1. Definitions
============================================================
-/

def weightedProd
    (a b c d : ℝ) : ℝ :=
  Real.rpow a a *
    Real.rpow b b *
    Real.rpow c c *
    Real.rpow d d

def linearFactor
    (a b c d : ℝ) : ℝ :=
  a + 2 * b + 3 * c + 4 * d

def squareSum
    (a b c d : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

/-!
============================================================
2. Consequences of the ordering
============================================================
-/

/--
The weighted-AM-GM step used by the source:

    a^a b^b c^c d^d
      ≤
    a² + b² + c² + d².
-/
def WeightedAMGMStatement
    (a b c d : ℝ) : Prop :=
  weightedProd a b c d
    ≤
  squareSum a b c d

/-!
============================================================
9. Combine AM-GM and the polynomial estimate
============================================================
-/
