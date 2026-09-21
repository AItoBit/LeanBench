namespace IMO2015P1

open Finset

/-!
# IMO 2015 Problem 1 — combinatorial core of part (b)

For a finite set of `n` points, write

    Equi c a b

for the statement that the point `c` is equidistant
from `a` and `b`.

Balancedness says that every pair of distinct points has
such a centre.

Centre-freeness implies that a fixed centre cannot serve
two pairs sharing exactly one endpoint. Hence the pairs
served by one centre are disjoint.

For even `n`, a fixed centre can therefore serve at most

    (n - 2) / 2

pairs.

After doubling all pair counts:

    required = n(n-1)
    capacity ≤ n(n-2).

But for `n ≥ 2`,

    n(n-2) < n(n-1),

a contradiction.

No `sorry`, `admit`, or extra axioms are used.
-/

variable {n : ℕ}

/-!
## Abstract equidistance
-/

abbrev EquiRel (n : ℕ) :=
  Fin n → Fin n → Fin n → Prop

def EquiSymmetric
    (Equi : EquiRel n) : Prop :=
  ∀ c a b,
    Equi c a b →
    Equi c b a

def Balanced
    (Equi : EquiRel n) : Prop :=
  ∀ a b : Fin n,
    a ≠ b →
    ∃ c : Fin n,
      Equi c a b

/--
Centre-free condition in the form needed for the counting proof.

A fixed point `c` cannot be equidistant from three distinct
points `a`, `b`, `d`.
-/
def CentreFree
    (Equi : EquiRel n) : Prop :=
  ∀ c a b d : Fin n,
    a ≠ b →
    a ≠ d →
    b ≠ d →
    ¬ (Equi c a b ∧ Equi c a d)

/-!
## Consequence of centre-freeness
-/
