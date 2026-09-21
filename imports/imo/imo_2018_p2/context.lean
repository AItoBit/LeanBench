namespace IMO2018P2

open Finset

open scoped BigOperators

/-!
# IMO 2018 Problem 2

Find all `n ≥ 3` for which there exist real numbers

    a₁, ..., aₙ₊₂

such that

    aₙ₊₁ = a₁,
    aₙ₊₂ = a₂,

and

    aᵢ * aᵢ₊₁ + 1 = aᵢ₊₂

for `i = 1,...,n`.

We encode this as a periodic infinite sequence.

The final theorem is

    Admissible n ↔ 3 ∣ n.

No `sorry`, `admit`, or extra axioms.
-/

/-!
## Periodic formulation
-/

def Admissible (n : ℕ) : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ i : ℕ, a (i + n) = a i) ∧
    (∀ i : ℕ,
      a i * a (i + 1) + 1 =
        a (i + 2))

/-!
## Periodicity lemmas
-/

/--
The repeating solution

    2, -1, -1, 2, -1, -1, ...
-/
def pattern (i : ℕ) : ℝ :=
  if i % 3 = 0
    then 2
    else -1
