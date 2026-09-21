/--
Formalization of IMO 1969 Problem 1.
Prove that there are infinitely many natural numbers a with the following property:
the number z = n^4 + a is not prime for any natural number n.

We model "infinitely many" by showing that for any arbitrary bound `m`, 
there exists an `a ≥ m` satisfying the property.
-/
theorem candidate (m : ℕ) : ∃ a ≥ m, ∀ n : ℕ, ¬ Nat.Prime (n^4 + a) :=
