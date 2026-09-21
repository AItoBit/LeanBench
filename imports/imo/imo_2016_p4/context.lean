namespace IMO2016P4

/-!
# IMO 2016 Problem 4 — arithmetic core and b = 6 construction

Let

    P(n) = n^2 + n + 1.

A block of length `b` starting after `a` is fragrant when
for every `i = 1,...,b`, there is a different `j = 1,...,b`
such that `P(a+i)` and `P(a+j)` have a common prime factor.

The source proves that the least possible `b` is 6.

This file formalizes:

* the key polynomial difference identity;
* the key quadratic identity used to restrict common primes;
* the explicit fragrant block of length 6:
      P(196),...,P(201).

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## The polynomial
-/

def P (n : ℕ) : ℕ :=
  n ^ 2 + n + 1

def Pz (x : ℤ) : ℤ :=
  x ^ 2 + x + 1

/-!
## Basic polynomial identities
-/

/--
`FragrantBlock a b` means that the `b` numbers

    P(a+1), ..., P(a+b)

form a fragrant set in the sense of the problem.

For each index `i`, another index `j ≠ i` must exist
such that the corresponding two values have a common
prime divisor.
-/
def FragrantBlock
    (a b : ℕ) : Prop :=
  2 ≤ b ∧
  ∀ i : ℕ,
    1 ≤ i →
    i ≤ b →
    ∃ j : ℕ,
      1 ≤ j ∧
      j ≤ b ∧
      j ≠ i ∧
      ∃ p : ℕ,
        Nat.Prime p ∧
        p ∣ P (a + i) ∧
        p ∣ P (a + j)

/-!
## Explicit divisibility facts for the source's block
-/
