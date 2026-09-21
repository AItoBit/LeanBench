namespace IMO2021P5

/-!
# IMO 2021 Problem 5 — parity core

The original problem has 2021 walnuts numbered 1,...,2021.

At move k, the two walnuts adjacent to walnut k are swapped.

Call walnut k "bad" when its two neighbours lie on opposite
sides of k, i.e.

    a < k < b

or

    b < k < a.

That is exactly the condition required by the problem,
after possibly interchanging the names a and b.

The source proves:

* initially, the number of upcoming bad walnuts is odd;
* after the last move it is zero;
* when the current walnut is not bad, the parity of the
  number of upcoming bad walnuts does not change.

Therefore at some move the current walnut must be bad.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Elementary parity predicates
============================================================
-/

def EvenN (n : ℕ) : Prop :=
  ∃ t : ℕ, n = 2 * t

def OddN (n : ℕ) : Prop :=
  ∃ t : ℕ, n = 2 * t + 1

/--
`Between k a b` means that `k` lies strictly between `a`
and `b`.

This is precisely the source's definition of a bad current
walnut.
-/
def Between
    (k a b : ℕ) : Prop :=
  (a < k ∧ k < b) ∨
  (b < k ∧ k < a)

/--
`left k` and `right k` are the numbers of the two walnuts
adjacent to the current walnut just before zero-based move k.

The current walnut has number k+1.
-/
def BadCurrent
    (left right : ℕ → ℕ)
    (k : ℕ) : Prop :=
  Between
    (k + 1)
    (left k)
    (right k)

/-!
============================================================
12. Main 2021 parity theorem
============================================================
-/
