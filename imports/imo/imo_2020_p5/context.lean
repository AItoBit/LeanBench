namespace IMO2020P5

open Finset

open scoped BigOperators

/-!
# IMO 2020 Problem 5 — infinite descent core

The source argument is:

* suppose a deck satisfying the mean property is not constant;
* choose a prime dividing its largest value;
* the mean property propagates this prime divisor through
  every card value;
* divide every card by that prime;
* the resulting deck is still positive, still satisfies the
  property, and is still nonconstant;
* some positive natural-valued measure strictly decreases;
* infinite descent gives a contradiction.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Basic predicates
============================================================
-/

def Positive
    {ι : Type*}
    (a : ι → ℕ) : Prop :=
  ∀ i, 0 < a i

def Constant
    {ι : Type*}
    (a : ι → ℕ) : Prop :=
  ∀ i j, a i = a j

/-!
============================================================
2. Divide a deck by a common divisor
============================================================
-/

def divideDeck
    {ι : Type*}
    (a : ι → ℕ)
    (p : ℕ) :
    ι → ℕ :=
  fun i => a i / p

variable
  {ι : Type*}
  (Good : (ι → ℕ) → Prop)

/-!
============================================================
11. Prime descent step
============================================================
-/
