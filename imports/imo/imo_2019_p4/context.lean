namespace IMO2019P4

open Finset

open scoped BigOperators

/-!
# IMO 2019 Problem 4 — bounded classification

We define

    rhs n = ∏ i ∈ range n, (2^n - 2^i).

The original equation is

    k! = rhs n.

The official argument first proves that every solution has
`n ≤ 5`, using 2-adic valuation and growth estimates.

This file formalizes the classification once that bound is known.

No `sorry`, `admit`, or additional axioms.
-/

/-!
============================================================
1. Right-hand side
============================================================
-/

def rhs (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n,
    (2 ^ n - 2 ^ i)

def IsSolution (k n : ℕ) : Prop :=
  0 < k ∧
  0 < n ∧
  k.factorial = rhs n

/-!
============================================================
2. Small RHS values
============================================================
-/
