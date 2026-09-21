namespace IMO2014P1

open Finset

open scoped BigOperators

def partialSum
    (a : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a i

def F
    (a : ℕ → ℕ)
    (n : ℕ) : ℤ :=
  (partialSum a n : ℤ) -
    (n : ℤ) * (a (n + 1) : ℤ)

def G
    (a : ℕ → ℕ)
    (n : ℕ) : ℤ :=
  (partialSum a n : ℤ) -
    (n : ℤ) * (a n : ℤ)

def GoodIndex
    (a : ℕ → ℕ)
    (n : ℕ) : Prop :=
  0 < n ∧
  (n : ℤ) * (a n : ℤ) <
      (partialSum a n : ℤ) ∧
  (partialSum a n : ℤ) ≤
      (n : ℤ) * (a (n + 1) : ℤ)
