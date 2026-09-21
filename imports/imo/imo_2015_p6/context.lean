namespace IMO2015P6

open Finset

open scoped BigOperators

/-!
# IMO 2015 Problem 6 — eventual-pattern core

The source proves that eventually there are:

* a constant "volume" `v`, with `0 ≤ v ≤ 2014`;
* a weight sequence `w`;
* the recurrence

      a_j - (v + 1) = w_{j+1} - w_j;

* bounds

      0 ≤ w_j ≤ (2014 - v) * v.

The recurrence telescopes, giving

    ∑_{j=m+1}^n (a_j - (v+1))
      =
    w_{n+1} - w_{m+1}.

Hence the absolute value is at most

    (2014-v)v ≤ 1007².

This formalizes that entire final stage.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Original hypotheses
-/

/--
The sequence has values between `1` and `2015`
for positive indices.
-/
def BoundedSequence
    (a : ℕ → ℤ) : Prop :=
  ∀ j : ℕ,
    1 ≤ j →
    1 ≤ a j ∧ a j ≤ 2015

/--
The condition

    k + a_k ≠ l + a_l

for `1 ≤ k < l`.
-/
def NoCollision
    (a : ℕ → ℤ) : Prop :=
  ∀ k l : ℕ,
    1 ≤ k →
    k < l →
    (k : ℤ) + a k ≠
      (l : ℤ) + a l

/-!
## Block sums
-/

/--
The sum

    ∑_{j=m+1}^n (a_j - b).

It is represented as a sum of `n-m` terms starting at `m+1`.
-/
def BlockDeviation
    (a : ℕ → ℤ)
    (b : ℤ)
    (m n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n - m),
    (a (m + 1 + i) - b)

/-!
## Telescoping lemma
-/
