open Finset

open scoped BigOperators

/--
Formalization of IMO 1968 Problem 6.
Evaluates the infinite sum of floor((n + 2^k) / 2^{k+1}) to n.
Since terms where 2^{k+1} > n + 2^k are zero, the sum is formulated 
as a finite sum up to N where 2^N > n, directly yielding the final atomic conclusion.
-/

theorem candidate (n N : ℕ) (h : n < 2 ^ N) :
    ∑ k ∈ range N, (n + 2 ^ k) / 2 ^ (k + 1) = n :=
