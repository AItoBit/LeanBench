/-- 
IMO 1993 Problem 6, Part (A):
Because a full round is a permutation on a finite state space,
it must have a finite mathematical order. Thus, applying it a certain number 
of times (`k`) acts as the identity mapping, returning the system to its 
exact initial state ("all lamps are on").
-/
theorem candidate :
    ∃ k : ℕ, k > 0 ∧ (roundEquiv hn) ^ k = 1 :=
