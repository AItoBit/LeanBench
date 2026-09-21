namespace IMO2009P3

open Finset

/-- A sequence is arithmetic if all its successive increments are equal. -/
def IsArithmetic (s : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∀ n : ℕ, s (n + 1) = s n + d
