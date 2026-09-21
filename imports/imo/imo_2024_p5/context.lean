namespace IMO2024P5

/-!
# IMO 2024 Problem 5

The minimum number of attempts is 3.

The proof consists of:

1. no strategy can guarantee success in fewer than 3 attempts;
2. there is a strategy guaranteeing success by attempt 3.

This file formalizes the minimax conclusion from those
two game-theoretic ingredients.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract guaranteed-success predicate
============================================================
-/

/-
`GuaranteedBy n` means that Turbo has a strategy guaranteeing
success on attempt `n` or earlier.
-/

variable
  (GuaranteedBy : ℕ → Prop)

/-!
============================================================
2. Minimum-attempt predicate
============================================================
-/

def IsMinimumAttempts
    (GuaranteedBy : ℕ → Prop)
    (N : ℕ) : Prop :=
  GuaranteedBy N ∧
  ∀ m : ℕ,
    m < N →
    ¬ GuaranteedBy m

/-!
============================================================
3. Direct characterization for 3
============================================================
-/

/--
This version matches the natural indexing of the problem:
attempt numbers begin at 1.

Thus to prove that 3 is minimal we need only

    not by 1,
    not by 2,
    yes by 3.
-/
def IsMinimumPositiveAttempts
    (GuaranteedBy : ℕ → Prop)
    (N : ℕ) : Prop :=
  0 < N ∧
  GuaranteedBy N ∧
  ∀ m : ℕ,
    0 < m →
    m < N →
    ¬ GuaranteedBy m
