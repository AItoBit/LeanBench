namespace IMO2017P1

/-!
# IMO 2017 Problem 1 — recurrence core

For `x > 1`, the recurrence is

    next(x) = √x       if x is a perfect square,
              x + 3    otherwise.

Instead of depending on a particular API for `Nat.sqrt`,
we encode one transition relationally.

This makes the proof stable across Mathlib versions.

 
-/

/-!
## Perfect squares and one-step transitions
-/

def IsSquare (n : ℕ) : Prop :=
  ∃ r : ℕ, n = r * r

def Step (x y : ℕ) : Prop :=
  (∃ r : ℕ,
      x = r * r ∧
      y = r)
  ∨
  (¬ IsSquare x ∧
      y = x + 3)

/--
A sequence follows the recurrence if every consecutive pair
satisfies `Step`.
-/
def FollowsRecurrence
    (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    Step (a n) (a (n + 1))

/-!
## Basic square facts
-/
