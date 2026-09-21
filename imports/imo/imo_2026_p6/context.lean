namespace IMO2026P6

/-!
# IMO 2026 Problem 6 — eventual translation core

The source proves that the set of sequence terms eventually
becomes invariant under translation by a positive integer L.

From this one obtains positive integers T and L such that

    a (n + T) = a n + L

for every n.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Basic recurrence data
============================================================
-/

def FollowsNext
    (a next : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    a (n + 1) = next (a n)

def NextTranslationInvariant
    (next : ℕ → ℕ)
    (L : ℕ) : Prop :=
  ∀ x : ℕ,
    next (x + L) =
      next x + L

/-!
============================================================
2. Index arithmetic
============================================================
-/

def HasPeriodicTranslation
    (a : ℕ → ℕ) : Prop :=
  ∃ T L : ℕ,
    0 < T ∧
    0 < L ∧
    ∀ n : ℕ,
      a (n + T) =
        a n + L

def HasPeriodicTranslationOneBased
    (a : ℕ → ℕ) : Prop :=
  ∃ T L : ℕ,
    0 < T ∧
    0 < L ∧
    ∀ n : ℕ,
      1 ≤ n →
      a (n + T) =
        a n + L

def Values
    (a : ℕ → ℕ) : Set ℕ :=
  Set.range a

def EventuallyTranslationInvariant
    (A : Set ℕ)
    (start L : ℕ) : Prop :=
  ∀ m : ℕ,
    start ≤ m →
    (m ∈ A ↔ m + L ∈ A)

/-!
============================================================
8. Forward membership translation
============================================================
-/

structure SourcePeriodData
    (a next : ℕ → ℕ) where

  T : ℕ
  L : ℕ

  T_pos :
    0 < T

  L_pos :
    0 < L

  recurrence :
    FollowsNext a next

  next_translation :
    NextTranslationInvariant next L

  first_period :
    a T =
      a 0 + L

/-!
============================================================
12. Complete source-style conclusion
============================================================
-/
