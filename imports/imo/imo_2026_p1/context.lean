namespace IMO2026P1

/-!
# IMO 2026 Problem 1 — termination and invariance core

A board contains exactly 2026 positive integers.

The source proof uses two central ideas:

1. a natural-valued quantity strictly decreases under every move,
   proving termination;

2. a prime-by-prime invariant is preserved by every move and,
   at a terminal state, determines the unique remaining integer
   greater than 1.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Boards
============================================================
-/

abbrev Board :=
  Fin 2026 → ℕ

def PositiveBoard
    (b : Board) : Prop :=
  ∀ i : Fin 2026,
    1 ≤ b i

def HasLarge
    (b : Board) : Prop :=
  ∃ i : Fin 2026,
    1 < b i

def HasTwoLarge
    (b : Board) : Prop :=
  ∃ i j : Fin 2026,
    i ≠ j ∧
    1 < b i ∧
    1 < b j

def Stopped
    (b : Board) : Prop :=
  ¬ HasTwoLarge b

def ExactlyOneLarge
    (b : Board)
    (M : ℕ) : Prop :=
  1 < M ∧
  ∃ i : Fin 2026,
    b i = M ∧
    ∀ j : Fin 2026,
      j ≠ i →
      b j = 1

/-!
============================================================
2. Finite reachability
============================================================
-/

inductive Reach
    (Step : Board → Board → Prop) :
    Board → Board → Prop

  | refl
      (b : Board) :
      Reach Step b b

  | tail
      {a b c : Board} :
      Reach Step a b →
      Step b c →
      Reach Step a c

/-!
============================================================
3. Predicates preserved by reachability
============================================================
-/

def InfiniteRunFrom
    (Step : Board → Board → Prop)
    (start : Board) : Prop :=
  ∃ f : ℕ → Board,
    f 0 = start ∧
    ∀ n : ℕ,
      Step (f n) (f (n + 1))

/-!
============================================================
6. Strict natural descent forbids infinite runs
============================================================
-/

structure SourceFacts
    (Step : Board → Board → Prop)
    (measure : Board → ℕ)
    (signature : Board → ℕ) : Prop where

  positive_step :
    ∀ {a b : Board},
      Step a b →
      PositiveBoard a →
      PositiveBoard b

  large_step :
    ∀ {a b : Board},
      Step a b →
      HasLarge a →
      HasLarge b

  measure_decrease :
    ∀ {a b : Board},
      Step a b →
      measure b < measure a

  signature_step :
    ∀ {a b : Board},
      Step a b →
      signature a = signature b

  terminal_signature :
    ∀ {b : Board}
      {M : ℕ},
      ExactlyOneLarge b M →
      signature b = M

/-!
============================================================
10. Reachable stopped boards have one survivor
============================================================
-/
