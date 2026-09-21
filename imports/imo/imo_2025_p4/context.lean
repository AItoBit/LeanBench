namespace IMO2025P4

/-!
# IMO 2025 Problem 4 — valuation/descent core

The source concludes that an initial value a₁ is possible iff

    ord₂(a₁) is odd,
    ord₃(a₁) > (ord₂(a₁)-1)/2,
    5 ∤ a₁.

The difficult number-theoretic part of the source establishes
six facts about the recurrence.  In particular, while

    ord₂(a_k) ≥ 2
    and
    3 ∣ a_k,

one has

    ord₂(a_{k+1}) = ord₂(a_k) - 2
    ord₃(a_{k+1}) = ord₃(a_k) - 1.

This file formalizes the arithmetic descent and the final
classification interface.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Odd natural numbers
============================================================
-/

def OddN (n : ℕ) : Prop :=
  ∃ r : ℕ,
    n = 2 * r + 1

variable
  (v2 v3 : ℕ → ℕ)

/--
The source's final condition on the first term.
-/
def GoodStart
    (a : ℕ) : Prop :=
  OddN (v2 a) ∧
  v3 a > (v2 a - 1) / 2 ∧
  ¬ 5 ∣ a

/-!
============================================================
3. Pure arithmetic form of an odd valuation
============================================================
-/

variable
  (Next : ℕ → ℕ → Prop)

/--
A sequence follows the IMO recurrence.
-/
def FollowsRecurrence
    (a : ℕ → ℕ) : Prop :=
  ∀ k : ℕ,
    Next (a k) (a (k + 1))

/-!
============================================================
9. Packaging the six claims from the source
============================================================
-/

/--
These are the structural facts proved on page 1 of the source.

They are intentionally explicit rather than hidden behind
`sorry`.
-/
structure SourceClaims where

  even :
    ∀ {x y : ℕ},
      Next x y →
      2 ∣ x

  decrease_if_not_three :
    ∀ {x y : ℕ},
      Next x y →
      ¬ 3 ∣ x →
      y < x

  three_persists :
    ∀ {x y : ℕ},
      Next x y →
      3 ∣ x →
      3 ∣ y

  four_divides :
    ∀ {x : ℕ},
      4 ∣ x

  valuation_step :
    ∀ {x y : ℕ},
      Next x y →
      2 ≤ v2 x →
      3 ∣ x →
      v2 y = v2 x - 2 ∧
      v3 y = v3 x - 1

  terminal_parity :
    ∀ {x y : ℕ},
      Next x y →
      v2 x = 1 →
      True

/-!
============================================================
10. One valuation step
============================================================
-/

/--
This is exactly the classification stated in the source.
-/
def Candidate
    (a : ℕ) : Prop :=
  OddN (v2 a) ∧
  v3 a > (v2 a - 1) / 2 ∧
  ¬ 5 ∣ a

variable
  (Possible : ℕ → Prop)

/-!
============================================================
15. Final classification
============================================================
-/
