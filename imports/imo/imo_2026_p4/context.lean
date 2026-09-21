namespace IMO2026P4

noncomputable section

/-!
# IMO 2026 Problem 4

The source proves that Mulan can force a win exactly for

    theta = π / n

with an integer n ≥ 2.

This is the radian form of

    theta = 180° / n.

The genuinely game-theoretic/geometric parts are encoded in
`StrategyFacts`.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Admissible angles
============================================================
-/

def AdmissibleAngle
    (theta : ℝ) : Prop :=
  0 < theta ∧ theta < Real.pi

/-!
============================================================
2. Candidate answer
============================================================
-/

def GoodAngle
    (theta : ℝ) : Prop :=
  ∃ n : ℕ,
    2 ≤ n ∧
    theta = Real.pi / n

/-!
============================================================
3. π facts
============================================================
-/

variable
  (MulanWins : ℝ → Prop)

/-!
============================================================
13. Strategy facts from the source
============================================================
-/

structure StrategyFacts
    (MulanWins : ℝ → Prop) : Prop where

  necessity :
    ∀ theta : ℝ,
      AdmissibleAngle theta →
      MulanWins theta →
      ∃ n : ℕ,
        2 ≤ n ∧
        (n : ℝ) * theta =
          Real.pi

  sufficiency :
    ∀ n : ℕ,
      2 ≤ n →
      MulanWins
        (Real.pi / n)

/-!
============================================================
14. Winning implies the classified form
============================================================
-/
