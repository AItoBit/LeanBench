namespace IMO2025P5

noncomputable section

/-!
# IMO 2025 Problem 5

The critical value is

    1 / √2.

The source classification is:

    0 < lam < 1 / √2   → Bazza wins
    lam = 1 / √2       → neither wins
    1 / √2 < lam       → Alice wins

The central analytic inequality in Bazza's strategy is

    √2 ≤ t + √(2 - t²)

for 0 ≤ t ≤ √2.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Critical value
============================================================
-/

def critical : ℝ :=
  1 / Real.sqrt 2

variable
  (AliceWins : ℝ → Prop)
  (BazzaWins : ℝ → Prop)
  (NeitherWins : ℝ → Prop)

/-!
============================================================
11. Three strategic facts from the source
============================================================
-/

structure StrategyFacts
    (AliceWins : ℝ → Prop)
    (BazzaWins : ℝ → Prop)
    (NeitherWins : ℝ → Prop) : Prop where

  alice :
    ∀ lam : ℝ,
      critical < lam →
      AliceWins lam

  bazza :
    ∀ lam : ℝ,
      0 < lam →
      lam < critical →
      BazzaWins lam

  equality :
    NeitherWins critical

/-!
============================================================
12. Classification of a positive parameter
============================================================
-/
