namespace IMO2021P1

/-!
# IMO 2021 Problem 1 — combinatorial core

The source constructs three distinct card values `a b c`
between `n` and `2n` such that every pair has square sum.

Then, because there are only two piles, two of the three
cards lie in the same pile.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Perfect squares
============================================================
-/

def IsSquare (m : ℕ) : Prop :=
  ∃ r : ℕ, m = r ^ 2

/-!
============================================================
2. Three objects in two piles
============================================================
-/

structure GoodTriple (n : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ

  ha_lower : n ≤ a
  ha_upper : a ≤ 2 * n

  hb_lower : n ≤ b
  hb_upper : b ≤ 2 * n

  hc_lower : n ≤ c
  hc_upper : c ≤ 2 * n

  hab_ne : a ≠ b
  hac_ne : a ≠ c
  hbc_ne : b ≠ c

  hab_square : IsSquare (a + b)
  hac_square : IsSquare (a + c)
  hbc_square : IsSquare (b + c)

/-!
============================================================
4. Pigeonhole step
============================================================
-/
