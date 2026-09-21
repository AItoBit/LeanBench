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

lemma three_bool_pigeonhole
    (x y z : Bool) :
    x = y ∨ x = z ∨ y = z := by
  cases x <;>
    cases y <;>
      cases z <;>
        simp

/-!
============================================================
3. Abstract three-card configuration
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

/--
If three card values form a `GoodTriple`, then in any
assignment to two piles, two distinct card values in the
same pile have square sum.
-/
theorem pair_in_same_pile
    {n : ℕ}
    (T : GoodTriple n)
    (pile : ℕ → Bool) :
    ∃ x y : ℕ,
      x ≠ y ∧
      n ≤ x ∧
      x ≤ 2 * n ∧
      n ≤ y ∧
      y ≤ 2 * n ∧
      pile x = pile y ∧
      IsSquare (x + y) := by

  have hpigeon :
      pile T.a = pile T.b ∨
      pile T.a = pile T.c ∨
      pile T.b = pile T.c :=
    three_bool_pigeonhole
      (pile T.a)
      (pile T.b)
      (pile T.c)

  rcases hpigeon with hab | hac | hbc

  · refine
      ⟨T.a,
       T.b,
       T.hab_ne,
       T.ha_lower,
       T.ha_upper,
       T.hb_lower,
       T.hb_upper,
       hab,
       T.hab_square⟩

  · refine
      ⟨T.a,
       T.c,
       T.hac_ne,
       T.ha_lower,
       T.ha_upper,
       T.hc_lower,
       T.hc_upper,
       hac,
       T.hac_square⟩

  · refine
      ⟨T.b,
       T.c,
       T.hbc_ne,
       T.hb_lower,
       T.hb_upper,
       T.hc_lower,
       T.hc_upper,
       hbc,
       T.hbc_square⟩

/-!
============================================================
5. Final IMO wrapper
============================================================
-/
