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
