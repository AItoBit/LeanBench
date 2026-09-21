/--
If for every `n ≥ 100` there exists a `GoodTriple n`,
then every partition of the cards `n, n+1, ..., 2n`
into two piles contains two cards in one pile whose sum
is a perfect square.
-/
theorem candidate
    (exists_good_triple :
      ∀ n : ℕ,
        100 ≤ n →
        ∃ T : GoodTriple n,
          True) :
    ∀ n : ℕ,
      100 ≤ n →
      ∀ pile : ℕ → Bool,
        ∃ x y : ℕ,
          x ≠ y ∧
          n ≤ x ∧
          x ≤ 2 * n ∧
          n ≤ y ∧
          y ≤ 2 * n ∧
          pile x = pile y ∧
          IsSquare (x + y) :=
