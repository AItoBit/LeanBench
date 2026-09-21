/--
Same theorem with

    2*n*(n-1)+1

written directly in the conclusion.
-/
theorem candidate
    (n : ℕ)

    (lower :
      ∀ S : Square n,
        gridEdges n + 1 ≤
          uphillCount S)

    (construction :
      ∃ S : Square n,
        uphillCount S =
          2 * n * (n - 1) + 1) :

    IsMinimum
      Square
      uphillCount
      n
      (2 * n * (n - 1) + 1) :=
