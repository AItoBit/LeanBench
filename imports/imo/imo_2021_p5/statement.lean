/--
At some move K between 1 and 2021, the two walnuts being
swapped can be named a,b so that

    a < K < b.

The pair `left k`, `right k` is exactly the pair adjacent
to walnut K=k+1 at that move.
-/
theorem candidate
    (left right : ℕ → ℕ)
    (badCount : ℕ → ℕ)

    (hstart :
      OddN (badCount 0))

    (hfinal :
      badCount 2021 = 0)

    (hpreserve :
      ∀ k : ℕ,
        k < 2021 →
        ¬ BadCurrent left right k →
        OddN (badCount k) →
        OddN (badCount (k + 1))) :

    ∃ k a b : ℕ,
      1 ≤ k ∧
      k ≤ 2021 ∧
      a < k ∧
      k < b ∧
      (
        (a = left (k - 1) ∧
         b = right (k - 1))
        ∨
        (a = right (k - 1) ∧
         b = left (k - 1))
      ) :=
