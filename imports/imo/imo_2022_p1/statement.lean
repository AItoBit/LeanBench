theorem candidate
    {n k : ℕ}
    (hk2n :
      k ≤ 2 * n)

    (hlower :
      ∀ j : ℕ,
        j < n →
        ¬ Works n j)

    (hupper :
      ∀ j : ℕ,
        (3 * n) / 2 < j →
        j ≤ 2 * n →
        ¬ Works n j)

    (hmiddle :
      ∀ j : ℕ,
        n ≤ j →
        j ≤ (3 * n) / 2 →
        Works n j) :

    Works n k ↔
      k ∈ AnswerSet n :=
