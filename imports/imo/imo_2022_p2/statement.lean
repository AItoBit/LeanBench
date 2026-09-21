theorem candidate
    (f : ℝ → ℝ)

    (hfpos :
      ∀ x : ℝ,
        0 < x →
        0 < f x)

    (huniq :
      ∀ x : ℝ,
        0 < x →
        ∃! y : ℝ,
          0 < y ∧
          x * f y +
              y * f x
            ≤
          2) :

    ∀ x : ℝ,
      0 < x →
      f x = 1 / x :=
