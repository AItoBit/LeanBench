theorem candidate (a : ℕ → ℤ)
    (hpos : ∀ i, ∃ j, i < j ∧ 0 < a j)
    (hneg : ∀ i, ∃ j, i < j ∧ a j < 0)
    (hrem : ∀ n : ℕ, 0 < n →
      ((Finset.Icc 1 n).image fun i => Int.emod (a i) n).card = n) :
    ∀ z : ℤ, ∃! i, 0 < i ∧ a i = z :=
