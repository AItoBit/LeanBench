theorem candidate
    {n : ℕ}
    (x : Fin n → ℝ)
    (henergy :
      2 *
          (∑ i : Fin n,
            ∑ j : Fin n,
              Real.sqrt |x i - x j|)
        -
      2 *
          (∑ i : Fin n,
            ∑ j : Fin n,
              Real.sqrt |x i + x j|)
        ≤
      0) :
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i - x j|)
      ≤
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i + x j|) :=
