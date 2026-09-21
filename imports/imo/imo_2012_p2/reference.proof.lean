by

  have hmul :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2) * a (i + 2))
        ≤
      ∏ i ∈ Finset.range (n - 1),
        (a (i + 2) + 1) ^ (i + 2) :=
    multiply_amgm_bounds
      a
      n
      hn
      hpos
      hAMGM

  have hcoeff :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2))
        =
      ((n : ℝ) ^ n) :=
    coeff_prod_to_n hn

  have hleft :
      (∏ i ∈ Finset.range (n - 1),
          coeff (i + 2) * a (i + 2))
        =
      ((n : ℝ) ^ n) := by

    rw [Finset.prod_mul_distrib]
    rw [hcoeff]
    rw [hprod]

    ring

  rw [hleft] at hmul

  exact hmul
