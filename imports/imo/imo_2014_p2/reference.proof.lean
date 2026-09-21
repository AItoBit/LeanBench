q - 1
    k * k < n ∧
    n ≤ (k + 1) * (k + 1) ∧
    n - k + 1 >
      k * (k - 1) + 1 ∧
    ∀ m : ℕ,
      m * m < n →
      m ≤ k := by

  let k := q - 1

  have hqpos :
      0 < q := by
    omega

  have hkpos :
      1 ≤ k := by

    dsimp [k]

    omega

  have hpred :
      (q - 1) * (q - 1) < n :=
    pred_sq_lt_of_minimal_square
      hqpos
      hminimal

  have hksq :
      k * k < n := by

    simpa [k] using hpred

  have hkq :
      k + 1 = q := by

    dsimp [k]

    omega

  have hupperK :
      n ≤
        (k + 1) * (k + 1) := by

    rw [hkq]

    exact hupper

  have hcount :
      n - k + 1 >
        k * (k - 1) + 1 :=
    key_counting_inequality'
      hkpos
      hksq

  have hnpos :
      0 < n := by
    omega

  refine
    ⟨hksq,
     hupperK,
     hcount,
     ?_⟩

  intro m hm

  exact
    maximal_of_square_boundary
      hupperK
      hm
