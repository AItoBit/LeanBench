by

  have hex :
      ∃ n : ℕ,
        F a n ≤ 0 :=
    exists_F_nonpos
      a
      hinc

  let N : ℕ :=
    Nat.find hex

  have hFN :
      F a N ≤ 0 := by

    dsimp [N]

    exact
      Nat.find_spec hex

  have hNpos :
      0 < N := by

    by_contra hnot

    have hNzero :
        N = 0 := by
      omega

    have hFzero :
        F a 0 = (a 0 : ℤ) :=
      F_zero a

    have ha0 :
        (0 : ℤ) < (a 0 : ℤ) := by
      exact_mod_cast hpos 0

    rw [hNzero, hFzero] at hFN

    linarith

  have hFpred :
      0 < F a (N - 1) := by

    by_contra hnot

    have hp :
        F a (N - 1) ≤ 0 := by
      exact le_of_not_gt hnot

    have hmin :
        N ≤ N - 1 := by

      dsimp [N]

      exact
        Nat.find_min'
          hex
          hp

    omega

  have hNsucc :
      N = (N - 1) + 1 := by
    omega

  have hG :
      0 < G a N := by

    rw [hNsucc]
    rw [G_succ_eq_F]

    exact hFpred

  have hGood :
      GoodIndex a N := by

    refine ⟨hNpos, ?_, ?_⟩

    · unfold G at hG

      linarith

    · unfold F at hFN

      linarith

  refine ⟨N, hGood, ?_⟩

  intro m hm

  exact
    goodIndex_unique
      a
      hinc
      hm
      hGood
