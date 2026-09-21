by

  have hodd :
      ∀ m : ℕ,
        b 1 + 3 * m ≤
          b (1 + 2 * m) := by

    intro m

    induction m with

    | zero =>
        simp

    | succ m ih =>

      have hn :
          1 ≤ 1 + 2 * m := by
        omega

      have hs :
          b (1 + 2 * m) + 3
            ≤
          b ((1 + 2 * m) + 2) :=
        hstep
          (1 + 2 * m)
          hn

      calc
        b 1 + 3 * (m + 1)
            =
          (b 1 + 3 * m) + 3 := by
            ring

        _ ≤
          b (1 + 2 * m) + 3 := by
            exact
              Nat.add_le_add_right
                ih
                3

        _ ≤
          b ((1 + 2 * m) + 2) :=
            hs

        _ =
          b (1 + 2 * (m + 1)) := by
            ring

  have h :
      b 1 + 3 * 1011 ≤
        b (1 + 2 * 1011) :=
    hodd 1011

  rw [h1] at h

  norm_num at h ⊢

  exact h
