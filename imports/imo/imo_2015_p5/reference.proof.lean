by

  constructor

  · intro h

    exact
      only_solutions h

  · intro h

    rcases h with
      hid | href

    · have hf :
          f = fun x : ℝ => x := by

        funext x

        exact hid x

      rw [hf]

      exact identity_satisfies

    · have hf :
          f = fun x : ℝ => 2 - x := by

        funext x

        exact href x

      rw [hf]

      exact reflection_satisfies
