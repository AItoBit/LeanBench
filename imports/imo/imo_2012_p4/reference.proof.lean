by

  by_cases h1 :
      f 1 = 0

  · exact Or.inl h1

  · right

    rcases f_two_cases hf with h2zero | h2four

    · exact
        Or.inl
          ⟨h1, h2zero⟩

    · exact
        Or.inr
          ⟨h1,
           h2four,
           f_three_cases hf h2four⟩
