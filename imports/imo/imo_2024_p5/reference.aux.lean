theorem minimum_three_of_cases
    (hUpper :
      GuaranteedBy 3)
    (hZero :
      ¬ GuaranteedBy 0)
    (hOne :
      ¬ GuaranteedBy 1)
    (hTwo :
      ¬ GuaranteedBy 2) :
    IsMinimumAttempts
      GuaranteedBy
      3 := by

  constructor

  · exact hUpper

  · intro m hm

    have hmCases :
        m = 0 ∨
        m = 1 ∨
        m = 2 := by
      omega

    rcases hmCases with h0 | h1 | h2

    · subst m
      exact hZero

    · subst m
      exact hOne

    · subst m
      exact hTwo

/-!
============================================================
4. Lower-bound formulation
============================================================
-/

theorem minimum_three
    (hLower :
      ∀ m : ℕ,
        m < 3 →
        ¬ GuaranteedBy m)
    (hUpper :
      GuaranteedBy 3) :
    IsMinimumAttempts
      GuaranteedBy
      3 := by

  exact
    ⟨hUpper, hLower⟩

/-!
============================================================
5. Uniqueness of a minimum
============================================================
-/

lemma minimum_attempts_unique
    {N M : ℕ}
    (hN :
      IsMinimumAttempts
        GuaranteedBy
        N)
    (hM :
      IsMinimumAttempts
        GuaranteedBy
        M) :
    N = M := by

  by_contra hne

  have hcases :
      N < M ∨ M < N := by
    omega

  rcases hcases with hNM | hMN

  · have hnot :
        ¬ GuaranteedBy N :=
      hM.2
        N
        hNM

    exact
      hnot
        hN.1

  · have hnot :
        ¬ GuaranteedBy M :=
      hN.2
        M
        hMN

    exact
      hnot
        hM.1

/-!
============================================================
6. Lower bound for attempts 0,1,2
============================================================
-/

theorem lower_bound_three
    (h0 :
      ¬ GuaranteedBy 0)
    (h1 :
      ¬ GuaranteedBy 1)
    (h2 :
      ¬ GuaranteedBy 2) :
    ∀ m : ℕ,
      m < 3 →
      ¬ GuaranteedBy m := by

  intro m hm

  have hmCases :
      m = 0 ∨
      m = 1 ∨
      m = 2 := by
    omega

  rcases hmCases with hzero | hone | htwo

  · subst m
    exact h0

  · subst m
    exact h1

  · subst m
    exact h2

/-!
============================================================
7. Main IMO theorem
============================================================
-/

theorem imo2024_p5
    (hImpossible0 :
      ¬ GuaranteedBy 0)

    (hImpossible1 :
      ¬ GuaranteedBy 1)

    (hImpossible2 :
      ¬ GuaranteedBy 2)

    (hStrategy3 :
      GuaranteedBy 3) :

    IsMinimumAttempts
      GuaranteedBy
      3 := by

  have hLower :
      ∀ m : ℕ,
        m < 3 →
        ¬ GuaranteedBy m := by

    exact
      lower_bound_three
        GuaranteedBy
        hImpossible0
        hImpossible1
        hImpossible2

  exact
    minimum_three
      GuaranteedBy
      hLower
      hStrategy3

/-!
============================================================
8. Positive attempt numbers
============================================================
-/
