theorem candidate
    (Cwide Cstrip : ℝ)

    (hCwide :
      0 < Cwide)

    (hCstrip :
      0 < Cstrip)

    (wide_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          Wide n S →
          HasSeparatingLine
            S
            (Cwide * nScale n))

    (strip_packing_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ¬ Wide n S →
          HasSeparatingLine
            S
            (Cstrip * nScale n)) :

    ∃ C : ℝ,
      0 < C ∧
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ∃ L : Line,
            Separates S L ∧
            ∀ x ∈ S,
              C * nScale n
                ≤
              lineDistance L x :=
