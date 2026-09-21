/--
Once the source reduction is established, the only positive
solution pair is `(1,1)`.
-/
theorem candidate
    (source_reduction :
      ∀ {a b : ℕ},
        0 < a →
        0 < b →
        EventuallyConstantGCD a b →
        ∃ D : NormalizedData a b,
          ∃ g : ℕ,
            0 < g ∧
            (g = D.d ∨
             g = 2 * D.d) ∧
            D.d ^ 2 * D.x * D.y + 1 ∣ g) :

    ∀ a b : ℕ,
      0 < a →
      0 < b →
      (EventuallyConstantGCD a b ↔
       (a = 1 ∧ b = 1)) :=
