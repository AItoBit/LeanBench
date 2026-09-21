/--
Once the source-specific recurrence analysis establishes

    Possible a → Candidate a

and

    Candidate a → Possible a,

the exact IMO classification follows.
-/
theorem candidate
    (necessity :
      ∀ a : ℕ,
        Possible a →
        Candidate v2 v3 a)

    (sufficiency :
      ∀ a : ℕ,
        Candidate v2 v3 a →
        Possible a) :

    ∀ a : ℕ,
      Possible a ↔
      (
        OddN (v2 a) ∧
        v3 a > (v2 a - 1) / 2 ∧
        ¬ 5 ∣ a
      ) :=
