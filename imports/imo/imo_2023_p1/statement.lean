/--
Once

* every valid composite n is a prime power;
* every composite prime power satisfies the original
  divisor condition,

the classification follows.
-/
theorem candidate
    (Property : ℕ → Prop)

    (necessity :
      ∀ n : ℕ,
        1 < n →
        ¬ Nat.Prime n →
        Property n →
        IsCompositePrimePower n)

    (sufficiency :
      ∀ p a : ℕ,
        Nat.Prime p →
        2 ≤ a →
        Property (p ^ a)) :

    ∀ n : ℕ,
      1 < n →
      ¬ Nat.Prime n →
      (Property n ↔
       IsCompositePrimePower n) :=
