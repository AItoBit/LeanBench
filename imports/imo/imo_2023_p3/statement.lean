/--
If the original polynomial condition is known to be
equivalent to the shift-invariance condition derived in the
source, then the exact sequence classification follows.
-/
theorem candidate
    (PolynomialCondition :
      (ℕ → ℕ) → ℕ → Prop)

    (shift_from_polynomial :
      ∀ a : ℕ → ℕ,
        ∀ k : ℕ,
          2 ≤ k →
          PolynomialCondition a k →
          ShiftInvariant a k)

    (polynomial_from_arithmetic :
      ∀ a : ℕ → ℕ,
        ∀ k : ℕ,
          2 ≤ k →
          IsArithmetic a →
          PolynomialCondition a k) :

    ∀ a : ℕ → ℕ,
      ∀ k : ℕ,
        2 ≤ k →
        (PolynomialCondition a k ↔
         IsArithmetic a) :=
