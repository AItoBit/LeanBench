namespace IMO2009P5

open Finset

/-- Three natural numbers satisfy the strict triangle inequalities. -/
def TriangleSides (a b c : ℕ) : Prop :=
  a < b + c ∧
  b < a + c ∧
  c < a + b

/-! ## Elementary triangle lemmas -/

/--
The condition from the olympiad problem.
-/
def Good (f : ℕ → ℕ) : Prop :=
  (∀ n : ℕ,
      0 < n →
      0 < f n) ∧
  (∀ a b : ℕ,
      0 < a →
      0 < b →
      TriangleSides
        a
        (f b)
        (f (b + f a - 1)))
