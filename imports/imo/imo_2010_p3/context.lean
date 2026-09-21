namespace IMO2010P3

/-! ## Problem predicates -/

/--
The original square condition, with zero-based indexing for the
positive integers.
-/
def Good (g : ℕ → ℕ) : Prop :=
  ∀ m n : ℕ,
    IsSquare
      ((g m + (n + 1)) *
       (g n + (m + 1)))

/--
The key Lemma 2 from the published proof:

successive values differ by exactly one.
-/
def AdjacentUnit (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    g (n + 1) = g n + 1 ∨
    g n = g (n + 1) + 1

/-! ## Elementary nonsquare lemmas -/
