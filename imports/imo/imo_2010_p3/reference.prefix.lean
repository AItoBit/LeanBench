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

/--
For positive `t`, the product `t(t+1)` cannot be a square.

It lies strictly between `t²` and `(t+1)²`.
-/
lemma not_square_mul_succ
    (t : ℕ)
    (ht : 0 < t) :
    ¬ IsSquare (t * (t + 1)) := by

  rintro ⟨r, hr⟩

  have hl :
      t * t < r * r := by
    rw [← hr]
    nlinarith

  have hu :
      r * r < (t + 1) * (t + 1) := by
    rw [← hr]
    nlinarith

  have htr :
      t < r := by
    by_contra h
    have hle :
        r ≤ t := by
      omega
    nlinarith

  have hrt :
      r < t + 1 := by
    by_contra h
    have hle :
        t + 1 ≤ r := by
      omega
    nlinarith

  omega

/--
For positive `t`, the product `t(t+2)` cannot be a square.

Indeed,

    t² < t(t+2) < (t+1)².
-/
lemma not_square_mul_add_two
    (t : ℕ)
    (ht : 0 < t) :
    ¬ IsSquare (t * (t + 2)) := by

  rintro ⟨r, hr⟩

  have hl :
      t * t < r * r := by
    rw [← hr]
    nlinarith

  have hu :
      r * r < (t + 1) * (t + 1) := by
    rw [← hr]
    nlinarith

  have htr :
      t < r := by
    by_contra h
    have hle :
        r ≤ t := by
      omega
    nlinarith

  have hrt :
      r < t + 1 := by
    by_contra h
    have hle :
        t + 1 ≤ r := by
      omega
    nlinarith

  omega

/-! ## Consequences of the square condition -/
