/-- IMO 2001, Problem 4. The values of a permutation are shifted by one
so that they range over 1, ..., n, as in the original statement. -/
theorem candidate (n : ℕ) (c : Fin n → ℤ) (hodd : Odd n) (hn : 1 < n) :
    ∃ a b : Equiv.Perm (Fin n), a ≠ b ∧
      (Nat.factorial n : ℤ) ∣
        (∑ i, c i * ((a i).val + 1 : ℤ)) -
        (∑ i, c i * ((b i).val + 1 : ℤ)) :=
