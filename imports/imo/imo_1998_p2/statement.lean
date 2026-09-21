theorem candidate
    (a b : ℕ) (k : ℝ)
    (ha : 0 < a)
    (hb : 3 ≤ b)
    (hodd : Odd b)
    (vote : Fin a → Fin b → Bool)
    (hpair : ∀ j l : Fin b, j ≠ l →
      (agreementCount vote j l : ℝ) ≤ k) :
    ((b : ℝ) - 1) / (2 * b) ≤ k / a :=
