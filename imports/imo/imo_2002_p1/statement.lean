/-- **IMO 2002 P1.** There are as many type 1 subsets as type 2 subsets. -/
theorem candidate (n : ℕ) (R : Finset (ℕ × ℕ))
    (hsub : ∀ p ∈ R, p.1 + p.2 < n)
    (hdown : ∀ p ∈ R, ∀ a b : ℕ, a ≤ p.1 → b ≤ p.2 → (a, b) ∈ R) :
    (Type1 n R).card = (Type2 n R).card :=
