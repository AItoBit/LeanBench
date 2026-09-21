/-- **IMO 1982, Problem 2.**  The three lines `MᵢSᵢ` pass through the common
point `P = e₂/e₁`: for the *real* number `λ = e₃/(e₁e₂)` one has
`P = Mᵢ + λ (Sᵢ - Mᵢ)` for `i = 1, 2, 3`. -/
theorem candidate (u₁ u₂ u₃ A₁ A₂ A₃ S₁ S₂ S₃ M₁ M₂ M₃ : ℂ)
    (hu₁ : u₁ * (starRingEnd ℂ) u₁ = 1) (hu₂ : u₂ * (starRingEnd ℂ) u₂ = 1)
    (hu₃ : u₃ * (starRingEnd ℂ) u₃ = 1)
    (h12 : u₁ + u₂ ≠ 0) (h23 : u₂ + u₃ ≠ 0) (h31 : u₃ + u₁ ≠ 0)
    (he1 : u₁ + u₂ + u₃ ≠ 0) (he2 : u₁ * u₂ + u₂ * u₃ + u₃ * u₁ ≠ 0)
    (hA₁ : A₁ = 2 * u₂ * u₃ / (u₂ + u₃)) (hA₂ : A₂ = 2 * u₃ * u₁ / (u₃ + u₁))
    (hA₃ : A₃ = 2 * u₁ * u₂ / (u₁ + u₂))
    (hS₁ : S₁ = u₂ * u₃ / u₁) (hS₂ : S₂ = u₃ * u₁ / u₂) (hS₃ : S₃ = u₁ * u₂ / u₃)
    (hM₁ : M₁ = (A₂ + A₃) / 2) (hM₂ : M₂ = (A₃ + A₁) / 2) (hM₃ : M₃ = (A₁ + A₂) / 2) :
    ∃ P lam : ℂ, (starRingEnd ℂ) lam = lam ∧
      P = M₁ + lam * (S₁ - M₁) ∧
      P = M₂ + lam * (S₂ - M₂) ∧
      P = M₃ + lam * (S₃ - M₃) :=
