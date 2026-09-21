/-- **IMO 1992 P3.** -/
theorem candidate :
    IsLeast {n : ℕ | ∀ c : Fin 9 → Fin 9 → Option Bool,
      (∀ i j, c i j = c j i) → n ≤ (colored c).card → HasMono c} 33 :=
