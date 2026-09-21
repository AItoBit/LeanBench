/-- **IMO 2002 P6**, granting the geometric inputs described at the top of the file. -/
theorem candidate (n : ℕ) (hn : 3 ≤ n) (d : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, d i j = d j i)
    (H : Finset (Fin n)) (hH3 : 3 ≤ H.card)
    (far : Fin n → Fin n) (θ : Fin n → ℝ)
    (hfar : ∀ i ∈ H, far i ≠ i)
    (hfarmin : ∀ i ∈ H, ∀ j : Fin n, j ≠ i → 2 / d i (far i) ≤ 2 / d i j)
    (hhull : ∀ i ∈ H, ∑ j ∈ (univ.erase i).erase (far i), 2 / d i j ≤ θ i)
    (hθ : ∑ i ∈ H, θ i = ((H.card : ℝ) - 2) * Real.pi)
    (hinner : ∀ i ∈ Hᶜ, ∑ j ∈ univ.erase i, 2 / d i j ≤ Real.pi) :
    ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), 1 / d i j
      ≤ ((n : ℝ) - 1) * Real.pi / 4 :=
