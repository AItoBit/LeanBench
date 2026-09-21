/-- **IMO 1975, Problem 1.**
Let `x i`, `y i` (`i = 1, …, n`) be real numbers with
`x 1 ≥ x 2 ≥ … ≥ x n` and `y 1 ≥ y 2 ≥ … ≥ y n`.
If `z` is any permutation of `y`, then
`∑ (x i - y i)^2 ≤ ∑ (x i - z i)^2`. -/
theorem candidate {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y)
    (σ : Equiv.Perm (Fin n)) (z : Fin n → ℝ) (hz : ∀ i, z i = y (σ i)) :
    ∑ i, (x i - y i) ^ 2 ≤ ∑ i, (x i - z i) ^ 2 :=
