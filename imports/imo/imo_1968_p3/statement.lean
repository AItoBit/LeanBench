/--
Part (b): If Δ = 0, there is exactly one (constant) solution possible.
-/
theorem candidate {ι : Type*} (s : Finset ι)
    (a b c : ℝ) (ha : a ≠ 0) (x : ι → ℝ)
    (hΔ : (b - 1)^2 - 4 * a * c = 0)
    (h_sum : ∑ i ∈ s, (a * x i^2 + (b - 1) * x i + c) = 0) :
    ∀ i ∈ s, x i = (1 - b) / (2 * a) :=
