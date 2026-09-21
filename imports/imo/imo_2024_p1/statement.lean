theorem candidate (α : ℝ) :
    (∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊(i : ℝ) * α⌋) ↔
      ∃ m : ℤ, Even m ∧ α = (m : ℝ) :=
