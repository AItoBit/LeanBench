/-- **1966 IMO Problem 4**
    For any natural number `n` and real `x` such that all intermediate sines are non-zero:
    ∑_{i=1}^n 1 / sin (2^i * x) = cot x - cot (2^n * x). -/
theorem candidate (n : ℕ) (x : ℝ) (h : ∀ t ≤ n, sin (2^t * x) ≠ 0) :
    ∑ i ∈ Finset.range n, (1 / sin (2^(i + 1) * x)) = cos x / sin x - cos (2^n * x) / sin (2^n * x) :=
