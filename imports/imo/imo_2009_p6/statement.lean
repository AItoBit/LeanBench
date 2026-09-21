/-- The main induction:  a grasshopper standing at `p`, with jumps `l` (distinct, positive) still
to perform, can avoid the obstacle set `M` provided that fewer than `l.length` obstacles lie
beyond `p` and that its final landing point is not an obstacle. -/
theorem candidate : ∀ n : ℕ, ∀ (l : List ℕ) (M : Finset ℕ) (p : ℕ), l.length = n →
    (∀ x ∈ l, 0 < x) → l.Nodup → (M.filter (fun m => p < m)).card < n → p + l.sum ∉ M →
    ∃ l', l' ~ l ∧ SafeFrom M p l' :=
