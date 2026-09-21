/-- **IMO 1989 P6.** -/
theorem candidate (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (S : Finset Pt) (hS : S.card = n)
    (hcol : ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set Pt))
    (hequi : ∀ p ∈ S, ∃ T : Finset Pt, T ⊆ S.erase p ∧ k ≤ T.card ∧
      ∃ d : ℝ, ∀ q ∈ T, dist p q = d) :
    (k : ℝ) < 1 / 2 + Real.sqrt (2 * n) :=
