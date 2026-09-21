/-- **IMO 1987 P5.** -/
theorem candidate (n : ℕ) (hn : 3 ≤ n) :
    ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧
      (∀ i j, i ≠ j → Irrational (eDist (P i) (P j))) ∧
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        triArea (P i) (P j) (P k) ≠ 0 ∧ ∃ q : ℚ, triArea (P i) (P j) (P k) = q) :=
