/-- **IMO 1999 P4.** -/
theorem candidate (n p : ℕ) (hp : p.Prime) (hn : 0 < n) (hle : n ≤ 2 * p) :
    n ^ (p - 1) ∣ (p - 1) ^ n + 1 ↔
      (n = 1 ∨ (n = 2 ∧ p = 2) ∨ (n = 3 ∧ p = 3)) :=
