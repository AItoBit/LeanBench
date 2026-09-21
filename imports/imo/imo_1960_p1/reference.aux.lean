set_option maxRecDepth 40000 in
/-- Bounded verification: for every `n < 1000`, the three-digit / divisibility /
digit-square condition holds exactly for `n = 550` and `n = 803`. -/
lemma imo_1960_p1_bounded :
    ∀ n ∈ Finset.range 1000,
      (((Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧
        ((Nat.digits 10 n).map (· ^ 2)).sum = (n / 11 : ℕ)) ↔ (n = 550 ∨ n = 803)) := by
  decide
