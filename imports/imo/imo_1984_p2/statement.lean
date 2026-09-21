/-- **IMO 1984, Problem 2.**
Find one pair of positive integers a, b such that:
(i) ab(a + b) is not divisible by 7;
(ii) (a + b)^7 - a^7 - b^7 is divisible by 7^7. -/
theorem candidate :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ ¬(7 ∣ a * b * (a + b)) ∧ 7^7 ∣ (a + b)^7 - a^7 - b^7 :=
