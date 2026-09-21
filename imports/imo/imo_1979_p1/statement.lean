/-- **IMO 1979, Problem 1.**  If `p / q = 1 - 1/2 + 1/3 - ... - 1/1318 + 1/1319`
for natural numbers `p, q` with `q ≠ 0`, then `1979 ∣ p`. -/
theorem candidate (p q : ℕ) (hq : q ≠ 0)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ) ^ i / (i + 1)) :
    1979 ∣ p :=
