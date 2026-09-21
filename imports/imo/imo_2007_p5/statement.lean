/-- **IMO 2007, Problem 5.** For positive integers `a`, `b`, if `4ab - 1` divides `(4a² - 1)²`
then `a = b`. -/
theorem candidate (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : (4 * a * b - 1) ∣ (4 * a ^ 2 - 1) ^ 2) : a = b :=
