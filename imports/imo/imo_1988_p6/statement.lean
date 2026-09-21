/-- Restatement in terms of the actual quotient: `(a ^ 2 + b ^ 2) / (a * b + 1)` (a natural
number division, which is exact here) is a square. -/
theorem candidate (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hdvd : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    IsSquare ((a ^ 2 + b ^ 2) / (a * b + 1)) :=
