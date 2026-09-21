namespace Imo1971P3

/-- One step of the construction: from `(k, Q)` to
`((k + 1) * φ (Q * (2 ^ k - 3)), Q * (2 ^ k - 3))`. -/
private def step (p : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + 1) * Nat.totient (p.2 * (2 ^ p.1 - 3)), p.2 * (2 ^ p.1 - 3))

private def seq : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | n + 1 => step (seq n)

/-- The exponents. -/
private def K (n : ℕ) : ℕ := (seq n).1

/-- The running product `∏ i < n, (2 ^ K i - 3)`. -/
private def Q (n : ℕ) : ℕ := (seq n).2

/-- The terms of the infinite subset. -/
private def f (n : ℕ) : ℕ := 2 ^ K n - 3
