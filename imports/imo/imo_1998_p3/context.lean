open scoped BigOperators

namespace IMO1998P3

def d (n : ℕ) : ℕ :=
  n.divisors.card

def ratio (n : ℕ) : ℚ :=
  (d (n ^ 2) : ℚ) / d n

def factor (e : ℕ) : ℚ :=
  (2 * (e : ℚ) + 1) / ((e : ℚ) + 1)

def chain (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => x :: chain (2 * x) t
