open List

namespace Imo1989P6

/-! ### Pairs and partners -/

/-- `a` and `b` differ by `n`. -/
def Pair (n a b : ℕ) : Prop := a + n = b ∨ b + n = a

/-- The relation "these two values do *not* differ by `n`". -/
def NotPair (n a b : ℕ) : Prop := ¬ Pair n a b

/-- The partner of `a` inside `{0, …, 2n-1}`. -/
def ptn (n a : ℕ) : ℕ := if a < n then a + n else a - n

/-- All listings of `{0, …, 2n-1}`. -/
def perms (n : ℕ) : Finset (List ℕ) := (List.range (2 * n)).permutations.toFinset
