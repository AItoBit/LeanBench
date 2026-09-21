open Finset

namespace Imo1997P4

/-- The `i`-th row and column together exhaust `{1, …, 2n-1}`. -/
def Silver (n : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  ∀ i : Fin n,
    (univ.image fun j => M i j) ∪ (univ.image fun j => M j i) = Finset.Icc 1 (2 * n - 1)

/-! ### Part (a) -/

/-- The cells of the `i`-th cross. -/
def cross (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) :=
  (univ.image fun j : Fin n => (i, j)) ∪ (univ.image fun j : Fin n => (j, i))

/-- The `xor` construction, silver whenever `n` is a power of two. -/
def SM (n : ℕ) (i j : Fin n) : ℕ :=
  if i.val = j.val then 2 * n - 1
  else if i.val < j.val then i.val ^^^ j.val
  else (i.val ^^^ j.val) + (n - 1)
