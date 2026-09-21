open Finset

namespace Imo1992P6

/-- `n²` is a sum of exactly `k` positive squares. -/
def Rep (n k : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < k, 0 < f i) ∧ ∑ i ∈ Finset.range k, (f i) ^ 2 = n ^ 2

/-- `m` is a valid value for the "greatest" in the definition of `S n`. -/
def Good (n m : ℕ) : Prop := ∀ k, 1 ≤ k → k ≤ m → Rep n k

/-! ### The numerical semigroup step -/
