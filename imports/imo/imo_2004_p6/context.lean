namespace Imo2004P6

/-- `m` is alternating: consecutive decimal digits have different parity. Digit `i` of `m` has the
parity of `m / 10 ^ i`, and exists exactly when `10 ^ i ≤ m`. -/
def Alternating (m : ℕ) : Prop :=
  ∀ i : ℕ, 10 ^ (i + 1) ≤ m → (m / 10 ^ i) % 2 ≠ (m / 10 ^ (i + 1)) % 2

/-! ### Sanity checks on the definition -/
