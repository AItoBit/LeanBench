namespace IMO2013P1

open scoped BigOperators

/-!
# IMO 2013 Problem 1

For all positive integers `k,n`, prove that there exist positive
integers `m₁,...,mₖ` such that

    1 + (2^k - 1)/n
      =
    ∏ᵢ (1 + 1/mᵢ).

We formalize the product over `ℚ`.
-/

/-- A factor of the required product. -/
noncomputable def factor (m : ℕ) : ℚ :=
  1 + 1 / (m : ℚ)

/-- Left-hand side of the IMO identity. -/
noncomputable def target (k n : ℕ) : ℚ :=
  1 + ((2 : ℚ) ^ k - 1) / (n : ℚ)

/--
`Works k n` means there are exactly `k` positive denominators
whose corresponding factors multiply to `target k n`.
-/
def Works (k n : ℕ) : Prop :=
  ∃ ms : List ℕ,
    ms.length = k ∧
    (∀ m ∈ ms, 0 < m) ∧
    (ms.map factor).prod = target k n

/-!
## Algebraic identities
-/
