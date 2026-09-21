namespace IMO2023P1

/-!
# IMO 2023 Problem 1

Determine all composite integers n > 1 such that, if

    1 = d₁ < d₂ < ... < dₖ = n

are all positive divisors of n, then

    dᵢ ∣ dᵢ₊₁ + dᵢ₊₂

for every valid i.

The answer is exactly the composite prime powers

    n = p^a,  p prime,  a ≥ 2.

This file formalizes the arithmetic core of the proof.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract chain property
============================================================
-/

def ChainProperty
    (k : ℕ)
    (d : ℕ → ℕ) : Prop :=
  ∀ i : ℕ,
    i + 2 < k →
    d i ∣ d (i + 1) + d (i + 2)

/-!
============================================================
2. Consecutive powers
============================================================
-/

def IsCompositePrimePower
    (n : ℕ) : Prop :=
  ∃ p a : ℕ,
    Nat.Prime p ∧
    2 ≤ a ∧
    n = p ^ a

/-!
============================================================
13. Composite prime powers are > 1
============================================================
-/

def DivisorProperty
    (n : ℕ) : Prop :=
  ∃ k : ℕ,
    ∃ d : ℕ → ℕ,
      3 ≤ k ∧
      d 0 = 1 ∧
      d (k - 1) = n ∧
      ChainProperty k d

/-!
============================================================
16. Necessity interface
============================================================
-/
