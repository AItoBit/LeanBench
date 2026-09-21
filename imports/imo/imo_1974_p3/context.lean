open scoped BigOperators

open scoped Nat

set_option maxHeartbeats 1000000

/-!
# IMO 1974, Problem 3

Prove that the number `∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)` is not divisible by `5`
for any integer `n ≥ 0`.

The proof works in the ring `ℤ√2`.  Writing `(1 + √2)^(2n+1) = A n + B n √2` one has
`A n = ∑_{k=0}^n C(2n+1,2k) 2^k`, `B n = ∑_{k=0}^n C(2n+1,2k+1) 2^k`, and taking norms
gives the Pell identity `A n ^ 2 - 2 * B n ^ 2 = -1`.

Modulo `5` we have `8 = 2^3 ≡ 2⁻¹`, and reversing the order of summation (together with the
symmetry `C(2n+1, 2(n-k)+1) = C(2n+1, 2k)`) shows `2^n * S n ≡ A n [ZMOD 5]`, where `S n`
is the sum from the problem.  Hence `5 ∣ S n` would force `A n ≡ 0`, so `2 * B n ^ 2 ≡ 1`
modulo `5`, which is impossible since `3` is not a square modulo `5`.
-/

namespace IMO1974P3

/-- The "rational part" of `(1 + √2) ^ (2n+1)`: `A n = ∑_{k=0}^{n} C(2n+1, 2k) 2^k`. -/
def A (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (2 * k) : ℤ) * 2 ^ k

/-- The "irrational part" of `(1 + √2) ^ (2n+1)`: `B n = ∑_{k=0}^{n} C(2n+1, 2k+1) 2^k`. -/
def B (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (2 * k + 1) : ℤ) * 2 ^ k

/-- The sum appearing in the problem: `S n = ∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (2 * n + 1).choose (2 * k + 1) * 2 ^ (3 * k)
