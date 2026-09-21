open scoped BigOperators

open scoped Nat

set_option maxHeartbeats 1000000

/-!
# IMO 1995 Problem 6

Let `p` be an odd prime.  The number of `p`-element subsets `A` of `{1, 2, …, 2p}`
whose element sum is divisible by `p` is `(C(2p, p) - 2)/p + 2`.

The proof uses the model `G p = ZMod p × Fin 2` for the ground set `{1, …, 2p}`
(an element `n` corresponds to its residue together with the information of which
half of the interval it lies in), and a free shift action of `ZMod p` on the first
half of the ground set.
-/

namespace IMO1995P6

open Finset

/-- The model of the ground set `{1, 2, …, 2p}`: a residue mod `p` together with a
half-indicator. -/
abbrev G (p : ℕ) : Type := ZMod p × Fin 2

variable {p : ℕ} [NeZero p]

/-- The `i`-th half of the ground set. -/
def half (p : ℕ) [NeZero p] (i : Fin 2) : Finset (G p) :=
  {b : G p | b.2 = i}

/-- The number of elements of `B` lying in the first half. -/
def mlen (B : Finset (G p)) : ℕ := (B.filter (fun b => b.2 = 0)).card

/-- Shift by `k` on the first half, identity on the second half. -/
def sh (k : ZMod p) (b : G p) : G p := (b.1 + (if b.2 = 0 then k else 0), b.2)

/-- All `p`-element subsets of the ground set. -/
def S (p : ℕ) [NeZero p] : Finset (Finset (G p)) := powersetCard p univ

/-- The `p`-element subsets that meet both halves. -/
def X (p : ℕ) [NeZero p] : Finset (Finset (G p)) :=
  (S p).filter (fun B => 0 < mlen B ∧ mlen B < p)

/-- The residue-sum of a subset of the model. -/
def rsum (B : Finset (G p)) : ZMod p := ∑ b ∈ B, b.1

/-- Encoding of the model into `{1, 2, …, 2p}`. -/
def enc (b : G p) : ℕ := b.1.val + 1 + p * b.2.val

/-- Decoding of `{1, 2, …, 2p}` into the model. -/
def dec (p : ℕ) [NeZero p] (n : ℕ) : G p := (((n - 1 : ℕ) : ZMod p), if n ≤ p then 0 else 1)

end IMO1995P6
