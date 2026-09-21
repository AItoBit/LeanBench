namespace IMO2010P6

open Finset

/--
Legal splitting indices for `n`.
-/
def splits (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 (n - 1)

/--
The value produced by splitting `n` at `k`.
-/
def splitValue
    (a : ℕ → ℝ)
    (n k : ℕ) :
    ℝ :=
  a k + a (n - k)

/--
The recurrence from the problem.

For each `n > s`:

* every legal split has value at most `a n`;
* some legal split attains `a n`.
-/
def MaxRecurrence
    (a : ℕ → ℝ)
    (s : ℕ) :
    Prop :=
  ∀ n : ℕ,
    s < n →
      (∀ k : ℕ,
          k ∈ splits n →
          splitValue a n k ≤ a n) ∧
      ∃ k : ℕ,
        k ∈ splits n ∧
        splitValue a n k = a n

/--
All positive-index terms are positive.
-/
def PositiveSequence
    (a : ℕ → ℝ) :
    Prop :=
  ∀ n : ℕ,
    0 < n →
    0 < a n

/--
A fixed `ℓ` eventually realizes the recurrence.
-/
def EventuallyFixedSplit
    (a : ℕ → ℝ)
    (ℓ N : ℕ) :
    Prop :=
  ∀ n : ℕ,
    N ≤ n →
    ℓ < n →
    a n = a ℓ + a (n - ℓ)

/-! ## Basic split facts -/

/--
Output of the combinatorial valid-type argument from the source:

one of the first `s` indices eventually always realizes the maximum.
-/
def TypeStabilizes
    (a : ℕ → ℝ)
    (s : ℕ) :
    Prop :=
  ∃ ℓ N : ℕ,
    1 ≤ ℓ ∧
    ℓ ≤ s ∧
    ∀ n : ℕ,
      N ≤ n →
      s < n →
      a ℓ + a (n - ℓ) = a n
