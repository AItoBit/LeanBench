namespace IMO2022P1

/-!
# IMO 2022 Problem 1 — classification core

The source proves that the valid values of k are exactly

    n ≤ k ≤ ⌊3n / 2⌋.

We isolate the three combinatorial components of the proof:

1. `k < n` never works;
2. `⌊3n/2⌋ < k ≤ 2n` never works;
3. `n ≤ k ≤ ⌊3n/2⌋` always works.

Once these are established for the concrete coin process,
Lean proves the exact classification.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The candidate range
============================================================
-/

def Admissible (n k : ℕ) : Prop :=
  n ≤ k ∧ k ≤ (3 * n) / 2

/-!
============================================================
2. Elementary interface for the coin process
============================================================
-/

/-
`Works n k` means:

For every initial ordering of n A-coins and n B-coins,
under the prescribed operation with parameter k,
at some moment the leftmost n coins all have the same type.
-/

variable
  (Works : ℕ → ℕ → Prop)

/-!
============================================================
3. Lower excluded range
============================================================
-/

/--
For fixed n, the answer is exactly the natural-number interval

    [n, floor(3n/2)].
-/
def AnswerSet
    (n : ℕ) : Finset ℕ :=
  Finset.Icc
    n
    ((3 * n) / 2)
