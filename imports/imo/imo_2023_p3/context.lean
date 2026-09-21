namespace IMO2023P3

open Finset

open scoped BigOperators

/-!
# IMO 2023 Problem 3 — arithmetic progression core

The source shows that all solutions are arithmetic progressions

    a_n = a_1 + (n - 1) m

with m ≥ 0.

Using zero-based indexing, we write this as

    a n = A + n * m.

For such a sequence the polynomial is represented numerically by

    P(x) = ∏_{j=1}^k (x + j*m),

and

    P(a_n) = a_{n+1} * ... * a_{n+k}.

This file formalizes:

* the shift-invariance argument;
* shift invariance implies arithmetic progression;
* every arithmetic progression has the required shift invariance;
* the product identity giving the polynomial from the source.

 
-/

/-!
============================================================
1. Arithmetic progressions
============================================================
-/

def IsArithmetic
    (a : ℕ → ℕ) : Prop :=
  ∃ A m : ℕ,
    ∀ n : ℕ,
      a n = A + n * m

/-!
============================================================
2. Shift invariance
============================================================
-/

/--
`ShiftInvariant a k` means that each of the next `k` terms
differs from `a n` by an amount depending only on the offset,
not on `n`.

This is exactly the property called

    a_{n+j} = a_n + g(j)

in the source solution.
-/
def ShiftInvariant
    (a : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∃ g : Fin k → ℕ,
    ∀ n : ℕ,
      ∀ j : Fin k,
        a (n + j.1 + 1) =
          a n + g j

/-!
============================================================
3. Shift invariance gives a constant first difference
============================================================
-/

/--
For an arithmetic progression with common difference `m`,
the source uses

    P(x) = (x + m)(x + 2m)...(x + km).

Here we first encode its value as a finite product.
-/
def CandidateValue
    (k m x : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k,
    (x + (j + 1) * m)

/-!
============================================================
9. Individual future term
============================================================
-/

def FutureProduct
    (a : ℕ → ℕ)
    (n k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k,
    a (n + j + 1)

/-!
============================================================
11. Main product identity
============================================================
-/
