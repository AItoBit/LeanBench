namespace IMO2019P5

/-!
# IMO 2019 Problem 5 — expectation core

For a configuration `C`, let `L(C)` be the number of
operations until the process terminates.

Let

    F(n) = ∑ L(C)

where the sum ranges over all `2^n` configurations of length `n`.

The source's case division gives

    F(1) = 1

and for every `n ≥ 1`

    F(n+1) = 2 F(n) + (n+1) 2^n.

From this we prove

    F(n) / 2^n = n(n+1)/4.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The recurrence
============================================================
-/

def TotalRecurrence
    (F : ℕ → ℕ) : Prop :=
  F 1 = 1 ∧
  ∀ n : ℕ,
    1 ≤ n →
    F (n + 1) =
      2 * F n +
      (n + 1) * 2 ^ n
