open scoped Nat

/-!
# IMO 1962 Problem 1

Find the smallest natural number `n` whose decimal representation ends in `6` and such that
moving that final `6` to the front of the number multiplies it by `4`.

The answer is `153846`.
-/

namespace Imo1962P1

open Nat

/-- The predicate describing the problem: the last decimal digit of `n` is `6`, and moving
this digit to the front multiplies `n` by `4`. -/
def ProblemPredicate (n : ℕ) : Prop :=
  n % 10 = 6 ∧ ofDigits 10 ((digits 10 n).tail.concat 6) = 4 * n

/-- A reformulation of the problem avoiding digit lists: `n = 10 * c + 6` and prefixing `6`
to the decimal representation of `c` yields `4 * n`. -/
abbrev ProblemPredicate' (c n : ℕ) : Prop :=
  n = 10 * c + 6 ∧ 6 * 10 ^ (digits 10 c).length + c = 4 * n

end Imo1962P1

open Imo1962P1
