namespace IMO2011P4

open Finset

/-!
## Powers of two
-/

/--
`oddDoubleFactorial n` is

    1 * 3 * 5 * ... * (2n - 1).

In zero-based recursive form:

    oddDoubleFactorial 0 = 1
    oddDoubleFactorial (n+1)
      = (2n+1) * oddDoubleFactorial n.
-/
def oddDoubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 * n + 1) * oddDoubleFactorial n
