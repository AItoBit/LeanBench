namespace IMO2009P1

/-!
## Initial products
-/

/--
`chainProd a m` is

    a 0 * a 1 * ... * a m.
-/
def chainProd (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => a 0
  | m + 1 => chainProd a m * a (m + 1)

/-!
## One step in the congruence chain
-/
