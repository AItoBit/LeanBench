/--
Arithmetic conclusion of the official counting argument:

any table satisfying the source's counting identities has
side length divisible by `9`.
-/
theorem candidate
    {n k a : ℕ}
    (hn :
      n = 3 * k)
    (hcount :
      3 * a = k * k) :
    9 ∣ n :=
