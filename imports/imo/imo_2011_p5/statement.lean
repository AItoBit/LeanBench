/--
**IMO 2011 Problem 5.**

If

    f(m-n) ∣ f(m)-f(n)

for all integers `m,n`, and all values of `f` are positive, then

    f(m) ≤ f(n)  →  f(m) ∣ f(n).
-/
theorem candidate
    (f : ℤ → ℤ)
    (hpos :
      ∀ x : ℤ,
        0 < f x)
    (hdiv :
      ∀ m n : ℤ,
        f (m - n) ∣ f m - f n) :
    ∀ m n : ℤ,
      f m ≤ f n →
      f m ∣ f n :=
