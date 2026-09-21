/--
**IMO 2011 Problem 3.**

If

    f(x+y) ≤ y f(x) + f(f(x))

for all real `x,y`, then

    f(x) = 0

for every `x ≤ 0`.
-/
theorem candidate
    (f : ℝ → ℝ)
    (hf : Good f) :
    ∀ x : ℝ,
      x ≤ 0 →
      f x = 0 :=
