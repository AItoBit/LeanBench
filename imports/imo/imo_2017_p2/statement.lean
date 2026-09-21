theorem candidate
    (f : ℝ → ℝ) :
    (∀ x y : ℝ,
        f (f x * f y) + f (x + y) =
          f (x * y))
      ↔
        f = (0 : ℝ → ℝ)
        ∨
        f = (fun x : ℝ => x - 1)
        ∨
        f = (fun x : ℝ => 1 - x) :=
