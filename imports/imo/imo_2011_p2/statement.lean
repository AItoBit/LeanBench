/--
Every point of the configuration occurs as pivot arbitrarily late.

This is the combinatorial conclusion of the windmill argument.
-/
theorem candidate
    {N : ℕ}
    (W : HalfTurnWindmill N) :
    ∀ p : Fin N,
      ∀ B : ℕ,
        ∃ t : ℕ,
          B < t ∧
          W.pivot t = p :=
