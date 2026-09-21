/-- **IMO 1975, Problem 5.**  One *can* find `1975` points on the circumference of a circle of
unit radius such that the distance between any two of them is a rational number. -/
theorem candidate :
    ∃ S : Finset ℂ, S.card = 1975 ∧ (∀ w ∈ S, ‖w‖ = 1) ∧
      ∀ w ∈ S, ∀ v ∈ S, ∃ q : ℚ, dist w v = (q : ℝ) :=
