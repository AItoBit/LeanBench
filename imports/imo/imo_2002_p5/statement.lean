/-- Complete classification, including verification of all three solutions. -/
theorem candidate (f : ℝ → ℝ) :
    Satisfies f ↔
      f = (fun _ => 0) ∨ f = (fun _ => (1 / 2 : ℝ)) ∨ f = (fun x => x ^ 2) :=
