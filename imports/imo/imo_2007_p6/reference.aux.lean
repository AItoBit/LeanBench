theorem mem_planeSet {a b c d : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ planeSet a b c d ↔ a * p.1 + b * p.2.1 + c * p.2.2 = d := Iff.rfl
