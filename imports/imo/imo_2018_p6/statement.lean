/--
The final result after the source's geometric construction
has reduced the problem to either the common case or the
special right-angle case.
-/
theorem candidate
    (BXA DXC : ℝ)
    (h :
      (∃ φ ψ : ℝ,
          BXA = φ ∧
          DXC = ψ ∧
          φ + ψ = 180)
      ∨
      (∃ AXD CXB : ℝ,
          BXA + DXC + AXD + CXB = 360 ∧
          AXD = 90 ∧
          CXB = 90)) :
    BXA + DXC = 180 :=
