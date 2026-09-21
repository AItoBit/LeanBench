/-- If `X` is strictly on the same side of the line `AB` as `C`, then the oriented angles
`∡ A B X` and `∡ A B C` have the same sign. -/
theorem candidate {A B C X : Pt} (h : line[ℝ, A, B].SSameSide C X) :
    (∡ A B X).sign = (∡ A B C).sign :=
