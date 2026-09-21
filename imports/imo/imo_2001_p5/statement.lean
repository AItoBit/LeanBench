/-- **IMO 2001, Problem 5.**  In a triangle `ABC` with `∠BAC = 60°`, let `X` be the point of
segment `BC` for which `AX` bisects `∠BAC`, and let `Y` be the point of segment `AC` for which
`BY` bisects `∠ABC`.  If `AB + BX = AY + YB`, then `∠ABC = 80°`. -/
theorem candidate {A B C X Y : Pt} (hX : Wbtw ℝ B X C) (hY : Wbtw ℝ A Y C)
    (hAX : ∠ B A X = ∠ X A C) (hBY : ∠ A B Y = ∠ Y B C) (hA : ∠ B A C = π / 3)
    (hsum : dist A B + dist B X = dist A Y + dist Y B) :
    ∠ A B C = 4 * π / 9 :=
