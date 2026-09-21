/-- **IMO 1975, Problem 3.**  On the sides of an arbitrary (positively oriented) triangle
`ABC`, triangles `ABR`, `BCP`, `CAQ` are constructed externally with
`∠CBP = ∠CAQ = 45°`, `∠BCP = ∠ACQ = 30°` and `∠ABR = ∠BAR = 15°`.
Then `∠QRP = 90°` and `QR = RP` (and the points `R`, `P`, `Q` are pairwise distinct, so that
the angle `∠QRP` is a genuine angle). -/
theorem candidate {A B C P Q R : ℂ} (horient : 0 < ((C - A) / (B - A)).im)
    (hPB : ∃ t : ℝ, 0 < t ∧ P - B = (t : ℂ) * rot (-(π / 4)) * (C - B))
    (hPC : ∃ t : ℝ, 0 < t ∧ P - C = (t : ℂ) * rot (π / 6) * (B - C))
    (hQC : ∃ t : ℝ, 0 < t ∧ Q - C = (t : ℂ) * rot (-(π / 6)) * (A - C))
    (hQA : ∃ t : ℝ, 0 < t ∧ Q - A = (t : ℂ) * rot (π / 4) * (C - A))
    (hRA : ∃ t : ℝ, 0 < t ∧ R - A = (t : ℂ) * rot (-(π / 12)) * (B - A))
    (hRB : ∃ t : ℝ, 0 < t ∧ R - B = (t : ℂ) * rot (π / 12) * (A - B)) :
    R ≠ P ∧ R ≠ Q ∧ EuclideanGeometry.angle Q R P = π / 2 ∧ dist Q R = dist R P :=
