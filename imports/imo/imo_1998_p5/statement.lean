/-- **IMO 1998, Problem 5.**
Let `I` be the incentre of the triangle `ABC`, and let its incircle (centre `I`, radius `r`)
touch the sides `BC`, `CA`, `AB` at `K`, `L`, `M` respectively (tangency being expressed by
saying that each touch point lies on the corresponding open side and that the radius to it is
orthogonal to that side).  The line through `B` parallel to `MK` meets the lines `LM` and `LK`
at `R` and `S` respectively.  Then the angle `RIS` is acute.

In fact the proof shows the sharper statement `⟪R - I, S - I⟫ = r ^ 2`. -/
theorem candidate (A B C I K L M R S : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hIK : dist I K = r) (hIL : dist I L = r) (hIM : dist I M = r)
    (hK : K ∈ openSegment ℝ B C) (hL : L ∈ openSegment ℝ C A) (hM : M ∈ openSegment ℝ A B)
    (hKt : ⟪K - I, C - B⟫ = 0) (hLt : ⟪L - I, A - C⟫ = 0) (hMt : ⟪M - I, B - A⟫ = 0)
    (hRline : R ∈ line[ℝ, L, M]) (hSline : S ∈ line[ℝ, L, K])
    (hRB : ∃ s : ℝ, R = B + s • (K - M)) (hSB : ∃ t : ℝ, S = B + t • (K - M)) :
    EuclideanGeometry.angle R I S < π / 2 :=
