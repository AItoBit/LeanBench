/-- **IMO 1981, Problem 1.**  Let `P` be a point inside the triangle `ABC` (given by strictly
positive barycentric coordinates `α, β, γ`), and let `D`, `E`, `F` be the feet of the
perpendiculars from `P` to the lines `BC`, `CA`, `AB`.  Then

  `BC/PD + CA/PE + AB/PF ≥ (BC + CA + AB)² / (2·area ABC)`,

with equality if and only if `P` is the incenter of the triangle, i.e.
`(a + b + c) • P = a • A + b • B + c • C` with `a = BC`, `b = CA`, `c = AB`; equivalently,
if and only if `PD = PE = PF`. -/
theorem candidate {A B C P D E F : V}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set V))
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hP : P = α • A + β • B + γ • C)
    (hD : D ∈ line[ℝ, B, C]) (hD' : ⟪P - D, C - B⟫ = 0)
    (hE : E ∈ line[ℝ, C, A]) (hE' : ⟪P - E, A - C⟫ = 0)
    (hF : F ∈ line[ℝ, A, B]) (hF' : ⟪P - F, B - A⟫ = 0) :
    (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C
        ≤ dist B C / dist P D + dist C A / dist P E + dist A B / dist P F ∧
      (dist B C / dist P D + dist C A / dist P E + dist A B / dist P F
          = (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C ↔
        (dist B C + dist C A + dist A B) • P = dist B C • A + dist C A • B + dist A B • C) ∧
      (dist B C / dist P D + dist C A / dist P E + dist A B / dist P F
          = (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C ↔
        dist P D = dist P E ∧ dist P E = dist P F) :=
