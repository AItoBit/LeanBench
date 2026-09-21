/-- **IMO 1988, Problem 5.**
In a right-angled triangle `ABC` (with the right angle at `A`), let `AD` be the altitude drawn to
the hypotenuse, and let the straight line joining the incentres of the triangles `ABD`, `ACD`
intersect the sides `AB`, `AC` at the points `K`, `L` respectively.  If `E` and `E₁` denote the
areas of the triangles `ABC` and `AKL` respectively, then `E / E₁ ≥ 2`. -/
theorem candidate (A B C D K L : Pt) (T₁ T₂ : Affine.Triangle ℝ Pt)
    (hT₁ : T₁.points = ![A, B, D]) (hT₂ : T₂.points = ![A, C, D])
    (hAB : A ≠ B) (hAC : A ≠ C) (hright : ⟪B - A, C - A⟫ = 0)
    (hD : D ∈ line[ℝ, B, C]) (hDperp : ⟪A - D, C - B⟫ = 0)
    (hK : K ∈ line[ℝ, A, B]) (hL : L ∈ line[ℝ, A, C])
    (hKcol : Collinear ℝ ({T₁.incenter, T₂.incenter, K} : Set Pt))
    (hLcol : Collinear ℝ ({T₁.incenter, T₂.incenter, L} : Set Pt)) :
    2 ≤ area A B C / area A K L :=
