/-- **IMO 1979, Problem 4** (complete answer).  Let `P` be a point of the plane `p` (given here
as the plane through `P` with nonzero normal vector `nv`) and let `Q ∉ p`.  Then
`√(2·PQ/(PQ - PT))`, with `T` the orthogonal projection of `Q` on `p`, is the greatest value of
`(QP + PR)/QR` for `R ∈ p`, and it is attained exactly at those points `R` of `p` with `PR = PQ`
lying on the ray `PT` (the ray condition degenerating to no condition at all when `T = P`, i.e.
when `PQ ⊥ p`). -/
theorem candidate (hnv : nv ≠ 0) (hQ : Q ∉ plane P nv) :
    IsGreatest ((fun R : E => (dist Q P + dist P R) / dist Q R) '' plane P nv)
        (maxRatio P Q nv) ∧
      ∀ R ∈ plane P nv,
        ((dist Q P + dist P R) / dist Q R = maxRatio P Q nv ↔
          dist P R = dist P Q ∧
            ⟪R - P, foot P Q nv - P⟫ = ‖R - P‖ * ‖foot P Q nv - P‖) :=
