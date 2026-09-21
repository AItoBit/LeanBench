/--
If `G` lies on `HA` and `AH ⟂ BD`,
then `GH ⟂ BD`.
-/
lemma radius_perpendicular_of_center_on_altitude
    {A B D H G : Point}
    (hG :
      LiesOnHA A H G)
    (hperp :
      Perpendicular A H B D) :
    Perpendicular G H B D := by

  rcases hG with
    ⟨c, hx, hy⟩

  unfold Perpendicular dot vec at hperp ⊢

  have hx' :
      H.1 - G.1 =
        c * (H.1 - A.1) := by
    linarith

  have hy' :
      H.2 - G.2 =
        c * (H.2 - A.2) := by
    linarith

  rw [hx', hy']

  calc
    c * (H.1 - A.1) * (D.1 - B.1) +
        c * (H.2 - A.2) * (D.2 - B.2)
        =
      c *
        ((H.1 - A.1) * (D.1 - B.1) +
         (H.2 - A.2) * (D.2 - B.2)) := by
          ring

    _ = 0 := by
      rw [hperp]
      ring

/-!
## Tangency
-/

lemma tangent_of_radius_perpendicular
    {O H B D : Point}
    (h :
      Perpendicular O H B D) :
    TangentAt O H B D := by
  exact h

/-!
## Circumcenter consequences
-/

lemma circumcenter_TS
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G T =
      distSq G S := by
  exact h.1

lemma circumcenter_SH
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G S =
      distSq G H := by
  exact h.2

lemma circumcenter_TH
    {G T S H : Point}
    (h :
      IsCircumcenter G T S H) :
    distSq G T =
      distSq G H := by

  calc
    distSq G T
        = distSq G S :=
      h.1

    _ = distSq G H :=
      h.2

/-!
## Final IMO 2014 P3 reduction
-/
