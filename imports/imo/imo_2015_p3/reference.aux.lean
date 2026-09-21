/--
If `O` is the circumcenter of `A,L,Q`, then

    OA² = OQ².
-/
lemma circumcenter_AQ
    {O A L Q : Point}
    (hO :
      IsCircumcenter O A L Q) :
    distSq O A = distSq O Q := by

  exact hO.1.trans hO.2

/-!
## Perpendicular-bisector calculation
-/

/--
If both `O` and `L` are equidistant from `A` and `Q`,
then `OL` is perpendicular to `AQ`.

This is the analytic form of:

"two points on the perpendicular bisector of AQ determine
the perpendicular-bisector line."
-/
lemma perpendicular_of_two_equidistant_points
    {O L A Q : Point}
    (hO :
      distSq O A = distSq O Q)
    (hL :
      distSq L A = distSq L Q) :
    Perpendicular O L A Q := by

  unfold Perpendicular dot vec distSq at *

  ring_nf at hO hL ⊢

  nlinarith [hO, hL]

/-!
## Perpendicularity transfers across parallel lines
-/

/--
If `OL ⟂ AQ` and `LM ∥ AQ`, then `OL ⟂ LM`.
-/
lemma perpendicular_of_parallel
    {O L M A Q : Point}
    (hperp :
      Perpendicular O L A Q)
    (hparallel :
      Parallel L M A Q) :
    Perpendicular O L L M := by

  rcases hparallel with
    ⟨c, hx, hy⟩

  unfold Perpendicular dot vec at hperp ⊢

  rw [hx, hy]

  calc
    (L.1 - O.1) *
          (c * (Q.1 - A.1)) +
        (L.2 - O.2) *
          (c * (Q.2 - A.2))
        =
      c *
        ((L.1 - O.1) * (Q.1 - A.1) +
         (L.2 - O.2) * (Q.2 - A.2)) := by
          ring

    _ = 0 := by
      rw [hperp]
      ring

/-!
## The exact final lemma used after the source's angle chasing
-/

/--
If

* `O` is the circumcenter of `ALQ`,
* `LA = LQ`,
* `ML ∥ AQ`,

then `ML` is tangent at `L` to the circumcircle of `ALQ`.
-/
theorem tangent_of_isosceles_and_parallel
    {O A L Q M : Point}
    (hcenter :
      IsCircumcenter O A L Q)
    (hisos :
      distSq L A = distSq L Q)
    (hparallel :
      Parallel L M A Q) :
    TangentAt O L M := by

  have hOAQ :
      distSq O A = distSq O Q :=
    circumcenter_AQ hcenter

  have hOLperp :
      Perpendicular O L A Q :=
    perpendicular_of_two_equidistant_points
      hOAQ
      hisos

  have hOLML :
      Perpendicular O L L M :=
    perpendicular_of_parallel
      hOLperp
      hparallel

  exact hOLML

/-!
## Midpoint machinery from the source
-/

/--
If `T` is the midpoint of `HA` and `N` is the midpoint
of `HQ`, then

    2 * TN = AQ

coordinatewise.
-/
lemma midpoint_segment_double
    {H A Q T N : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q) :
    2 * (N.1 - T.1) =
        Q.1 - A.1 ∧
    2 * (N.2 - T.2) =
        Q.2 - A.2 := by

  rcases hT with ⟨hTx, hTy⟩
  rcases hN with ⟨hNx, hNy⟩

  constructor

  · rw [hTx, hNx]
    ring

  · rw [hTy, hNy]
    ring

/-!
## Rectangle/parallelogram relation
-/

/--
The midpoint relation together with the rectangle relation
implies

    LM ∥ AQ.

In fact,

    LM = (1/2) AQ.
-/
lemma parallel_AQ_of_midpoints_rectangle
    {H A Q T N M L : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q)
    (hrect :
      OppositeSidesEqual T N M L) :
    Parallel L M A Q := by

  have hdouble :
      2 * (N.1 - T.1) =
          Q.1 - A.1 ∧
      2 * (N.2 - T.2) =
          Q.2 - A.2 :=
    midpoint_segment_double hT hN

  rcases hdouble with
    ⟨hx2, hy2⟩

  rcases hrect with
    ⟨hxrect, hyrect⟩

  refine ⟨(1 : ℝ) / 2, ?_, ?_⟩

  · rw [hxrect]
    linarith

  · rw [hyrect]
    linarith

/-!
## Source-style final package
-/
