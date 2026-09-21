lemma D_on_BM
    (a b c : ℝ) :
    Collinear
      pointB
      (pointM a c)
      (pointD a b c) := by

  unfold Collinear det3
  simp [pointB, pointM, pointD]
  ring

/-!
## D lies on CN
-/

lemma D_on_CN
    (a b c : ℝ) :
    Collinear
      pointC
      (pointN a b)
      (pointD a b c) := by

  unfold Collinear det3
  simp [pointC, pointN, pointD]
  ring

/-!
## Circumcircle equation
-/

/--
Substitution of

    D = (-a² : 2b² : 2c²)

into

    a²yz + b²zx + c²xy = 0

gives

    4a²b²c²
      - 2a²b²c²
      - 2a²b²c²
    = 0.
-/
lemma D_on_circumcircle
    (a b c : ℝ) :
    OnCircumcircle
      a b c
      (pointD a b c) := by

  unfold OnCircumcircle pointD
  simp
  ring

/-!
## Combined result
-/

/--
The barycentric core of IMO 2014 Problem 4.

The point

    D = (-a² : 2b² : 2c²)

lies simultaneously on BM, on CN, and on the
circumcircle of ABC.
-/
theorem imo2014_p4_barycentric_core
    (a b c : ℝ) :
    Collinear
        pointB
        (pointM a c)
        (pointD a b c)
    ∧
    Collinear
        pointC
        (pointN a b)
        (pointD a b c)
    ∧
    OnCircumcircle
        a b c
        (pointD a b c) := by

  constructor

  · exact D_on_BM a b c

  · constructor

    · exact D_on_CN a b c

    · exact D_on_circumcircle a b c

/-!
## An explicit substitution identity
-/

/--
The exact polynomial cancellation appearing when D is
substituted into the circumcircle equation.
-/
lemma circumcircle_substitution_identity
    (a b c : ℝ) :
    a ^ 2 * (2 * b ^ 2) * (2 * c ^ 2)
      +
    b ^ 2 * (2 * c ^ 2) * (-(a ^ 2))
      +
    c ^ 2 * (-(a ^ 2)) * (2 * b ^ 2)
      =
    0 := by
  ring

/-!
## Explicit line determinant identities
-/

/--
The determinant for B, M, D vanishes identically.
-/
lemma BM_determinant
    (a b c : ℝ) :
    det3
      pointB
      (pointM a c)
      (pointD a b c)
      =
    0 := by

  simp [det3, pointB, pointM, pointD]
  ring

/--
The determinant for C, N, D vanishes identically.
-/
lemma CN_determinant
    (a b c : ℝ) :
    det3
      pointC
      (pointN a b)
      (pointD a b c)
      =
    0 := by

  simp [det3, pointC, pointN, pointD]
  ring

/-!
## Abstract final form
-/

/--
If a point `D` is simultaneously on `BM`, on `CN`,
and on the circumcircle, then the intersection represented
by `D` lies on the circumcircle.

This packages the final incidence statement.
-/
theorem common_point_on_circumcircle
    {a b c : ℝ}
    {B C M N D : BaryPoint}
    (hBM :
      Collinear B M D)
    (hCN :
      Collinear C N D)
    (hcircle :
      OnCircumcircle a b c D) :
    Collinear B M D ∧
    Collinear C N D ∧
    OnCircumcircle a b c D := by

  exact ⟨hBM, hCN, hcircle⟩

/-!
## Final packaged theorem
-/
