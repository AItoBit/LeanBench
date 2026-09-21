/--
Expanded form of collinearity.
-/
lemma collinear_iff
    (P Q R : Point) :
    Collinear P Q R ↔
      (Q.1 - P.1) * (R.2 - P.2)
        -
      (Q.2 - P.2) * (R.1 - P.1)
        = 0 := by
  rfl

/--
A repeated point gives a collinear triple.
-/
lemma collinear_self_left
    (P Q : Point) :
    Collinear P P Q := by
  simp [Collinear, cross, vec]

/--
Swapping the last two points preserves collinearity.
-/
lemma collinear_swap_last
    {P Q R : Point}
    (h : Collinear P Q R) :
    Collinear P R Q := by
  unfold Collinear cross vec at h ⊢
  nlinarith

/-!
## Main fixed-point identity
-/

/--
Pure algebra behind the source's fixed-line argument.

Let

    S = A + D

and define

    X = (S, w*u)
    Y = (0, (S-w)*v)
    H = (A, D*v).

If

    A*u = D*v,

then `X,Y,H` are collinear.
-/
lemma fixed_point_collinear
    (A D u v w : ℝ)
    (hrel :
      A * u = D * v) :
    Collinear
      (A + D, w * u)
      (0, (A + D - w) * v)
      (A, D * v) := by

  unfold Collinear cross vec
  dsimp

  calc
    (0 - (A + D)) *
          (D * v - w * u)
        -
        (((A + D - w) * v) - w * u) *
          (A - (A + D))
        =
      w * (A * u - D * v) := by
        ring

    _ = 0 := by
      rw [hrel]
      ring

/--
Version with an explicit side-sum identity.
-/
lemma fixed_point_collinear_of_sum
    (BC A D u v w : ℝ)
    (hsum :
      BC = A + D)
    (hrel :
      A * u = D * v) :
    Collinear
      (BC, w * u)
      (0, (BC - w) * v)
      (A, D * v) := by

  rw [hsum]

  exact
    fixed_point_collinear
      A
      D
      u
      v
      w
      hrel

/-!
## Law-of-Sines algebra
-/

/--
Cross-multiplication form of the Law of Sines.

If

    AC / sinB = AB / sinC

with nonzero denominators, then

    AC * sinC = AB * sinB.
-/
lemma sine_law_cross
    (AC AB sinB sinC : ℝ)
    (hsinB :
      sinB ≠ 0)
    (hsinC :
      sinC ≠ 0)
    (hsine :
      AC / sinB =
        AB / sinC) :
    AC * sinC =
      AB * sinB := by

  exact
    (div_eq_div_iff hsinB hsinC).mp
      hsine

/--
This is the cotangent relation needed by the source:

    (AC cosC) cotB =
    (AB cosB) cotC.

We encode

    cotB = cosB / sinB
    cotC = cosC / sinC.
-/
lemma sine_law_gives_cot_relation
    (AC AB sinB sinC cosB cosC : ℝ)
    (hsinB :
      sinB ≠ 0)
    (hsinC :
      sinC ≠ 0)
    (hsine :
      AC / sinB =
        AB / sinC) :
    (AC * cosC) * (cosB / sinB)
      =
    (AB * cosB) * (cosC / sinC) := by

  have hsine' :
      AC * sinC =
        AB * sinB := by

    exact
      sine_law_cross
        AC
        AB
        sinB
        sinC
        hsinB
        hsinC
        hsine

  calc
    (AC * cosC) * (cosB / sinB)
        =
      (AC * sinC * cosC * cosB) /
        (sinB * sinC) := by
          field_simp [hsinB, hsinC]

    _ =
      (AB * sinB * cosC * cosB) /
        (sinB * sinC) := by
          rw [hsine']

    _ =
      (AB * cosB) * (cosC / sinC) := by
          field_simp [hsinB, hsinC]

/-!
## Source-specific fixed-point theorem
-/

/--
Interpret

    ACcosC = |AC| cos C
    ABcosB = |AB| cos B
    cotB    = cot B
    cotC    = cot C.

If

    BC = ACcosC + ABcosB

and

    ACcosC * cotB =
      ABcosB * cotC,

then the source's points

    X = (BC, w*cotB)
    Y = (0, (BC-w)*cotC)

and

    H = (ACcosC, ABcosB*cotC)

are collinear.
-/
theorem imo2013_p4_complex_core
    (BC ACcosC ABcosB cotB cotC w : ℝ)
    (hside :
      BC = ACcosC + ABcosB)
    (htrig :
      ACcosC * cotB =
        ABcosB * cotC) :
    Collinear
      (BC, w * cotB)
      (0, (BC - w) * cotC)
      (ACcosC,
        ABcosB * cotC) := by

  exact
    fixed_point_collinear_of_sum
      BC
      ACcosC
      ABcosB
      cotB
      cotC
      w
      hside
      htrig

/-!
## Version deriving the cotangent relation from the Law of Sines
-/

/--
Expanded form corresponding closely to the source calculation.

Assume

    BC = AC*cosC + AB*cosB

and

    AC/sinB = AB/sinC.

Then the points

    X =
      (BC,
       w * cosB/sinB)

    Y =
      (0,
       (BC-w) * cosC/sinC)

    H =
      (AC*cosC,
       AB*cosB * cosC/sinC)

are collinear.
-/
theorem imo2013_p4_from_sine_law
    (BC AC AB sinB sinC cosB cosC w : ℝ)
    (hsinB :
      sinB ≠ 0)
    (hsinC :
      sinC ≠ 0)
    (hside :
      BC =
        AC * cosC +
        AB * cosB)
    (hsine :
      AC / sinB =
        AB / sinC) :
    Collinear
      (BC,
        w * (cosB / sinB))
      (0,
        (BC - w) *
          (cosC / sinC))
      (AC * cosC,
        (AB * cosB) *
          (cosC / sinC)) := by

  have htrig :
      (AC * cosC) *
          (cosB / sinB)
        =
      (AB * cosB) *
          (cosC / sinC) := by

    exact
      sine_law_gives_cot_relation
        AC
        AB
        sinB
        sinC
        cosB
        cosC
        hsinB
        hsinC
        hsine

  exact
    fixed_point_collinear_of_sum
      BC
      (AC * cosC)
      (AB * cosB)
      (cosB / sinB)
      (cosC / sinC)
      w
      hside
      htrig

/-!
## Explicit determinant factorization
-/

/--
The determinant in the final collinearity proof factors as

    w * (A*u - D*v).
-/
lemma determinant_factorization
    (A D u v w : ℝ) :
    (0 - (A + D)) *
          (D * v - w * u)
        -
        (((A + D - w) * v) - w * u) *
          (A - (A + D))
      =
    w * (A * u - D * v) := by

  ring

/-!
## Fixed point for the full one-parameter line family
-/

/--
For every parameter `w`, the line through

    X(w) = (A+D, w*u)

and

    Y(w) = (0, (A+D-w)*v)

passes through the same fixed point

    H = (A, D*v),

provided

    A*u = D*v.
-/
theorem fixed_point_on_all_lines
    (A D u v : ℝ)
    (hrel :
      A * u = D * v) :
    ∀ w : ℝ,
      Collinear
        (A + D, w * u)
        (0, (A + D - w) * v)
        (A, D * v) := by

  intro w

  exact
    fixed_point_collinear
      A
      D
      u
      v
      w
      hrel

/-!
## Fully expanded final theorem
-/
