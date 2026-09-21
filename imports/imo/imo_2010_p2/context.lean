namespace IMO2010P2

variable
    {P : Type*}
    [AddCommGroup P]
    [Module ℝ P]

/-! ## Lines -/

/--
`X` lies on the affine line through `A` and `B`.
-/
def OnLine (A B X : P) : Prop :=
  ∃ t : ℝ, X = A + t • (B - A)

/--
For the final incidence argument we only need the set of points
belonging to the circumcircle.
-/
structure CircleData (P : Type*) where
  carrier : Set P

/--
A point belongs to the circle.
-/
def OnCircle
    (Γ : CircleData P)
    (X : P) :
    Prop :=
  X ∈ Γ.carrier

/-! ## Unique intersection -/

/--
Lines `AB` and `CD` have at most one common point.

This is exactly the uniqueness property needed in the final step.
-/
def UniqueIntersection
    (A B C D : P) :
    Prop :=
  ∀ X Y : P,
    OnLine A B X →
    OnLine C D X →
    OnLine A B Y →
    OnLine C D Y →
    X = Y
