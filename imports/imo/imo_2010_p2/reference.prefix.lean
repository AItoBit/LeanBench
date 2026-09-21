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
The first endpoint lies on its line.
-/
lemma left_mem_line
    (A B : P) :
    OnLine A B A := by
  refine ⟨0, ?_⟩
  simp [OnLine]

/--
The second endpoint lies on its line.
-/
lemma right_mem_line
    (A B : P) :
    OnLine A B B := by
  refine ⟨1, ?_⟩
  simp [OnLine]

/--
Reversing the endpoints does not change line membership.
-/
lemma onLine_comm
    {A B X : P}
    (h : OnLine A B X) :
    OnLine B A X := by

  rcases h with ⟨t, ht⟩

  refine ⟨1 - t, ?_⟩

  rw [ht]

  module

/--
The converse direction of `onLine_comm`.
-/
lemma onLine_comm_iff
    {A B X : P} :
    OnLine A B X ↔ OnLine B A X := by

  constructor

  · intro h
    exact onLine_comm h

  · intro h
    exact onLine_comm h

/-! ## Circle carrier -/

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

/--
If `J` and `X` both lie on both lines, uniqueness implies `X = J`.
-/
lemma intersection_eq_J
    {E I D G J X : P}
    (hunique :
      UniqueIntersection E I D G)
    (hJEI :
      OnLine E I J)
    (hJDG :
      OnLine D G J)
    (hXEI :
      OnLine E I X)
    (hXDG :
      OnLine D G X) :
    X = J := by

  exact
    hunique
      X
      J
      hXEI
      hXDG
      hJEI
      hJDG

/-! ## Final IMO incidence argument -/

/--
If `J`

* is on the circumcircle,
* is on line `EI`,
* is on line `DG`,

and `X` is the unique intersection of `EI` and `DG`,
then `X` is on the circumcircle.
-/
theorem imo2010_p2_final
    (Γ : CircleData P)
    (E I D G J X : P)
    (hunique :
      UniqueIntersection E I D G)
    (hJΓ :
      OnCircle Γ J)
    (hJEI :
      OnLine E I J)
    (hJDG :
      OnLine D G J)
    (hXEI :
      OnLine E I X)
    (hXDG :
      OnLine D G X) :
    OnCircle Γ X := by

  have hXJ :
      X = J := by
    exact
      intersection_eq_J
        hunique
        hJEI
        hJDG
        hXEI
        hXDG

  rw [hXJ]

  exact hJΓ
