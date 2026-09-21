namespace IMO2019P6

/-!
# IMO 2019 Problem 6 — inversion / angle core

The supplied solution proceeds through four main stages.

1. Construct an auxiliary point `S`, and reduce the original
   incidence statement to a circle-membership statement.

2. Prove that `Q, B, I, C` are concyclic.

3. After inversion in the incircle, prove that the midpoint
   `M` of `AD` belongs to an auxiliary circle `Ω`.

4. Prove that the image of `Q` also belongs to `Ω` using
   the angle chain

       ∠PQM = ∠PQC
            = ∠PEC
            = ∠PED
            = ∠PSD
            = ∠PSM.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
============================================================
1. Abstract geometric primitives
============================================================
-/

variable {Point Circle : Type*}

/-
`ang A B C` denotes a directed angle ∠ABC.
-/

variable (ang : Point → Point → Point → ℝ)

/-
Basic incidence predicates.
-/

variable
  (OnCircle : Circle → Point → Prop)
  (Collinear : Point → Point → Point → Prop)
  (Perpendicular : Point → Point → Point → Point → Prop)

/--
Four points are concyclic if they lie on one circle.
-/
def Concyclic
    (OnCircle : Circle → Point → Prop)
    (A B C D : Point) : Prop :=
  ∃ ω : Circle,
    OnCircle ω A ∧
    OnCircle ω B ∧
    OnCircle ω C ∧
    OnCircle ω D

/--
The original target:

the point X = DI ∩ PQ lies on the line through A
perpendicular to AI.
-/
def Target
    (Collinear :
      Point → Point → Point → Prop)
    (Perpendicular :
      Point → Point → Point → Point → Prop)
    (A I D P Q X : Point) : Prop :=
  Collinear D I X ∧
  Collinear P Q X ∧
  Perpendicular A X A I

/-!
============================================================
10. Reduction from Q ∈ Ω
============================================================
-/
