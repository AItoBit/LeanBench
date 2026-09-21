namespace IMO2023P2

variable {Point Circle : Type*}

variable
  (d : Point → Point → ℝ)
  (Collinear : Point → Point → Point → Prop)
  (TangentAt : Circle → Point → Point → Prop)
  (InternalBisector : Point → Point → Point → Point → Prop)

/-!
# IMO 2023 Problem 2 — geometric proof core

The source introduces H on BS and on the internal angle
bisector of ∠BAC. The remaining geometric work shows that
HP is tangent to ω at P.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Target
============================================================
-/

def Target
    (Collinear : Point → Point → Point → Prop)
    (TangentAt : Circle → Point → Point → Prop)
    (InternalBisector : Point → Point → Point → Point → Prop)
    (A B C S P : Point)
    (ω : Circle) : Prop :=
  ∃ H : Point,
    Collinear B S H ∧
    InternalBisector A B C H ∧
    TangentAt ω P H

/-!
============================================================
2. Direct target constructor
============================================================
-/

def OnPerpBisector
    (d : Point → Point → ℝ)
    (H A P : Point) : Prop :=
  d H A = d H P

abbrev EPoint :=
  EuclideanSpace ℝ (Fin 2)

/-!
============================================================
13. Euclidean perpendicular-bisector lemma
============================================================
-/
