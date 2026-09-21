namespace IMO2019P2

/-!
# IMO 2019 Problem 2 — angle/cyclicity core

The supplied solution constructs an auxiliary circle `ω`
through

    P, Q, A0, B0,

then proves that both

    P1 ∈ ω
    Q1 ∈ ω.

Therefore

    P, Q, P1, Q1

are concyclic.

This file formalizes that logical angle/cyclicity structure.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract geometric objects
============================================================
-/

variable {Point Circle : Type*}

/-
`ang A B C` represents the directed angle ∠ABC.

It is kept abstract here because the supplied proof only uses
equalities between directed angles.
-/

variable (ang : Point → Point → Point → ℝ)

/-
`OnCircle ω P` means that point `P` lies on circle `ω`.
-/

variable (OnCircle : Circle → Point → Prop)

/--
Four points are concyclic if some circle contains all four.
-/
def Concyclic
    (OnCircle : Circle → Point → Prop)
    (A B C D : Point) : Prop :=
  ∃ ω : Circle,
    OnCircle ω A ∧
    OnCircle ω B ∧
    OnCircle ω C ∧
    OnCircle ω D

/-!
============================================================
2. Basic circle packaging
============================================================
-/
