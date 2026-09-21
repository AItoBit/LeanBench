/--
A direct formulation matching the final sentence of the olympiad proof:

every common point of `EI` and `DG` lies on `Γ`, once the constructed
point `J` is known to lie on all three.
-/
theorem candidate
    (Γ : CircleData P)
    (E I D G J : P)
    (hunique :
      UniqueIntersection E I D G)
    (hJΓ :
      OnCircle Γ J)
    (hJEI :
      OnLine E I J)
    (hJDG :
      OnLine D G J) :
    ∀ X : P,
      OnLine E I X →
      OnLine D G X →
      OnCircle Γ X :=
