/--
Final concurrency theorem corresponding to the last step of
Solution 2 of IMO 2016 Problem 1.

If reflection in `ME` exchanges

    B ↔ X
    D ↔ F,

then `BD`, `FX`, and `ME` are concurrent.

The coordinate system is chosen so that `ME` is the y-axis.
-/
theorem candidate
    (B D F X : Point)
    (hB_X :
      X = reflectAxis B)
    (hD_F :
      F = reflectAxis D)
    (hBD :
      B.1 ≠ D.1) :
    ∃ P : Point,
      Collinear B D P ∧
      Collinear F X P ∧
      OnAxis P :=
