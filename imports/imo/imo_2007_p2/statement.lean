/--
IMO 2007 P2: AF is the internal bisector of angle DAB.

* `hpar` and `hnd` say ABCD is a nondegenerate parallelogram.
* `hcyclic` places B,C,D,E on one circle.
* `hF` places F strictly inside DC.
* `hG` places G on the full line BC.
* `hline` places G on the full line through A and F.
* `hEF` and `hEG` express EF = EC and EG = EC.
-/
theorem candidate (A B C D E F G : Plane)
    (hpar : C = B + D - A)
    (hnd : LinearIndependent ℝ ![B - A, D - A])
    (hcyclic : ∃ O : Plane, ∃ R : ℝ,
      dist B O = R ∧ dist C O = R ∧ dist D O = R ∧ dist E O = R)
    (hF : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F = D + t • (C - D))
    (hG : ∃ s : ℝ, G = B + s • (C - B))
    (hline : ∃ k : ℝ, G - A = k • (F - A))
    (hEF : dist E F = dist E C)
    (hEG : dist E G = dist E C) :
    EuclideanGeometry.angle D A F = EuclideanGeometry.angle F A B :=
