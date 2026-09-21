namespace IMO2021P4

variable {Point : Type*}

variable (d : Point → Point → ℝ)

/-!
============================================================
1. Symmetry helpers
============================================================
-/

abbrev EPoint :=
  EuclideanSpace ℝ (Fin 2)
