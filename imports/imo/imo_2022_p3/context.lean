namespace IMO2022P4

variable {Point : Type*}

variable
  (ang : Point → Point → Point → ℝ)
  (dist : Point → Point → ℝ)

variable
  (Concyclic : Point → Point → Point → Point → Prop)

/-!
============================================================
1. Equality-chain helpers
============================================================
-/
