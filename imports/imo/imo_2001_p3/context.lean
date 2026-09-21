namespace IMO2001P3

open Finset

/-- The conditions on the problems the girls and boys solved, represented as functions from `Fin 21`
(index in cohort) to the finset of problems they solved (numbered arbitrarily). -/
structure Condition (G B : Fin 21 → Finset ℕ) where
  /-- Every girl solved at most six problems. -/
  G_le_6 (i) : #(G i) ≤ 6
  /-- Every boy solved at most six problems. -/
  B_le_6 (j) : #(B j) ≤ 6
  /-- Every girl-boy pair solved at least one problem in common. -/
  G_inter_B (i j) : ¬Disjoint (G i) (B j)

/-- A problem is easy for a cohort (boys or girls) if at least three of its members solved it. -/
def Easy (F : Fin 21 → Finset ℕ) (p : ℕ) : Prop := 3 ≤ #{i | p ∈ F i}

variable {G B : Fin 21 → Finset ℕ}
