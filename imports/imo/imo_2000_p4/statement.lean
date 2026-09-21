/-- **IMO 2000 P4.** There are exactly `12` distributions for which the trick always works. -/
theorem candidate : Nat.card {f : Fin 100 → Fin 3 // Good f} = 12 :=
