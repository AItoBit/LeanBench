/--
**IMO 2010 Problem 5.**

Yes: the target state is reachable.
-/
theorem candidate :
    Reachable
      (Pi.single
        (5 : Fin 6)
        (2010 ^ 2010 ^ 2010)) :=
