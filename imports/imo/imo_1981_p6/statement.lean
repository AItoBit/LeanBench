/-- **IMO 1981, Problem 6.** For the Ackermann-type function `f`,
`f 4 1981 = 2^2^⋯^2 - 3`, a tower of 1984 twos minus 3. -/
theorem candidate : f 4 1981 = tower 1984 - 3 :=
