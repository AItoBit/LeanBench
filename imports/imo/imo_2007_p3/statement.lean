/-- **IMO 2007, Problem 3.**  If the largest size of a clique among all the competitors is
even, then the competitors can be arranged into two rooms (a room `A` and its complement)
so that the largest size of a clique contained in one room equals the largest size of a
clique contained in the other. -/
theorem candidate (G : SimpleGraph V) (hEven : Even (cliqueSize G Finset.univ)) :
    ∃ A : Finset V, cliqueSize G A = cliqueSize G Aᶜ :=
