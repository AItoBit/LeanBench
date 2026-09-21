/-- **IMO 1978, Problem 6.**  An international society has members from six different
countries, the members being numbered `1, 2, …, 1978`.  Then some member's number is the
sum of the numbers of two (not necessarily distinct) members from his own country. -/
theorem candidate (c : ℕ → Fin 6) :
    ∃ x y z : ℕ, x ∈ Finset.Icc 1 1978 ∧ y ∈ Finset.Icc 1 1978 ∧ z ∈ Finset.Icc 1 1978 ∧
      x + y = z ∧ c x = c z ∧ c y = c z :=
