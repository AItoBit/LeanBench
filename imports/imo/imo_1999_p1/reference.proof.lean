by
  constructor
  · intro hsym
    exact regular_of_isSymmetric S hS hsym
  · rintro ⟨c, w, hw, hEq⟩
    exact isSymmetric_of_regular S hS hw hEq
