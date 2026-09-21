theorem zmod13 (x y : ZMod 13) (h : x ^ 4 + y ^ 4 = 0) : x = 0 ∧ y = 0 := by
  revert x y
  decide

theorem zmod37 (x y : ZMod 37) (h : x ^ 4 + y ^ 4 = 0) : x = 0 ∧ y = 0 := by
  revert x y
  decide
