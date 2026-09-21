namespace Imo1981P1

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram determinant of two vectors, `‖u‖²‖v‖² - ⟪u, v⟫²`. -/
noncomputable def gram (u v : V) : ℝ := ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2

/-- Twice the area of the triangle with vertices `A`, `B`, `C`. -/
noncomputable def areaDoubled (A B C : V) : ℝ := Real.sqrt (gram (B - A) (C - A))

/-! ### Basic properties of the Gram determinant -/
