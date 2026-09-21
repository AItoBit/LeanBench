open scoped RealInnerProductSpace

open Affine

namespace IncenterBarycentric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram determinant attached to an ordered triple of points; it is the square of twice the
area of the triangle they form. -/
noncomputable def gram (x y z : V) : ℝ := ‖y - x‖ ^ 2 * ‖z - x‖ ^ 2 - ⟪y - x, z - x⟫ ^ 2
