namespace Imo2006P1

open EuclideanGeometry Module Real

open scoped Affine

section Oriented

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
  [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-! ### Generic lemmas on oriented and unoriented angles -/
