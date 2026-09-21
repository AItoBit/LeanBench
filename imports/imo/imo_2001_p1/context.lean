open Real EuclideanGeometry

open scoped EuclideanGeometry

namespace IMO2001P1

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E] [Fact (Module.finrank ℝ V = 2)]

/-- The orthogonal projection of A onto the line BC. -/
noncomputable def altitudeFoot (t : Affine.Triangle ℝ E) : E :=
  orthogonalProjection (line[ℝ, t.points 1, t.points 2]) (t.points 0)
