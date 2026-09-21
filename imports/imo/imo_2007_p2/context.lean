namespace IMO2007P2

open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 1000000

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end InnerProduct

section Core

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end Core

abbrev Plane := EuclideanSpace ℝ (Fin 2)
