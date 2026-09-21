by

  have hparallel :
      Parallel L M A Q :=
    parallel_AQ_of_midpoints_rectangle
      hT
      hN
      hrect

  exact
    tangent_of_isosceles_and_parallel
      hcenter
      hLbisector
      hparallel

/-!
## Explicit dot-product form
-/
