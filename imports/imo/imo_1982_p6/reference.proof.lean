by
  constructor
  · have t : dist (A j) (A k) ≤ dist (A j) Z + dist Z (A k) := dist_triangle _ _ _
    have e : dist Z (A k) = dist (A k) Z := dist_comm _ _
    linarith
  · have h1 : 99 ≤ dist (A j) (A m) := far hXZ hB hZB
    have h2 : 99 ≤ dist (A k) (A m) := far hYZ hB hZB
    have h2' : 99 ≤ dist (A m) (A k) := by rwa [dist_comm] at h2
    have h3 := dist_le_plen A hjm
    have h4 := dist_le_plen A hmk
    have h5 := plen_add A hjm hmk
    linarith
