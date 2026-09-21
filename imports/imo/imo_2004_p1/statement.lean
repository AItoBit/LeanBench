/-- **IMO 2004 P1.** -/
theorem candidate
    (u v b c k s t' t m1 m2 n1 n2 r1 r2 : ℝ)
    (hv : 0 < v)                                    -- `A` is off the line `BC`
    (hu : u ≠ 0)                                    -- `AB ≠ AC`
    (hb : 0 < b) (hc : 0 < c)
    (hbsq : b ^ 2 = (u + 1) ^ 2 + v ^ 2)            -- `b = AC`
    (hcsq : c ^ 2 = (u - 1) ^ 2 + v ^ 2)            -- `c = AB`
    (hP : 0 < u ^ 2 + v ^ 2 - 1)                    -- the angle at `A` is acute
    (hk : k * (b + c) = b - c)                      -- `K` is the foot of the `A`-bisector
    -- `M` lies on `AB`, and `CM ⊥ AB`
    (hm1 : m1 = u + s * (1 - u)) (hm2 : m2 = v - s * v)
    (hMperp : (m1 - (-1)) * (1 - u) + (m2 - 0) * (0 - v) = 0)
    -- `N` lies on `AC`, and `BN ⊥ AC`
    (hn1 : n1 = u + t' * (-1 - u)) (hn2 : n2 = v - t' * v)
    (hNperp : (n1 - 1) * (-1 - u) + (n2 - 0) * (0 - v) = 0)
    -- `R` lies on `AK` and is equidistant from `M` and `N`
    (hr1 : r1 = u + t * (k - u)) (hr2 : r2 = v - t * v)
    (hReq : (r1 - m1) ^ 2 + (r2 - m2) ^ 2 = (r1 - n1) ^ 2 + (r2 - n2) ^ 2) :
    cyc 1 0 m1 m2 r1 r2 k 0 = 0 ∧ cyc (-1) 0 n1 n2 r1 r2 k 0 = 0 ∧ -1 < k ∧ k < 1 :=
