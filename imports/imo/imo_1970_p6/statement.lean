/--
Formalization of the logical core of the "Solution re-written" for IMO 1970 Problem 6. 

The rewritten solution notes a key abstraction: we do not actually need to compute 
the exact overcounting factor `k = C(n-3, 2)` ("...but we don't need this"). 
We only need to know that it is strictly positive, and that it uniformly scales 
both the total number of triangles `T` and the number of acute triangles `A` 
into the lists `L₁` and `L₂`.
-/
theorem candidate (A T L1 L2 k : ℕ)
    (hk_pos : 0 < k)
    (hL1 : L1 = k * T)
    (hL2 : L2 = k * A)
    (h_ratio : 10 * L2 ≤ 7 * L1) :
    10 * A ≤ 7 * T :=
