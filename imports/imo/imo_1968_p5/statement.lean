/-- **IMO 1969, Problem 5.** Given `n > 4` points in the plane, no three collinear, there are at
least `(n-3).choose 2 = (n-3)(n-4)/2` four-element subsets in convex position, i.e. convex
quadrilaterals with vertices among the given points. -/
theorem candidate (S : Finset Pt) (hcard : 4 < S.card) (hgen : NoThreeCollinear S) :
    (S.card - 3).choose 2 ≤ ((S.powersetCard 4).filter InConvexPosition).card :=
