/--
`CanPlace` represents the existence of a frog placement
satisfying Geoff's condition.

For even `n`, if any successful placement would force
`Even (n-1)`, then no successful placement exists.
-/
theorem candidate
    {n : ℕ}
    (hn : 2 ≤ n)
    (CanPlace : Prop)
    (hEvenNecessary :
      Even n →
      CanPlace →
      Even (n - 1)) :
    Even n →
    ¬ CanPlace :=
