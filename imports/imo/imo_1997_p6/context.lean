namespace BinaryPartition

/-- The binary partition function, defined by its recurrence:
`f 0 = 1`, `f (2m+1) = f (2m)` and `f (2m+2) = f (2m+1) + f (m+1)`. -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 1 then f n else f n + f ((n + 1) / 2)
decreasing_by all_goals omega
