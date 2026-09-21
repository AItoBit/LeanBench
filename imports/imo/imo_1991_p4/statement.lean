/--
Both Solution 1 and Solution 2 rely on assigning consecutive integers
`n` and `n + 1` to adjacent edges around a vertex. This theorem fully
proves that this algorithmic step is sufficient to guarantee the GCD
condition for that vertex, regardless of what other edges are attached.
-/
theorem candidate (incident_labels : List ℕ) (n : ℕ)
    (hn : n ∈ incident_labels) (hsucc : n + 1 ∈ incident_labels) :
    ValidVertexLabeling incident_labels :=
