namespace IMO1991P4

/--
Represents the mathematical property required at each vertex of degree >= 2:
The greatest common divisor of its incident edge labels must equal 1.
-/

def ValidVertexLabeling (incident_labels : List ℕ) : Prop :=
  ∀ d : ℕ, (∀ x ∈ incident_labels, d ∣ x) → d = 1

/--
Both Solution 1 and Solution 2 rely on assigning consecutive integers
`n` and `n + 1` to adjacent edges around a vertex. This theorem fully
proves that this algorithmic step is sufficient to guarantee the GCD
condition for that vertex, regardless of what other edges are attached.
-/

theorem candidate (incident_labels : List ℕ) (n : ℕ)
    (hn : n ∈ incident_labels) (hsucc : n + 1 ∈ incident_labels) :
    ValidVertexLabeling incident_labels :=
