namespace IMO1991P4

/--
Represents the mathematical property required at each vertex of degree >= 2:
The greatest common divisor of its incident edge labels must equal 1.
-/
def ValidVertexLabeling (incident_labels : List ℕ) : Prop :=
  ∀ d : ℕ, (∀ x ∈ incident_labels, d ∣ x) → d = 1
