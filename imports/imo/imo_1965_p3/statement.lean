/-- **IMO 1965, Problem 3.**
    For any tetrahedron of volume `V > 0`, the ratio of the volume of the piece
    containing edge `AB` to the volume of the piece containing edge `CD` is
    `k² (k + 3) / (3k + 1)`. -/
theorem candidate {k : ℝ} (hk : 0 < k) {V : ℝ} (hV : 0 < V) :
    volLower k V / volUpper k V = k ^ 2 * (k + 3) / (3 * k + 1) :=
