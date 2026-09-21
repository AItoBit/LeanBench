/-- **IMO 1989 P2, metric core.** -/
theorem candidate
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    excentralArea a b c r S = 2 * hexArea a b c r S ∧ 4 * S ≤ excentralArea a b c r S :=
