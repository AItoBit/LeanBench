namespace Imo1997P1

/-- A point of the plane is black when the unit square containing it is. -/
def IsBlack (p : ℝ × ℝ) : Prop := Even (⌊p.1⌋ + ⌊p.2⌋)

/-- Translating by an integer vector `(a, b)` preserves colours exactly when `a + b` is even. -/
theorem isBlack_add_int (p : ℝ × ℝ) (a b : ℤ) (hab : Even (a + b)) :
    IsBlack (p.1 + (a : ℝ), p.2 + (b : ℝ)) ↔ IsBlack p := by
  unfold IsBlack
  rw [Int.floor_add_intCast, Int.floor_add_intCast]
  obtain ⟨c, hc⟩ := hab
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d - c, by omega⟩
  · rintro ⟨d, hd⟩
    exact ⟨d + c, by omega⟩
