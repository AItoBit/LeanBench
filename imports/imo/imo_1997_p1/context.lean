namespace Imo1997P1

/-- A point of the plane is black when the unit square containing it is. -/
def IsBlack (p : ℝ × ℝ) : Prop := Even (⌊p.1⌋ + ⌊p.2⌋)
