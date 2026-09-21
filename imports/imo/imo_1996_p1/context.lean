set_option maxHeartbeats 1000000

namespace Imo1996P1

abbrev Pos := ℤ × ℤ

/-- The centre of a square of the board. -/
def OnBoard (p : Pos) : Prop := 1 ≤ p.1 ∧ p.1 ≤ 20 ∧ 1 ≤ p.2 ∧ p.2 ≤ 12

/-- A legal move for the parameter `r`. -/
def Move (r : ℤ) (p q : Pos) : Prop :=
  OnBoard p ∧ OnBoard q ∧
    (q.1 - p.1) * (q.1 - p.1) + (q.2 - p.2) * (q.2 - p.2) = r

/-- Reachability by legal moves. -/
def Reach (r : ℤ) : Pos → Pos → Prop := Relation.ReflTransGen (Move r)

/-- Parity of the horizontal band `1–4`, `5–8`, `9–12`. -/
def blk (y : ℤ) : ZMod 2 := if y ≤ 4 then 1 else if y ≤ 8 then 0 else 1

/-- The invariant for `r = 97`. -/
def inv97 (p : Pos) : ZMod 2 := ((p.1 : ℤ) : ZMod 2) + blk p.2
