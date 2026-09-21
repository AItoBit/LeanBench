namespace Imo1993P3

/-- A square, as a point of the integer lattice. -/
abbrev Pos := ℤ × ℤ

/-- The colour of a square. -/
def color (p : Pos) : ZMod 3 := ((p.1 + p.2 : ℤ) : ZMod 3)

/-- One jump: a piece at `p` hops over the piece at `p + d` into the empty square `p + 2d`. -/
def Move (S T : Finset Pos) : Prop :=
  ∃ p d : Pos, (d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) ∧
    p ∈ S ∧ (p.1 + d.1, p.2 + d.2) ∈ S ∧
    (p.1 + 2 * d.1, p.2 + 2 * d.2) ∉ S ∧
    T = insert (p.1 + 2 * d.1, p.2 + 2 * d.2)
      ((S.erase p).erase (p.1 + d.1, p.2 + d.2))

/-- Parity of the number of pieces of colour `c`. -/
def w (c : ZMod 3) (S : Finset Pos) : ZMod 2 := ∑ p ∈ S, (if color p = c then 1 else 0)

/-- The full `n × n` board. -/
def board (n : ℕ) : Finset Pos :=
  (Finset.range n ×ˢ Finset.range n).image (fun q : ℕ × ℕ => ((q.1 : ℤ), (q.2 : ℤ)))
