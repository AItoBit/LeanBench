open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option pp.fullNames true

set_option pp.structureInstances true

set_option pp.coercions.types true

set_option pp.funBinderTypes true

set_option pp.letVarTypes true

set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# IMO 1974, Problem 4

Consider decompositions of an `8 × 8` chessboard into `p` non-overlapping rectangles subject to
the following conditions:

* (i) each rectangle has as many white squares as black squares;
* (ii) if `a i` is the number of white squares in the `i`-th rectangle, then
  `a 1 < a 2 < ⋯ < a p`.

Find the maximum value of `p` for which such a decomposition is possible.  For this value of `p`,
determine all possible sequences `a 1, a 2, …, a p`.

The answer is `p = 7`, and the possible sequences are

`1,2,3,4,5,7,10`,  `1,2,3,4,5,8,9`,  `1,2,3,4,6,7,9`,  `1,2,3,5,6,7,8`.
-/

namespace Imo1974P4

/-- An axis-parallel rectangle of cells, consisting of the cells `(r, c)` with
`r1 ≤ r < r2` and `c1 ≤ c < c2`. -/
structure Rect where
  r1 : ℕ
  r2 : ℕ
  c1 : ℕ
  c2 : ℕ

deriving DecidableEq

/-- The set of cells of a rectangle. -/
def Rect.cells (R : Rect) : Finset (ℕ × ℕ) := Finset.Ico R.r1 R.r2 ×ˢ Finset.Ico R.c1 R.c2

/-- The cells of the `8 × 8` chessboard. -/
def board : Finset (ℕ × ℕ) := Finset.range 8 ×ˢ Finset.range 8

/-- The number of white cells of a rectangle; a cell `(r, c)` is white when `r + c` is even. -/
def whiteCount (R : Rect) : ℕ := (R.cells.filter (fun q => (q.1 + q.2) % 2 = 0)).card

/-- The number of black cells of a rectangle; a cell `(r, c)` is black when `r + c` is odd. -/
def blackCount (R : Rect) : ℕ := (R.cells.filter (fun q => (q.1 + q.2) % 2 = 1)).card

/-- `R` is a decomposition of the chessboard into `p` non-empty, non-overlapping rectangles. -/
def IsDecomposition {p : ℕ} (R : Fin p → Rect) : Prop :=
  (∀ i, (R i).cells.Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (R i).cells (R j).cells) ∧
  Finset.univ.biUnion (fun i => (R i).cells) = board

/-- A decomposition of the chessboard satisfying conditions (i) and (ii) of the problem. -/
def IsGood {p : ℕ} (R : Fin p → Rect) : Prop :=
  IsDecomposition R ∧
  (∀ i, whiteCount (R i) = blackCount (R i)) ∧
  StrictMono (fun i => whiteCount (R i))

/-- The four sequences claimed to be the possible ones. -/
def answerSeqs : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 7, 10], [1, 2, 3, 4, 5, 8, 9], [1, 2, 3, 4, 6, 7, 9], [1, 2, 3, 5, 6, 7, 8]]

/-! ### Basic counting lemmas -/

/-- A decomposition realizing the sequence `1, 2, 3, 4, 5, 7, 10`. -/
def tilingA : Fin 7 → Rect
  | 0 => ⟨5, 7, 0, 1⟩
  | 1 => ⟨5, 7, 1, 3⟩
  | 2 => ⟨5, 7, 3, 6⟩
  | 3 => ⟨7, 8, 0, 8⟩
  | 4 => ⟨0, 5, 4, 6⟩
  | 5 => ⟨0, 7, 6, 8⟩
  | 6 => ⟨0, 5, 0, 4⟩

/-- A decomposition realizing the sequence `1, 2, 3, 4, 5, 8, 9`. -/
def tilingB : Fin 7 → Rect
  | 0 => ⟨6, 8, 0, 1⟩
  | 1 => ⟨0, 4, 5, 6⟩
  | 2 => ⟨4, 6, 3, 6⟩
  | 3 => ⟨0, 4, 3, 5⟩
  | 4 => ⟨6, 8, 1, 6⟩
  | 5 => ⟨0, 8, 6, 8⟩
  | 6 => ⟨0, 6, 0, 3⟩

/-- A decomposition realizing the sequence `1, 2, 3, 4, 6, 7, 9`. -/
def tilingC : Fin 7 → Rect
  | 0 => ⟨7, 8, 6, 8⟩
  | 1 => ⟨0, 4, 5, 6⟩
  | 2 => ⟨4, 6, 3, 6⟩
  | 3 => ⟨0, 4, 3, 5⟩
  | 4 => ⟨6, 8, 0, 6⟩
  | 5 => ⟨0, 7, 6, 8⟩
  | 6 => ⟨0, 6, 0, 3⟩

/-- A decomposition realizing the sequence `1, 2, 3, 5, 6, 7, 8`. -/
def tilingD : Fin 7 → Rect
  | 0 => ⟨7, 8, 2, 4⟩
  | 1 => ⟨6, 8, 4, 6⟩
  | 2 => ⟨5, 8, 6, 8⟩
  | 3 => ⟨0, 5, 6, 8⟩
  | 4 => ⟨0, 6, 4, 6⟩
  | 5 => ⟨0, 7, 2, 4⟩
  | 6 => ⟨0, 8, 0, 2⟩
