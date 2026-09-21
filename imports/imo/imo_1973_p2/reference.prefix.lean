set_option maxRecDepth 100000

namespace Imo1973P2

open Finset

/-- Points of space, with integer coordinates. -/
abbrev Pt := ℤ × ℤ × ℤ

/-- Difference of two points. -/
def sub (A B : Pt) : Pt := (A.1 - B.1, A.2.1 - B.2.1, A.2.2 - B.2.2)

/-- Cross product; it vanishes exactly on parallel pairs. -/
def cross (u v : Pt) : Pt :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

/-- Determinant of three vectors; it vanishes exactly when they are coplanar. -/
def det (u v w : Pt) : ℤ :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1)
    - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1)
    + u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- The `3 × 3 × 3` grid `{-1, 0, 1}³`. -/
def M : Finset Pt :=
  ({-1, 0, 1} : Finset ℤ) ×ˢ (({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ))

/-- The shift `±1` that keeps both `a` and `b` inside `{-1, 0, 1}`, when
`|a - b| ≤ 1`. -/
def sh (a b : ℤ) : ℤ := if a ≤ 0 ∧ b ≤ 0 then 1 else -1

/-- The explicit choice of the second pair `(C, D)` for a given pair `(A, B)`. -/
def wit (A B : Pt) : Pt × Pt :=
  if A.1 = B.1 then
    ((A.1 + sh A.1 B.1, A.2.1, A.2.2), (B.1 + sh A.1 B.1, B.2.1, B.2.2))
  else if A.2.1 = B.2.1 then
    ((A.1, A.2.1 + sh A.2.1 B.2.1, A.2.2), (B.1, B.2.1 + sh A.2.1 B.2.1, B.2.2))
  else if A.2.2 = B.2.2 then
    ((A.1, A.2.1, A.2.2 + sh A.2.2 B.2.2), (B.1, B.2.1, B.2.2 + sh A.2.2 B.2.2))
  else if A.1 - B.1 = 1 ∨ B.1 - A.1 = 1 then
    ((A.1 + sh A.1 B.1, A.2.1, A.2.2), (B.1 + sh A.1 B.1, B.2.1, B.2.2))
  else if A.2.1 - B.2.1 = 1 ∨ B.2.1 - A.2.1 = 1 then
    ((A.1, A.2.1 + sh A.2.1 B.2.1, A.2.2), (B.1, B.2.1 + sh A.2.1 B.2.1, B.2.2))
  else if A.2.2 - B.2.2 = 1 ∨ B.2.2 - A.2.2 = 1 then
    ((A.1, A.2.1, A.2.2 + sh A.2.2 B.2.2), (B.1, B.2.1, B.2.2 + sh A.2.2 B.2.2))
  else
    ((-A.1, 0, 0), (0, A.2.1, A.2.2))

/-- The whole verification, as a finite check over the `27 × 27` pairs. -/
private lemma wit_spec : ∀ A ∈ M, ∀ B ∈ M, A ≠ B →
    (wit A B).1 ∈ M ∧ (wit A B).2 ∈ M ∧ (wit A B).1 ≠ (wit A B).2 ∧
      cross (sub B A) (sub (wit A B).2 (wit A B).1) = (0, 0, 0) ∧
      cross (sub (wit A B).1 A) (sub B A) ≠ (0, 0, 0) := by
  decide
