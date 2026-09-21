open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Pointwise

set_option maxHeartbeats 1000000

/-!
# IMO 1979 Problem 6

Let `A` and `E` be opposite vertices of an octagon.  A frog starts at vertex `A`.  From any
vertex except `E` it jumps to one of the two adjacent vertices.  When it reaches `E` it stops.
Let `aₙ` be the number of distinct paths of exactly `n` jumps ending at `E`.  Then

```
a_{2n-1} = 0,     a_{2n} = ((2 + √2)^(n-1) - (2 - √2)^(n-1)) / √2 .
```

We label the vertices of the octagon by `ZMod 8`, with `A = 0` and `E = 4`.  A path is encoded by
the list of its jumps: `true` means "jump to the next vertex", `false` means "jump to the previous
vertex".  A path is legal when it ends at `E` and never visits `E` earlier (the frog stops at `E`).
-/

namespace IMO1979P6

/-- One jump from vertex `X`: `true` moves to `X + 1`, `false` moves to `X - 1`. -/
def step (X : ZMod 8) (b : Bool) : ZMod 8 := if b then X + 1 else X - 1

/-- The vertex reached from `X` after performing the jumps in the list `s`. -/
def endsAt (X : ZMod 8) : List Bool → ZMod 8
  | [] => X
  | b :: t => endsAt (step X b) t

/-- `s` is a legal frog path starting at `X`: it ends at `E = 4` and it never visits `E`
before its last step (in particular the frog never jumps away from `E`). -/
def ValidPath (X : ZMod 8) (s : List Bool) : Prop :=
  endsAt X s = 4 ∧ ∀ k < s.length, endsAt X (s.take k) ≠ 4

instance (X : ZMod 8) : DecidablePred (ValidPath X) := fun s => by
  unfold ValidPath; infer_instance

/-- The finset of all lists of booleans of length `n`. -/
def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (boolLists n).image (List.cons true) ∪ (boolLists n).image (List.cons false)

/-- The number of legal frog paths of exactly `n` jumps starting at the vertex `X`. -/
def N (X : ZMod 8) (n : ℕ) : ℕ := ((boolLists n).filter (ValidPath X)).card

/-- `aₙ`: the number of distinct paths of exactly `n` jumps from `A = 0` ending at `E = 4`. -/
def a (n : ℕ) : ℕ := N 0 n

/-! ### Basic facts about `boolLists` -/

/-- The parity of a vertex. -/
private def par : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- `(pq n).1 = a_{2(n+1)}` and `(pq n).2 = N 2 (2(n+1)) = N 6 (2(n+1))`. -/
def pq : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (2 * (pq n).1 + 2 * (pq n).2, (pq n).1 + 2 * (pq n).2)
