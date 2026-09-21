by
  have key : ∀ T, Relation.ReflTransGen Move (board (3 * m)) T →
      ∃ k : ZMod 2, ∀ c, w c T = ((3 * m * m : ℕ) : ZMod 2) + k := by
    intro T hT
    induction hT with
    | refl => exact ⟨0, fun c => by rw [w_board]; ring⟩
    | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, fun c => by rw [w_move hstep c, hk c]; ring⟩
  obtain ⟨k, hk⟩ := key S h
  intro hcard
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 hcard
  have hw : ∀ c, w c ({p} : Finset Pos) = if color p = c then 1 else 0 := by
    intro c
    rw [w, Finset.sum_singleton]
  have heq01 : (if color p = (0 : ZMod 3) then (1 : ZMod 2) else 0)
      = (if color p = (1 : ZMod 3) then (1 : ZMod 2) else 0) := by
    rw [← hw, ← hw, hk 0, hk 1]
  have heq02 : (if color p = (0 : ZMod 3) then (1 : ZMod 2) else 0)
      = (if color p = (2 : ZMod 3) then (1 : ZMod 2) else 0) := by
    rw [← hw, ← hw, hk 0, hk 2]
  have hc3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hc3 (color p) with hc | hc | hc <;> rw [hc] at heq01 heq02 <;>
    revert heq01 heq02 <;> decide

/-!
### The other half

For `n` not divisible by `3` the game *can* be finished, but the proof is an explicit strategy:
a base construction for `n = 2` and `n = 4`, a routine for clearing three border rows that
reduces an `(r+3) × s` rectangle to an `r × s` one, and a routine for shortening a `2 × s`
rectangle by three. Formalizing it means exhibiting and verifying concrete move sequences by
induction on `n`, which is a separate and much larger development; it is not attempted here.
-/
