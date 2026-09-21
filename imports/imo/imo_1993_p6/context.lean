namespace IMO1993P6A

variable {n : ℕ} (hn : 2 ≤ n)

/-- We use `Fin n` to represent the lamps in a circle. 
    The state of the lamps is a function from `Fin n` to `Bool`. -/
abbrev LampState (n : ℕ) := Fin n → Bool

/-- The index of the previous lamp, wrapping around to n - 1 if i is 0. -/
def prev (i : Fin n) : Fin n :=
  if h : (i : ℕ) = 0 then ⟨n - 1, by omega⟩ else ⟨(i : ℕ) - 1, by omega⟩

/-- 
The state update at step `i`:
If the previous lamp is lit (true), we toggle the current lamp `i` via XOR.
Otherwise, we do nothing.
-/
def step (i : Fin n) (s : LampState n) : LampState n :=
  fun j => if j = i then xor (s i) (s (prev hn i)) else s j

/-- Each individual step is uniquely reversible, forming a bijection (permutation). -/
def stepEquiv (i : Fin n) : Equiv.Perm (LampState n) where
  toFun := step hn i
  invFun := step hn i
  left_inv s := step_involutive hn i s
  right_inv s := step_involutive hn i s

/-- 
A full round consists of applying the step operation sequentially 
for each lamp from 0 to n - 1. We construct this by folding over `Fin n`.
-/
def roundEquiv : Equiv.Perm (LampState n) :=
  (List.finRange n).foldr (fun i eq => eq.trans (stepEquiv hn i)) (Equiv.refl _)
