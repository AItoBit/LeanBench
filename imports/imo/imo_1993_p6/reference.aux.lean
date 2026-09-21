/-- The previous lamp is never the current lamp, since n ≥ 2. -/
lemma prev_ne (i : Fin n) : prev hn i ≠ i := by
  intro hc
  -- Project the Fin n equality down to ℕ for omega to reason about
  have hc' : (prev hn i).val = i.val := congrArg Fin.val hc
  unfold prev at hc'
  split_ifs at hc' with h
  · -- Unwrap the Fin constructor so omega sees (n - 1) = i
    simp only [Fin.val_mk] at hc'
    omega
  · -- Unwrap the Fin constructor so omega sees (i - 1) = i
    simp only [Fin.val_mk] at hc'
    omega

/-- 
Crucial observation: the operation at step `i` is an involution 
(it is its own inverse). This rigorously proves the step is deterministic 
and perfectly reversible.
-/
theorem step_involutive (i : Fin n) (s : LampState n) :
    step hn i (step hn i s) = s := by
  ext j
  by_cases h : j = i
  · -- Replace j with i in the goal, without destroying i in the context
    rw [h]
    dsimp [step]
    simp only [ite_true]
    -- Because prev i ≠ i, the previous lamp's state isn't touched
    have h_prev : prev hn i = i ↔ False := iff_false_intro (prev_ne hn i)
    simp only [h_prev, ite_false]
    -- Verify the XOR toggling natively evaluates to the identity
    cases s i <;> cases s (prev hn i) <;> rfl
  · -- For all other lamps, they are untouched
    dsimp [step]
    have hj : j = i ↔ False := iff_false_intro h
    simp only [hj, ite_false]
