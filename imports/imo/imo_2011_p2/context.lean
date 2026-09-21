namespace IMO2011P2

/-!
## Discrete windmill model
-/

/--
`HalfTurnWindmill N` packages the discrete information needed from
the geometric windmill process.

* `pivot t` is the pivot at step `t`.
* `color t p` is the side-color of point `p` at step `t`.
* `period` is the number of transitions representing one half-turn.
* `color_change_pivot` says a color change can only occur at an
  old/new pivot.
* `half_turn_flip` says every color is reversed after one half-turn.
-/
structure HalfTurnWindmill (N : ℕ) where
  pivot : ℕ → Fin N
  color : ℕ → Fin N → Bool
  period : ℕ
  period_pos : 0 < period

  color_change_pivot :
    ∀ t p,
      color t p ≠ color (t + 1) p →
      p = pivot t ∨ p = pivot (t + 1)

  half_turn_flip :
    ∀ t p,
      color (t + period) p = !(color t p)

/-!
## Discrete sequence lemmas
-/

/--
`p` is a pivot infinitely often if it occurs after every time bound.
-/
def PivotsInfinitelyOften
    {N : ℕ}
    (W : HalfTurnWindmill N)
    (p : Fin N) : Prop :=
  ∀ B : ℕ,
    ∃ t : ℕ,
      B < t ∧
      W.pivot t = p
