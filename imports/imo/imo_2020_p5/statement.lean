/--
Once the source-specific prime-propagation step has been
proved, infinite descent forces every positive good deck to
have all entries equal.
-/
theorem candidate
    {State : Type*}
    (μ : State → ℕ)
    (PositiveState GoodState : State → Prop)
    (AllEqual : State → Prop)

    (hstep :
      ∀ s : State,
        PositiveState s →
        GoodState s →
        ¬ AllEqual s →
        ∃ t : State,
          PositiveState t ∧
          GoodState t ∧
          ¬ AllEqual t ∧
          μ t < μ s)

    (s : State)
    (hpos :
      PositiveState s)
    (hgood :
      GoodState s) :
    AllEqual s :=
