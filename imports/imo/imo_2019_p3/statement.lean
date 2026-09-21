/--
Source-style final theorem.

Once the graph-specific local lemmas have been proved:

* every legal event decreases edge count;
* a cycle-removal event exists while a connected graph is
  cyclic;
* a forest-reduction event exists while some degree is > 1;

the required finite sequence of events exists.
-/
theorem candidate
    {State User : Type*}

    (edgeCount : State → ℕ)
    (degree : State → User → ℕ)

    (Event : State → State → Prop)

    (Connected Acyclic : State → Prop)

    (Good : State → Prop)

    (hGood :
      ∀ G : State,
        Good G →
        ∀ u : User,
          degree G u ≤ 1)

    (hdecrease :
      ∀ {G H : State},
        Event G H →
        edgeCount H < edgeCount G)

    (hcycleStep :
      ∀ G : State,
        Connected G →
        ¬ Acyclic G →
        ∃ H : State,
          Event G H ∧
          Connected H)

    (hforestStep :
      ∀ G : State,
        Acyclic G →
        ¬ Good G →
        ∃ H : State,
          Event G H ∧
          Acyclic H)

    (G₀ : State)
    (hConnected :
      Connected G₀) :
    ∃ Gfinal : State,
      Reach Event G₀ Gfinal ∧
      ∀ u : User,
        degree Gfinal u ≤ 1 :=
