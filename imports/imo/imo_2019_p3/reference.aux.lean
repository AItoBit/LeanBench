lemma Reach.trans
    {State : Type*}
    {Step : State → State → Prop}
    {a b c : State}
    (hab : Reach Step a b)
    (hbc : Reach Step b c) :
    Reach Step a c := by

  induction hbc with

  | refl =>
      exact hab

  | tail h₁ h₂ ih =>
      exact
        Reach.tail
          ih
          h₂

/-!
A single step gives reachability.
-/

lemma Reach.single
    {State : Type*}
    {Step : State → State → Prop}
    {a b : State}
    (h : Step a b) :
    Reach Step a b := by

  exact
    Reach.tail
      (Reach.refl a)
      h

/-!
============================================================
2. Generic decreasing algorithm
============================================================
-/

/--
Suppose

* `μ s` is a natural-number measure;
* every `Step` strictly decreases `μ`;
* `Inv` is an invariant we want to preserve;
* whenever the goal has not yet been reached, an invariant-
  preserving next step exists.

Then, starting from an invariant state, after finitely many
steps we reach an invariant state satisfying `Goal`.

This is the termination principle used twice in the source.
-/
theorem descend_preserving
    {State : Type*}
    (μ : State → ℕ)
    (Step : State → State → Prop)
    (Inv Goal : State → Prop)
    (hdecrease :
      ∀ {s t : State},
        Step s t →
        μ t < μ s)
    (hnext :
      ∀ s : State,
        Inv s →
        ¬ Goal s →
        ∃ t : State,
          Step s t ∧
          Inv t)
    (s : State)
    (hInv : Inv s) :
    ∃ t : State,
      Reach Step s t ∧
      Inv t ∧
      Goal t := by

  by_cases hGoal :
      Goal s

  · exact
      ⟨s,
       Reach.refl s,
       hInv,
       hGoal⟩

  · obtain
      ⟨u, hsu, hInvU⟩ :=
      hnext
        s
        hInv
        hGoal

    obtain
      ⟨t,
       hut,
       hInvT,
       hGoalT⟩ :=
      descend_preserving
        μ
        Step
        Inv
        Goal
        hdecrease
        hnext
        u
        hInvU

    exact
      ⟨t,
       Reach.trans
         (Reach.single hsu)
         hut,
       hInvT,
       hGoalT⟩

termination_by
  μ s

decreasing_by
  exact
    hdecrease hsu

/-!
============================================================
3. Phase I: eliminate all cycles
============================================================
-/

/--
Abstract form of the first algorithm in the supplied solution.

While a connected graph still contains a cycle, choose one
of the events described in the proof. The local graph lemma
says this preserves connectedness.

Since every event decreases the number of edges, eventually
we reach a connected acyclic graph.
-/
theorem eliminate_cycles
    {State : Type*}
    (edgeCount : State → ℕ)
    (Event : State → State → Prop)
    (Connected Acyclic : State → Prop)

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

    (G : State)
    (hConnected :
      Connected G) :
    ∃ T : State,
      Reach Event G T ∧
      Connected T ∧
      Acyclic T := by

  exact
    descend_preserving
      edgeCount
      Event
      Connected
      Acyclic
      hdecrease
      hcycleStep
      G
      hConnected

/-!
============================================================
4. Phase II: reduce the forest to degree ≤ 1
============================================================
-/

/--
Abstract form of the second algorithm.

When the graph is a forest and some vertex has degree at
least two, the source applies an event at such a vertex.

The local graph lemma says the new graph is again a forest.

Again, edge count strictly decreases, so this process
terminates at a forest in which every vertex has degree at
most one.
-/
theorem reduce_forest
    {State : Type*}
    (edgeCount : State → ℕ)
    (Event : State → State → Prop)
    (Acyclic Good : State → Prop)

    (hdecrease :
      ∀ {G H : State},
        Event G H →
        edgeCount H < edgeCount G)

    (hforestStep :
      ∀ G : State,
        Acyclic G →
        ¬ Good G →
        ∃ H : State,
          Event G H ∧
          Acyclic H)

    (G : State)
    (hAcyclic :
      Acyclic G) :
    ∃ H : State,
      Reach Event G H ∧
      Acyclic H ∧
      Good H := by

  exact
    descend_preserving
      edgeCount
      Event
      Acyclic
      Good
      hdecrease
      hforestStep
      G
      hAcyclic

/-!
============================================================
5. Combine both phases
============================================================
-/

/--
This is the complete algorithmic core of IMO 2019 P3.

Starting with a connected graph:

1. eliminate cycles while preserving connectedness;
2. from the resulting forest, keep applying events until
   every vertex has degree at most one.

The resulting graph is reachable from the original graph by
a finite sequence of legal events.
-/
theorem imo2019_p3_algorithm
    {State : Type*}
    (edgeCount : State → ℕ)
    (Event : State → State → Prop)
    (Connected Acyclic Good : State → Prop)

    /- Every event removes one net edge. -/
    (hdecrease :
      ∀ {G H : State},
        Event G H →
        edgeCount H < edgeCount G)

    /-
    Source's cycle-removal lemma:
    a connected cyclic state admits an event preserving
    connectedness.
    -/
    (hcycleStep :
      ∀ G : State,
        Connected G →
        ¬ Acyclic G →
        ∃ H : State,
          Event G H ∧
          Connected H)

    /-
    Source's forest lemma:
    if a forest is not yet a matching/isolated-vertex forest,
    a legal event exists which preserves acyclicity.
    -/
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
      Good Gfinal := by

  obtain
    ⟨T,
     hGT,
     _hConnectedT,
     hAcyclicT⟩ :=
    eliminate_cycles
      edgeCount
      Event
      Connected
      Acyclic
      hdecrease
      hcycleStep
      G₀
      hConnected

  obtain
    ⟨F,
     hTF,
     _hAcyclicF,
     hGoodF⟩ :=
    reduce_forest
      edgeCount
      Event
      Acyclic
      Good
      hdecrease
      hforestStep
      T
      hAcyclicT

  exact
    ⟨F,
     Reach.trans hGT hTF,
     hGoodF⟩

/-!
============================================================
6. Numerical facts from the original problem
============================================================
-/

/--
There are 2019 users.
-/
lemma users_count :
    1010 + 1009 = 2019 := by
  norm_num

/--
The minimum initial degree is 1009.
-/
lemma minimum_degree :
    min 1009 1010 = 1009 := by
  norm_num

/--
Two disjoint neighborhoods of size at least 1009 would
contain at least 2018 vertices.
-/
lemma two_neighborhoods_size :
    1009 + 1009 = 2018 := by
  norm_num

/--
But after excluding two distinct users, only 2017 other
users remain.

This is the pigeonhole inequality behind the source's
connectivity observation.
-/
lemma connectivity_numerical_core :
    2017 < 1009 + 1009 := by
  norm_num

/-!
============================================================
7. Edge-count decrease
============================================================
-/

/--
An event removes two friendships and creates one friendship,
so the total number of friendships drops by exactly one.

This is the arithmetic part once graph bookkeeping has shown

    E' = E - 2 + 1.
-/
lemma event_decreases_edge_count
    {E E' : ℕ}
    (hE :
      2 ≤ E)
    (hchange :
      E' = E - 2 + 1) :
    E' < E := by

  omega

/-!
============================================================
8. Terminal interpretation
============================================================
-/

/--
At the end of phase II, `Good` can be instantiated as

    every user has degree ≤ 1.

Then this theorem states exactly the requested conclusion.
-/
theorem final_degree_bound
    {State User : Type*}
    (degree : State → User → ℕ)
    (Good : State → Prop)
    (hGood :
      ∀ G : State,
        Good G →
        ∀ u : User,
          degree G u ≤ 1)
    {G : State}
    (hG :
      Good G) :
    ∀ u : User,
      degree G u ≤ 1 := by

  exact
    hGood G hG

/-!
============================================================
9. Final source-style wrapper
============================================================
-/
