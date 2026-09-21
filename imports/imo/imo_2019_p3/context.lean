namespace IMO2019P3

/-!
# IMO 2019 Problem 3 — termination / graph-reduction core

The source solution uses the following structure.

1. The initial friendship graph is connected.
2. Every legal event decreases the number of edges.
3. While the graph contains a cycle, one can perform an event
   that preserves connectedness.
4. When no cycles remain, the graph is a tree/forest.
5. In a forest, whenever some vertex has degree at least two,
   another legal event can be performed and the result is still
   a forest.
6. Since every event decreases the number of edges, both
   procedures terminate.
7. The final forest has maximum degree at most one.

This file formalizes that complete descent argument.

The local graph-theoretic existence statements in steps 3
and 5 are explicit hypotheses. This avoids pretending that
Mathlib automatically supplies the synthetic graph surgery
used in the olympiad solution.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
============================================================
1. Reflexive-transitive closure of a sequence of events
============================================================
-/

inductive Reach
    {State : Type*}
    (Step : State → State → Prop) :
    State → State → Prop

  | refl
      (s : State) :
      Reach Step s s

  | tail
      {a b c : State}
      (hab : Reach Step a b)
      (hbc : Step b c) :
      Reach Step a c

/-!
If `a` reaches `b` and `b` reaches `c`, then `a` reaches `c`.
-/
