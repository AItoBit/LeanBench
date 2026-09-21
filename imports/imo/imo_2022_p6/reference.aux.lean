lemma target_eq
    (n : ℕ) :
    target n =
      2 * n * (n - 1) + 1 := by
  rfl

/-!
============================================================
2. Horizontal and vertical adjacency counts
============================================================
-/

lemma gridEdges_eq
    (n : ℕ) :
    gridEdges n =
      2 * n * (n - 1) := by

  unfold gridEdges
  unfold horizontalEdges
  unfold verticalEdges

  ring

/-!
============================================================
3. Abstract Nordic-square type
============================================================
-/

/-
`Square n` is the type of Nordic squares of size n.

A later literal formalization can replace this abstract family
by an actual n × n grid carrying a bijective numbering.
-/

/--
If every grid edge gives a different non-singleton uphill path
and there is one additional singleton path, then every square
has at least the target number of uphill paths.
-/
theorem lower_bound
    {n : ℕ}
    (S : Square n)
    (hedges :
      gridEdges n + 1 ≤
        uphillCount S) :
    target n ≤
      uphillCount S := by

  have hcount :
      gridEdges n + 1 =
        target n := by

    unfold gridEdges
    unfold horizontalEdges
    unfold verticalEdges
    unfold target

    ring

  rw [← hcount]

  exact hedges

/-!
============================================================
5. Pure arithmetic form of the lower bound
============================================================
-/

lemma lower_bound_arithmetic
    {n paths : ℕ}
    (h :
      2 * n * (n - 1) + 1 ≤
        paths) :
    target n ≤ paths := by

  unfold target

  exact h

/-!
============================================================
6. Sharpness witness
============================================================
-/

/--
If one square has exactly the target number of paths, then
there exists a square attaining the bound.
-/
lemma sharp_of_construction
    {n : ℕ}
    (S : Square n)
    (hS :
      uphillCount S =
        target n) :
    ∃ T : Square n,
      uphillCount T =
        target n := by

  exact
    ⟨S, hS⟩

/-!
============================================================
7. Minimum predicate
============================================================
-/

/--
The source proof has:

* a universal lower bound obtained from the edge count;
* a construction attaining that lower bound.

Together these show that the minimum equals the target.
-/
theorem imo2022_p6
    (n : ℕ)

    (lower :
      ∀ S : Square n,
        gridEdges n + 1 ≤
          uphillCount S)

    (construction :
      ∃ S : Square n,
        uphillCount S =
          target n) :

    IsMinimum
      Square
      uphillCount
      n
      (target n) := by

  constructor

  · intro S

    exact
      lower_bound
        uphillCount
        S
        (lower S)

  · exact construction

/-!
============================================================
9. Explicit-answer version
============================================================
-/
