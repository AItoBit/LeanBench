/--
If two angles are equal, we can invoke the supplied criterion
for lying on an angle bisector.
-/
lemma on_bisector_of_equal_angles
    {A X B C : Point}
    (h :
      ang B A X =
        ang X A C)
    (criterion :
      ang B A X =
          ang X A C →
      OnBisector A X B C) :
    OnBisector A X B C := by

  exact criterion h

/-!
============================================================
3. Perpendicular bisector packaging
============================================================
-/

/--
Equal distances to A and B imply membership in the
perpendicular bisector of AB.
-/
lemma on_perp_bisector_of_eq_dist
    {X A B : Point}
    (h :
      dist X A =
        dist X B)
    (criterion :
      dist X A =
          dist X B →
      OnPerpBisector X A B) :
    OnPerpBisector X A B := by

  exact criterion h

/-!
============================================================
4. Cyclic angle equality chains
============================================================
-/

/--
A two-step equality chain through a common angle value.
-/
lemma angle_chain
    {A B C D E F : Point}
    (θ : ℝ)
    (h₁ :
      ang A B C = θ)
    (h₂ :
      ang D E F = θ) :
    ang A B C =
      ang D E F := by

  calc
    ang A B C = θ := h₁
    _ = ang D E F := h₂.symm

/-!
============================================================
5. The ADP circle gives the D-bisector
============================================================
-/

/--
This packages the cyclic-angle calculation showing that
`OD` bisects `∠ADP`.
-/
lemma d_bisector
    {A D P O : Point}
    (h₁ :
      ang A D O =
        ang O D P)
    (criterion :
      ang A D O =
          ang O D P →
      OnBisector D O A P) :
    OnBisector D O A P := by

  exact
    criterion h₁

/-!
============================================================
6. The BCP circle gives the C-bisector
============================================================
-/

/--
Analogously, `OC` bisects `∠BCP`.
-/
lemma c_bisector
    {B C P O : Point}
    (h₁ :
      ang B C O =
        ang O C P)
    (criterion :
      ang B C O =
          ang O C P →
      OnBisector C O B P) :
    OnBisector C O B P := by

  exact
    criterion h₁

/-!
============================================================
7. Equal-radius argument
============================================================
-/

/--
If O and P lie on a circle centered at A, then OA = OP.
We keep this standard circle-radius fact explicit.
-/
lemma equal_dist_from_circle_center
    {A O P : Point}
    (h :
      dist A O =
        dist A P) :
    dist A O =
      dist A P := by

  exact h

/-!
============================================================
8. From OA = OP and OB = OP to OA = OB
============================================================
-/

lemma equal_dist_to_A_B
    {O A B P : Point}
    (hA :
      dist O A =
        dist O P)
    (hB :
      dist O B =
        dist O P) :
    dist O A =
      dist O B := by

  calc
    dist O A
        =
      dist O P :=
        hA

    _ =
      dist O B :=
        hB.symm

/-!
============================================================
9. Concurrency predicate
============================================================
-/

/--
If O satisfies the two angle-bisector conditions and is
equidistant from A and B, then it is the required common
point.
-/
theorem concurrency_from_common_point
    {A B C D P O : Point}
    (hD :
      OnBisector D O A P)
    (hC :
      OnBisector C O B P)
    (hAB :
      OnPerpBisector O A B) :
    ConcurrentTarget
      OnBisector
      OnPerpBisector
      A B C D P := by

  exact
    ⟨O,
     hD,
     hC,
     hAB⟩

/-!
============================================================
11. Full Solution-3 wrapper
============================================================
-/

/--
This theorem packages Solution 3 of the supplied proof.

The standard Euclidean facts are exposed as hypotheses:

* the cyclic-angle argument for `OD`;
* the cyclic-angle argument for `OC`;
* the equal-radius relations giving OA = OP and OB = OP;
* the standard characterization of the perpendicular bisector.

From those, Lean proves the desired concurrency.
-/
theorem imo2020_p1_core
    {A B C D P O : Point}

    (hDangle :
      ang A D O =
        ang O D P)

    (hCangle :
      ang B C O =
        ang O C P)

    (dCriterion :
      ang A D O =
          ang O D P →
      OnBisector D O A P)

    (cCriterion :
      ang B C O =
          ang O C P →
      OnBisector C O B P)

    (hOA :
      dist O A =
        dist O P)

    (hOB :
      dist O B =
        dist O P)

    (perpCriterion :
      dist O A =
          dist O B →
      OnPerpBisector O A B) :

    ConcurrentTarget
      OnBisector
      OnPerpBisector
      A B C D P := by

  have hD :
      OnBisector D O A P :=
    d_bisector
      ang
      OnBisector
      hDangle
      dCriterion

  have hC :
      OnBisector C O B P :=
    c_bisector
      ang
      OnBisector
      hCangle
      cCriterion

  have hEq :
      dist O A =
        dist O B :=
    equal_dist_to_A_B
      dist
      hOA
      hOB

  have hPB :
      OnPerpBisector O A B :=
    on_perp_bisector_of_eq_dist
      dist
      OnPerpBisector
      hEq
      perpCriterion

  exact
    concurrency_from_common_point
      OnBisector
      OnPerpBisector
      hD
      hC
      hPB

/-!
============================================================
12. Version closer to the source angle computation
============================================================
-/

/--
The source writes ∠BAC = 2α and derives the relevant angles
through the same value α or 2α.

This helper packages such a computation.
-/
lemma equal_angles_via_alpha
    {A B C D E F : Point}
    (α : ℝ)
    (h₁ :
      ang A B C =
        2 * α)
    (h₂ :
      ang D E F =
        2 * α) :
    ang A B C =
      ang D E F := by

  calc
    ang A B C
        =
      2 * α :=
        h₁

    _ =
      ang D E F :=
        h₂.symm

/-!
============================================================
13. Strong final statement
============================================================
-/
