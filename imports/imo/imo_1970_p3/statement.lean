open Real

/--
Formalization of the algebraic identity and bounding step from the solution in "image_9a3b4a.png".
For the term b_n = 2 - 2 / sqrt(a_n), we prove that if a_n > 1, then b_n < 2.
-/

theorem candidate (an : ℝ) (ha : an > 1) :
    2 - 2 / sqrt an < 2 :=
