namespace Imo2007P4

/-!
Formalization of the algebraic core of IMO 2007 Problem 4.
Proves that the areas of triangles RQL and RPK are equal given the
midpoint symmetry on the secant line and the similarity of the projected right triangles.
-/

theorem candidate
    (RQ QL RP PK QC PC sin_theta k x y : ℝ)
    (h_sim1 : QL = k * QC)
    (h_sim2 : PK = k * PC)
    (h_RQ : RQ = -x - (-y))
    (h_QC : QC = y - (-x))
    (h_RP : RP = x - (-y))
    (h_PC : PC = y - x) :
    (1 / 2 : ℝ) * RQ * QL * sin_theta = (1 / 2 : ℝ) * RP * PK * sin_theta :=
