/-- 
Identity required for the forward direction (QE = QF ⟹ OQ ⟂ EF).
This reduces the perpendicularity dot product into an exact combination of the 
distance difference, the cross product (collinearity), and the circumcenter condition.
-/
lemma imo1994_p2_id_fwd (a b q s t y_o : ℝ) :
  2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o) =
  ((-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2)) *
    ( ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 - a^2 * s^2 * (a^2 + b^2) )
  + ((-b*(1-s) - q) * (a*t) - (a*s) * (b*(1-t) - q)) *
    ((-b*(1-s) - q) * (a*t) + (a*s) * (b*(1-t) - q)) * (a^2 + b^2)
  - 2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * (t-s) * (b^2 + a*y_o) := by ring

/-- 
Identity required for the backward direction (OQ ⟂ EF ⟹ QE = QF).
This relates the scaled distance difference back to the perpendicularity condition 
while absorbing the collinearity and circumcenter relations.
-/
lemma imo1994_p2_id_bwd (a b q s t y_o : ℝ) :
  (2 * a * b^2 * (1-s) * (1-t)) * ((-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2)) =
  ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o) *
    ( a * (s-t)^2 * (a^2+b^2) + 2 * (2 * a * b^2 * (1-s) * (1-t)) )
  - ((-b*(1-s) - q) * (a*t) - (a*s) * (b*(1-t) - q)) *
    ( b * (2-s-t) * (s-t) * (a^2+b^2) )
  + (b^2 + a*y_o) *
    ( 2 * (2 * a * b^2 * (1-s) * (1-t)) * (t-s) - a * (s-t)^3 * (a^2+b^2) ) := by ring
