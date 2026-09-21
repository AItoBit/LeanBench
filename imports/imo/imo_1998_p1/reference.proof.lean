by
  have h1 : 2*a*x - 2*b*y - a^2 + b^2 = 0 := by
    dsimp [sqDist] at hAB
    nlinarith
  have h2 : -2*c*x + 2*d*y - c^2 + d^2 = 0 := by
    dsimp [sqDist] at hCD
    nlinarith
  have harea :
      area (a,0) (0,b) (x,y) = area (-c,0) (0,-d) (x,y) ↔
      (b+d)*x + (a+c)*y - a*b + c*d = 0 := by
    rcases hinside with ⟨hpos1, _, hpos2, _⟩
    have e1 : (0-a)* (y-0) - (b-0)*(x-a) = a*b-b*x-a*y := by ring
    have e2 : (0- -c)*(y-0) - (-d-0)*(x- -c) = c*d+d*x+c*y := by ring
    change |(0-a)*(y-0)-(b-0)*(x-a)|/2 =
      |(0- -c)*(y-0)-(-d-0)*(x- -c)|/2 ↔ _
    rw [e1, e2, abs_of_pos hpos1, abs_of_pos hpos2]
    constructor <;> intro h <;> linarith
  rw [cyclic_iff a b c d ha hb hc hd, harea]
  have hid :
      (a*c-b*d)*((a+c)^2+(b+d)^2) =
      2*(a*d-b*c)*((b+d)*x+(a+c)*y-a*b+c*d) := by
    linear_combination
      -(d*(b+d)+c*(a+c))*h1 - (b*(b+d)+a*(a+c))*h2
  constructor
  · intro h
    have hz : 2*(a*d-b*c)*((b+d)*x+(a+c)*y-a*b+c*d) = 0 := by
      rw [h] at hid
      nlinarith [hid]
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hnotparallel)
  · intro h
    rw [h, mul_zero] at hid
    have hp : 0 < (a+c)^2+(b+d)^2 := by
      have hs := sq_pos_of_pos (add_pos ha hc)
      nlinarith [sq_nonneg (b+d)]
    have hz := (mul_eq_zero.mp hid).resolve_right (ne_of_gt hp)
    linarith
