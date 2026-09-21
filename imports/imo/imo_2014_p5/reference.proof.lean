by

  have hlarge :
      (20000 : ℝ) / 201 <
        ∑ i : Fin 100, w i :=
    total_gt_20000_div_201
      w
      c
      hc
      hblocked

  have hcritical :
      (199 : ℝ) / 2 <
        (20000 : ℝ) / 201 :=
    critical_bound

  linarith

/-!
## Contrapositive: a light coin must fit somewhere
-/
