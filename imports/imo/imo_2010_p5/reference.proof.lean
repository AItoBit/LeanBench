by

  open Reachable

-- Avoid deep kernel recursion in the giant exponent.
  set m : ℕ := 2010

  have hm :
      m = 2010 := by
    rfl

  convert!
    ((quarter_target hm).push
      (show (3 : Fin 6) < 5 by decide)).push
      (show (4 : Fin 6) < 5 by decide)

  simp only [
    Pi.single_eq_same,
    tsub_self,
    Fin.reduceAdd,
    zero_add,
    Pi.single_inj
  ]

  rw [
    ← mul_assoc,
    show 2 * 2 = 4 by rfl,
    mul_comm,
    Nat.div_mul_cancel
  ]

  trans 2010 ^ 2

  · lia

  · apply pow_dvd_pow

    trans 2010 ^ 1

    · lia

    · gcongr <;> lia
