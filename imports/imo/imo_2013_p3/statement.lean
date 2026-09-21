/--
The exact numerical angle conclusion:

    ∠CAB = 90°.
-/
theorem candidate
    (angleCAB angleIcIaIb : ℝ)
    (h45 :
      angleIcIaIb = Real.pi / 4)
    (hrel :
      angleCAB =
        Real.pi - 2 * angleIcIaIb) :
    angleCAB = Real.pi / 2 :=
