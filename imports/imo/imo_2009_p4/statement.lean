/--
From

    sin(3x - 45°) = 0  or  sin(2x - 45°) = 0

the source, using `0 < x < 45`, obtains the two linear equations below.
Once those bounded-zero conclusions are available, Lean closes the
olympiad result purely arithmetically.
-/
theorem candidate
    (x angleCAB : ℝ)
    (hbisector :
      angleCAB = 4 * x)
    (hzero :
      3 * x = 45 ∨
      2 * x = 45) :
    angleCAB = 60 ∨ angleCAB = 90 :=
