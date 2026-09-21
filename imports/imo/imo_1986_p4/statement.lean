theorem candidate (n : ℝ) (hn : n ≠ 0)
    (angle_YBZ angle_YXZ : ℝ)
    (h_YBZ : angle_YBZ = (n - 2) * Real.pi / n)
    (h_YXZ : angle_YXZ = 2 * Real.pi / n) :
    angle_YBZ + angle_YXZ = Real.pi :=
