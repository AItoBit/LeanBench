/--
Once the source's preceding circle/tangency calculations give
`RK = RL` and the angle-bisector condition, the desired equality
`KM = LM` follows.
-/
theorem candidate
    (R K L M : Point)
    (hRKRL :
      sqDist R K = sqDist R L)
    (hangle :
      dotAt R K M = dotAt R L M) :
    distance K M = distance L M :=
