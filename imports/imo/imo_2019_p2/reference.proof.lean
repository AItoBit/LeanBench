by

  have hAuxAngle :
      ang Q P A0 =
        ang Q B0 A0 :=
    auxiliary_angle_chain
      ang
      δ
      hQPA0
      hQB0A0

  obtain
    ⟨ω,
     hP,
     hQ,
     hA0,
     hB0⟩ :=
    cyclic_of_equal_angle
      hAuxAngle

  have hP1Angle :
      ang P A0 B0 =
        ang P P1 B0 :=
    p1_angle_chain
      ang
      φ
      hPA0
      hPP1

  have hP1 :
      OnCircle ω P1 :=
    p1_membership
      ω
      hP
      hA0
      hB0
      hP1Angle

  have hQ1Angle :
      ang Q A0 B0 =
        ang Q Q1 B0 :=
    q1_angle_chain
      ang
      ψ
      hQA0
      hQQ1

  have hQ1 :
      OnCircle ω Q1 :=
    q1_membership
      ω
      hQ
      hA0
      hB0
      hQ1Angle

  exact
    concyclic_of_same_circle
      OnCircle
      hP
      hQ
      hP1
      hQ1
