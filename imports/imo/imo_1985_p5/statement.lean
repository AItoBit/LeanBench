namespace IMO1985P5

theorem candidate
    (θ φ η lam angle_AON angle_AMN angle_OMN angle_MNB angle_OMB : ℝ)
    (h1 : θ + φ = 90)
    (h2 : θ = η + lam)
    (h3 : angle_AON = 2 * η + 2 * lam)
    (h4 : angle_AMN = 2 * φ)
    (h5 : angle_OMN = φ)
    (h6 : angle_MNB = θ)
    (h7 : angle_OMB = angle_OMN + angle_MNB) :
    (angle_AON + angle_AMN = 180) ∧ (angle_OMB = 90) :=
