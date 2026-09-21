/--
Once the geometric proof has established P,O₁,O₂ collinear,
the requested concurrency follows immediately.
-/
theorem candidate
    {B C E F P O₁ O₂ : Point}
    (hBC :
      Collinear B C P)
    (hEF :
      Collinear E F P)
    (hcenters :
      Collinear O₁ O₂ P) :
    Concurrent
      Collinear
      B C
      E F
      O₁ O₂ :=
