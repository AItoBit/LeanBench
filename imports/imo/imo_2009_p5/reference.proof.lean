by

  constructor

  · intro hf

    exact
      imo2009_p5_forward
        f
        hf.1
        hf.2

  · intro hid

    constructor

    · intro n hn

      rw [hid n hn]

      exact hn

    · intro a b ha hb

      have hfa :
          f a = a :=
        hid a ha

      have hfb :
          f b = b :=
        hid b hb

      rw [hfa, hfb]

      have hargpos :
          0 < b + a - 1 := by
        omega

      have hfarg :
          f (b + a - 1) =
            b + a - 1 :=
        hid
          (b + a - 1)
          hargpos

      rw [hfarg]

      unfold TriangleSides

      constructor

      · omega

      constructor

      · omega

      · omega
