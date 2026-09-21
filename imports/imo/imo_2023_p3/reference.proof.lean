by

  intro a k hk

  constructor

  · intro hpoly

    have hshift :
        ShiftInvariant a k :=
      shift_from_polynomial
        a
        k
        hk
        hpoly

    have hkpos :
        0 < k := by
      omega

    exact
      shiftInvariant_implies_arithmetic
        hkpos
        hshift

  · intro harith

    exact
      polynomial_from_arithmetic
        a
        k
        hk
        harith
