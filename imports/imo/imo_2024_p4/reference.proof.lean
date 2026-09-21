by

  calc
    ang K I L + ang Y P X
        =
      (ang A I K + ang A I L) +
        (Real.pi -
          ang A I L -
          ang A I K) := by
            rw [hKILeq, hPY]

    _ =
      Real.pi := by
        ring
