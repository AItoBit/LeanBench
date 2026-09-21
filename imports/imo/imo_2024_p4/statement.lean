theorem candidate
    {A I K L Y P X : Point}

    (hPY :
      ang Y P X =
        Real.pi -
          ang A I L -
          ang A I K)

    (hKILeq :
      ang K I L =
        ang A I K +
        ang A I L) :

    ang K I L +
        ang Y P X =
      Real.pi :=
