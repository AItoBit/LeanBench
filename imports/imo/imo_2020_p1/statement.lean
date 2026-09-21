/--
A direct statement of the desired concurrency once the source's
circle computations have produced the needed relations.
-/
theorem candidate
    {A B C D P O : Point}

    (hD :
      OnBisector D O A P)

    (hC :
      OnBisector C O B P)

    (hOA :
      dist O A =
        dist O P)

    (hOB :
      dist O B =
        dist O P)

    (perpCriterion :
      dist O A =
          dist O B →
      OnPerpBisector O A B) :

    ConcurrentTarget
      OnBisector
      OnPerpBisector
      A B C D P :=
