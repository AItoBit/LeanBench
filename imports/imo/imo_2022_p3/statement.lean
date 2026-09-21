/--
Once the source has established ∠QPR = ∠QSR,
the desired cyclicity follows immediately.
-/
theorem candidate
    {P Q R S : Point}
    (h :
      ang Q P R =
        ang Q S R)
    (criterion :
      ang Q P R =
          ang Q S R →
      Concyclic P Q R S) :
    Concyclic P Q R S :=
