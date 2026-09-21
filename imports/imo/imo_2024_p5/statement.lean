theorem candidate
    (h1 :
      ¬ GuaranteedBy 1)
    (h2 :
      ¬ GuaranteedBy 2)
    (h3 :
      GuaranteedBy 3) :
    IsMinimumPositiveAttempts
      GuaranteedBy
      3 :=
