open Classical in
/-- **IMO 1989 P6.** More listings of `{0, …, 2n-1}` have property `T` than do not. -/
theorem candidate (n : ℕ) (hn : 0 < n) :
    ((perms n).filter (fun l => l.IsChain (NotPair n))).card
      < ((perms n).filter (fun l => ¬ l.IsChain (NotPair n))).card :=
