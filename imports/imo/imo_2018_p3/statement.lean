/--
A compact abstraction of the final paragraph of the source.

If:

* the bottom row has `large + nonlarge = 2018`;
* at least 1892 entries are large;
* `bad + good = 2017` for the adjacent pairs;
* each non-large entry can spoil at most two pairs;
* all good pairs except possibly one are impossible,

then contradiction.
-/
theorem candidate
    (goodPairs : Finset (Fin 2017))
    (exception : Fin 2017)
    {large nonlarge bad : ℕ}
    (hentries :
      large + nonlarge = 2018)
    (hlarge :
      1892 ≤ large)
    (hbad :
      bad ≤ 2 * nonlarge)
    (hpairs :
      bad + goodPairs.card = 2017)
    (hforbidden :
      ∀ i ∈ goodPairs,
        i ≠ exception →
        False) :
    False :=
