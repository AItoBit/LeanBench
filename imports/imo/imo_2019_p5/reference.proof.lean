by

  have hTotal :
      TotalRecurrence F :=
    ⟨hbase, hrec⟩

  exact
    expected_value_pretty
      F
      hTotal
      n
      hn
