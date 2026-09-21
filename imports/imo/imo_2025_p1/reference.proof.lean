by

  have hbase :
      BaseConstructions Valid := by
    exact
      ⟨h0, h1, h3⟩

  exact
    imo2025_p1
      Valid
      hbase_forward
      hbase
      reduce
      lift
