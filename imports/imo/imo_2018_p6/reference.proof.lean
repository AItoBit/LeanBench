by

  rcases h with hcommon | hspecial

  · rcases hcommon with
      ⟨φ, ψ, hBXA, hDXC, hsupp⟩

    exact
      common_case_angle_finish
        BXA
        DXC
        φ
        ψ
        hBXA
        hDXC
        hsupp

  · rcases hspecial with
      ⟨AXD, CXB, haround, hAXD, hCXB⟩

    exact
      special_case_angle_finish
        BXA
        DXC
        AXD
        CXB
        haround
        hAXD
        hCXB
