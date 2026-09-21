by
  by_cases h5 : n = 5
  · -- `n = 5`: use `4` and `14`
    subst h5
    have iA : Indec 5 16 := by
      refine indec_of _ _ ⟨3, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      nlinarith
    have iB : Indec 5 196 := by
      refine indec_of _ _ ⟨39, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj2 : j ≤ 2 := by nlinarith
      interval_cases j <;> norm_num at hdvd
    have iC : Indec 5 56 := by
      refine indec_of _ _ ⟨11, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj1 : j ≤ 1 := by nlinarith
      have hj' : j = 1 := by omega
      subst hj'
      norm_num at hdvd
    exact ⟨3136, 16, 196, 56, 56, ⟨627, by norm_num, by norm_num⟩, iA, iB, iC, iC,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  by_cases h8 : n = 8
  · -- `n = 8`: use `7` and `23`
    subst h8
    have iA : Indec 8 49 := by
      refine indec_of _ _ ⟨6, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      nlinarith
    have iB : Indec 8 529 := by
      refine indec_of _ _ ⟨66, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj2 : j ≤ 2 := by nlinarith
      interval_cases j <;> norm_num at hdvd
    have iC : Indec 8 161 := by
      refine indec_of _ _ ⟨20, by norm_num, by norm_num⟩ ?_
      rintro p ⟨j, hj, rfl⟩ hdvd hle
      have hj1 : j ≤ 1 := by nlinarith
      have hj' : j = 1 := by omega
      subst hj'
      norm_num at hdvd
    exact ⟨25921, 49, 529, 161, 161, ⟨3240, by norm_num, by norm_num⟩, iA, iB, iC, iC,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  -- the general case
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 3 := ⟨n - 3, by omega⟩
  have hu2 : u ≠ 2 := by omega
  have hu5 : u ≠ 5 := by omega
  have hA : V (u + 3) ((u + 2) * (u + 2)) := ⟨u + 1, by omega, by ring⟩
  have hB : V (u + 3) ((2 * u + 5) * (2 * u + 5)) := ⟨4 * u + 8, by omega, by ring⟩
  have hC : V (u + 3) ((u + 2) * (2 * u + 5)) := ⟨2 * u + 3, by omega, by ring⟩
  have iA : Indec (u + 3) ((u + 2) * (u + 2)) := by
    refine indec_of _ _ hA ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hp : u + 4 ≤ 1 + j * (u + 3) := by nlinarith
    nlinarith
  have iB : Indec (u + 3) ((2 * u + 5) * (2 * u + 5)) := by
    refine indec_of _ _ hB ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hj1 : j = 1 := by
      by_contra hne
      have h2 : 2 ≤ j := by omega
      have hbig : 2 * u + 7 ≤ 1 + j * (u + 3) := by nlinarith
      nlinarith
    subst hj1
    rw [show 1 + 1 * (u + 3) = u + 4 from by ring,
      show (2 * u + 5) * (2 * u + 5) = (u + 4) * (4 * (u + 1)) + 9 from by ring] at hdvd
    have h9 : (u + 4) ∣ 9 := (Nat.dvd_add_right ⟨4 * (u + 1), rfl⟩).mp hdvd
    have hle9 : u + 4 ≤ 9 := Nat.le_of_dvd (by norm_num) h9
    have hub : u ≤ 5 := by omega
    interval_cases u <;> omega
  have iC : Indec (u + 3) ((u + 2) * (2 * u + 5)) := by
    refine indec_of _ _ hC ?_
    rintro p ⟨j, hj, rfl⟩ hdvd hle
    have hj1 : j = 1 := by
      by_contra hne
      have h2 : 2 ≤ j := by omega
      have hbig : 2 * u + 7 ≤ 1 + j * (u + 3) := by nlinarith
      nlinarith
    subst hj1
    rw [show 1 + 1 * (u + 3) = u + 4 from by ring,
      show (u + 2) * (2 * u + 5) = (u + 4) * (2 * u + 1) + 6 from by ring] at hdvd
    have h6 : (u + 4) ∣ 6 := (Nat.dvd_add_right ⟨2 * u + 1, rfl⟩).mp hdvd
    have hle6 : u + 4 ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    have hub : u ≤ 2 := by omega
    interval_cases u <;> omega
  refine ⟨(u + 2) * (u + 2) * ((2 * u + 5) * (2 * u + 5)), (u + 2) * (u + 2),
    (2 * u + 5) * (2 * u + 5), (u + 2) * (2 * u + 5), (u + 2) * (2 * u + 5),
    V_mul hA hB, iA, iB, iC, iC, rfl, by ring, ?_, ?_⟩
  · intro h; nlinarith
  · intro h; nlinarith
