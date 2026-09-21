/-- Splitting a sum along an intersection. -/
private lemma sum_split (X Y : Finset ℕ) :
    ∑ x ∈ X \ Y, x + ∑ x ∈ X ∩ Y, x = ∑ x ∈ X, x := by
  have hsub : X ∩ Y ⊆ X := Finset.inter_subset_left
  have hs := Finset.sum_sdiff (f := fun x => x) hsub
  have hXY : X \ (X ∩ Y) = X \ Y := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rwa [hXY] at hs

/-- If `A ≠ B` are subsets of `S` with equal sums, then `A \ B` is nonempty. -/
private lemma nonempty_sdiff {S A B : Finset ℕ} (hS : ∀ n ∈ S, 10 ≤ n ∧ n ≤ 99)
    (hA : A ⊆ S) (hB : B ⊆ S) (hne : A ≠ B) (hsum : ∑ x ∈ A, x = ∑ x ∈ B, x) :
    (A \ B).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hsub : A ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hemp
  have h1 : ∑ x ∈ B \ A, x + ∑ x ∈ B ∩ A, x = ∑ x ∈ B, x := sum_split B A
  have h2 : B ∩ A = A := Finset.inter_eq_right.mpr hsub
  rw [h2, ← hsum] at h1
  have h3 : ∑ x ∈ B \ A, x = 0 := by omega
  have h4 : B \ A = ∅ := by
    by_contra hcon
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
    have hx0 : x = 0 := Finset.sum_eq_zero_iff.mp h3 x hx
    have hxS : x ∈ S := hB (Finset.mem_sdiff.mp hx).1
    have := (hS x hxS).1
    omega
  exact hne (Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp h4))
