by
  intro hreach
  have hc2 : (2 : ZMod 2) = 0 := by decide
  have hinv : ∀ p q : Pos, Move 97 p q → inv97 p = inv97 q := by
    rintro p q ⟨⟨hp1, hp2, hp3, hp4⟩, ⟨hq1, hq2, hq3, hq4⟩, heq⟩
    rcases sol97 heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `x` shifts by `±9`, `y` by `±4`: both parities flip
      have hxs : ((q.1 : ℤ) : ZMod 2) = ((p.1 : ℤ) : ZMod 2) + 1 := by
        rcases ha with h | h
        · have hq : q.1 = p.1 + 9 := by omega
          rw [hq]; push_cast; linear_combination (4 : ZMod 2) * hc2
        · have hq : q.1 = p.1 - 9 := by omega
          rw [hq]; push_cast; linear_combination (-5 : ZMod 2) * hc2
      have hys : blk q.2 = blk p.2 + 1 := by
        rcases hb with h | h
        · have hq : q.2 = p.2 + 4 := by omega
          rw [hq]; exact blk_add_four hp3 (by omega)
        · have hq : q.2 = p.2 - 4 := by omega
          rw [hq]; exact blk_sub_four (by omega) hp4
      unfold inv97
      rw [hxs, hys]
      linear_combination -hc2
    · -- `x` shifts by `±4`, `y` by `±9`: both parities are preserved
      have hxs : ((q.1 : ℤ) : ZMod 2) = ((p.1 : ℤ) : ZMod 2) := by
        rcases ha with h | h
        · have hq : q.1 = p.1 + 4 := by omega
          rw [hq]; push_cast; linear_combination (2 : ZMod 2) * hc2
        · have hq : q.1 = p.1 - 4 := by omega
          rw [hq]; push_cast; linear_combination (-2 : ZMod 2) * hc2
      have hys : blk q.2 = blk p.2 := by
        rcases hb with h | h
        · have hq : q.2 = p.2 + 9 := by omega
          rw [hq]; exact blk_add_nine hp3 (by omega)
        · have hq : q.2 = p.2 - 9 := by omega
          rw [hq]; exact blk_sub_nine (by omega) hp4
      unfold inv97
      rw [hxs, hys]
  have h := inv_of_reach _ hinv hreach
  unfold inv97 at h
  norm_num [blk] at h
  revert h
  decide
