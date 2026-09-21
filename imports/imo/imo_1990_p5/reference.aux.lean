theorem aWin_of_can_choose_1990
    {n : ℕ}
    (hn : 1 < n)
    (hlegal : LegalA n 1990) :
    AWin n := by
  exact AWin.immediate hn hlegal

theorem legalA_1990_of_between
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    LegalA n 1990 := by
  refine ⟨hhi, ?_⟩
  have hsquare : 45 * 45 ≤ n * n :=
    Nat.mul_le_mul hlo hlo
  nlinarith [hsquare]

theorem aWin_of_between_45_and_1990
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    AWin n := by
  exact aWin_of_can_choose_1990
    (n := n)
    (by omega)
    (legalA_1990_of_between hlo hhi)

theorem not_bWin_of_can_choose_1990
    {n : ℕ}
    (hlegal : LegalA n 1990) :
    ¬ BWin n := by
  intro h
  cases h with
  | step active reply avoids_target legal_reply continues =>
      exact avoids_target 1990 hlegal rfl

theorem not_bWin_of_between_45_and_1990
    {n : ℕ}
    (hlo : 45 ≤ n)
    (hhi : n ≤ 1990) :
    ¬ BWin n := by
  exact not_bWin_of_can_choose_1990
    (n := n)
    (legalA_1990_of_between hlo hhi)
