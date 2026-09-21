by

  change
    Good f ↔
      f = (0 : ℝ → ℝ)
      ∨
      f = (fun x : ℝ => x - 1)
      ∨
      f = (fun x : ℝ => 1 - x)

  constructor


  /- Forward direction -/
  · intro hf

    rcases eq_or_ne f 0 with hzero | hnonzero

    /- f = 0 -/
    · exact Or.inl hzero


    /- f ≠ 0, hence f(0)=±1 -/
    · have hf0cases :
          f 0 = 1 ∨ f 0 = -1 :=
        Good.map_zero_eq_one_or_neg_one
          hf
          hnonzero

      rcases hf0cases with hf0 | hf0


      /- f(0)=1 -/
      · right
        right

        exact
          Good.eq_one_sub_of_map_zero_eq_one
            hf
            hf0


      /- f(0)=-1 -/
      · right
        left

        have hneg :
            Good (-f) :=
          Good.neg hf

        have hneg0 :
            (-f) 0 = 1 := by
          change -f 0 = 1
          linarith

        have hclass :
            (-f) =
              (fun x : ℝ => 1 - x) :=
          Good.eq_one_sub_of_map_zero_eq_one
            hneg
            hneg0

        funext x

        have hx :=
          congrFun hclass x

        change -f x = 1 - x at hx

        linarith


  /- Reverse direction -/
  · intro h

    rcases h with hzero | hsub | hone

    · rw [hzero]
      exact good_zero

    · rw [hsub]
      exact good_sub_one

    · rw [hone]
      exact good_one_sub
