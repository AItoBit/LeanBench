by
  have hd : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  obtain ⟨α, β, hα, hβ, hαβ, hM⟩ := hMseg
  obtain ⟨hM1, hMQ⟩ := nondegenerate a b c ha hb hc M α β hα hβ (by linarith) hM.symm
  rw [eq_Hpt_of_isOrthocenter b c hc.ne' M H hM1.ne' hMQ.ne' hH]
  refine line_equation a b c hd β M ?_
  rw [← hM]
  have hα1 : α = 1 - β := by linarith
  rw [hα1]
