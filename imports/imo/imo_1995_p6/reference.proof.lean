by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  classical
  have key : ((S p).filter (fun B => rsum B = 0)).card
      = (((Finset.Icc 1 (2 * p)).powerset.filter
          (fun A => A.card = p ∧ p ∣ ∑ x ∈ A, x)).card) := by
    refine Finset.card_bij (fun B _ => B.image enc) ?_ ?_ ?_
    · intro B hB
      obtain ⟨hBS, hB0⟩ := Finset.mem_filter.mp hB
      have hcard : B.card = p := by simpa [S, Finset.mem_powersetCard] using hBS
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro n hn
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hn
        exact enc_mem_Icc b
      · rw [Finset.card_image_of_injective _ enc_injective, hcard]
      · exact (ZMod.natCast_eq_zero_iff _ p).mp (by rw [cast_sum_image_enc B hcard, hB0])
    · exact fun B _ B' _ h => Finset.image_injective enc_injective h
    · intro A hA
      rw [Finset.mem_filter, Finset.mem_powerset] at hA
      obtain ⟨hAsub, hAcard, hAdvd⟩ := hA
      have hdec : ∀ n ∈ A, enc (dec p n) = n := fun n hn => enc_dec (hAsub hn)
      have himg : (A.image (dec p)).image enc = A := by
        rw [Finset.image_image]
        rw [show (enc ∘ dec p) = fun n => enc (dec p n) from rfl]
        rw [Finset.image_congr (g := id) (fun n hn => hdec n hn), Finset.image_id]
      have hinj : Set.InjOn (dec p) A := by
        intro a ha b hb hab
        rw [← hdec a ha, ← hdec b hb, hab]
      have hcardB : (A.image (dec p)).card = p := by
        rw [Finset.card_image_of_injOn hinj, hAcard]
      refine ⟨A.image (dec p), ?_, himg⟩
      refine Finset.mem_filter.mpr ⟨by simp [S, Finset.mem_powersetCard, hcardB], ?_⟩
      have hsum := cast_sum_image_enc (A.image (dec p)) hcardB
      rw [himg] at hsum
      rw [← hsum, ZMod.natCast_eq_zero_iff]
      exact hAdvd
  rw [← key, card_model hp hodd]
