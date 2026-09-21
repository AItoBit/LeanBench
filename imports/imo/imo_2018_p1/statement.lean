/-- **IMO 2018 P1.** `DE` and `FG` are parallel (possibly equal). -/
theorem candidate
    (O A B C D E F G : Pt) (R l m : ℝ)
    -- `A`, `B`, `C`, `F`, `G` lie on the circle `Γ` of centre `O` and radius `R`
    (hA : dotp (A - O) (A - O) = R ^ 2)
    (hB : dotp (B - O) (B - O) = R ^ 2)
    (hC : dotp (C - O) (C - O) = R ^ 2)
    (hFc : dotp (F - O) (F - O) = R ^ 2)
    (hGc : dotp (G - O) (G - O) = R ^ 2)
    -- `ABC` is a genuine triangle
    (hABC : crossp (B - A) (C - A) ≠ 0)
    -- `D` is interior to `AB`, `E` is interior to `AC`
    (hl0 : 0 < l) (hl1 : l < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hD : D = A + l • (B - A)) (hE : E = A + m • (C - A))
    -- `AD = AE`
    (hDE : dotp (D - A) (D - A) = dotp (E - A) (E - A))
    -- `F` on the perpendicular bisector of `BD`, `G` on that of `CE`
    (hFbd : dotp (F - B) (F - B) = dotp (F - D) (F - D))
    (hGce : dotp (G - C) (G - C) = dotp (G - E) (G - E))
    -- `F` on the arc `AB` away from `C`, `G` on the arc `AC` away from `B`
    (harcF : crossp (B - A) (F - A) * crossp (B - A) (C - A) < 0)
    (harcG : crossp (C - A) (G - A) * crossp (C - A) (B - A) < 0) :
    crossp (E - D) (G - F) = 0 :=
