namespace IMO2017P3

noncomputable section

/-
IMO 2017 Problem 3 — quantitative core of the official solution.

The official construction considers

  ε = 200 - √(200² - 1)
    = 200 - √39999.

The key facts are

  ε² + 1 = 400 ε

and

  ε > 1/400.

These imply that, while the hunter-rabbit distance d is < 100,
the rabbit can choose one of the two 200-step directions so that

  new_distance² > d² + 1/2.
-/


/- ============================================================
   Definition of ε
   ============================================================ -/

def ε : ℝ :=
  200 - Real.sqrt 39999


/- ============================================================
   Facts about √39999
   ============================================================ -/
