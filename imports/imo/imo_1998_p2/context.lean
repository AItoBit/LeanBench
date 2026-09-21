noncomputable section

open scoped BigOperators

namespace IMO1998P2

def passes {b : ℕ} (v : Fin b → Bool) : ℕ :=
  (Finset.univ.filter (fun j => v j = true)).card

def failures {b : ℕ} (v : Fin b → Bool) : ℕ :=
  (Finset.univ.filter (fun j => v j = false)).card

def agreementCount {a b : ℕ}
    (vote : Fin a → Fin b → Bool) (j l : Fin b) : ℕ :=
  (Finset.univ.filter (fun i => vote i j = vote i l)).card

def agreement {a b : ℕ}
    (vote : Fin a → Fin b → Bool)
    (i : Fin a) (j l : Fin b) : ℝ :=
  if vote i j = vote i l then 1 else 0
