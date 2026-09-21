namespace Problem_A3

variable {Point : Type}

variable {n : ℕ}

variable (color : Point → Fin n)

variable (C : ℕ → Set Point)

/--
Formalization of the combinatorial core of the argument:
"Suppose there are n colors. Then by taking successively smaller circles 
C_2, C_3, ... , C_{n+1} we reach a contradiction, since each circle includes 
a point of different color to those on any of the larger circles."
-/

theorem candidate
    (x : Fin (n + 1) → Point)
    (hx : ∀ (j : Fin (n + 1)), x j ∈ C j.val)
    (h_diff : ∀ (i j : Fin (n + 1)), i < j → ∀ y ∈ C i.val, color (x j) ≠ color y) :
    False :=
