open Pi Equiv Function

namespace IMO2010P5

/-- A configuration is reachable from `(1,1,1,1,1,1)` by legal moves. -/
inductive Reachable : (Fin 6 → ℕ) → Prop
  | base : Reachable 1

  /-- Type 1:
  remove one coin from `Bᵢ` and put two in `Bᵢ₊₁`. -/
  | move1 {B i}
      (rB : Reachable B)
      (hi : i < 5)
      (pB : 0 < B i) :
      Reachable
        (B - Pi.single i 1 +
          Pi.single (i + 1) 2)

  /-- Type 2:
  remove one coin from `Bᵢ`, then swap `Bᵢ₊₁` and `Bᵢ₊₂`. -/
  | move2 {B i}
      (rB : Reachable B)
      (hi : i < 4)
      (pB : 0 < B i) :
      Reachable
        (B ∘ Equiv.swap (i + 1) (i + 2) -
          Pi.single i 1)

namespace Reachable

end Reachable
