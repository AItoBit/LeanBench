theorem candidate
  {α : Type*} [MetricSpace α]
  (X X' Y B B' : α)
  (hXX' : dist X X' ≤ (1:ℝ) / 2)
  (hX'Y : dist X' Y ≤ (1:ℝ) / 2)
  (hBB' : dist B B' ≤ (1:ℝ) / 2)
  (hX'B' : 100 ≤ dist X' B') :
  dist X Y ≤ (1:ℝ) ∧ 
  (99:ℝ) ≤ dist X B ∧ 
  (99:ℝ) ≤ dist Y B ∧ 
  (198:ℝ) ≤ dist X B + dist Y B :=
