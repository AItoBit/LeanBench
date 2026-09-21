/--
Every solution enters the same initial case tree as in the source:

* `f 1 = 0`, or
* `f 1 ≠ 0` and `f 2 = 0`, or
* `f 1 ≠ 0`, `f 2 = 4 f 1`, and
  `f 3 = f 1` or `f 3 = 9 f 1`.
-/
theorem candidate
    {f : ℤ → ℤ}
    (hf : Good f) :
    f 1 = 0 ∨
    (f 1 ≠ 0 ∧ f 2 = 0) ∨
    (f 1 ≠ 0 ∧
      f 2 = 4 * f 1 ∧
      (f 3 = f 1 ∨
       f 3 = 9 * f 1)) :=
