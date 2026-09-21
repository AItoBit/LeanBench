open Finset

/-! ### Floor wrappers

These two facts are `@[simp]` in Mathlib, but their names have moved around
(`Int.floor_add_int` → `Int.floor_add_intCast`, etc.).  Proving them by `simp`
here makes the file insensitive to that. -/
