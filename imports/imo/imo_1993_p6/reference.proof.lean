by
  -- In Mathlib, any element of a finite group has finite order, meaning 
  -- some strictly positive power of it is the identity element.
  have h : IsOfFinOrder (roundEquiv hn) := isOfFinOrder_of_finite (roundEquiv hn)
  exact h.exists_pow_eq_one
