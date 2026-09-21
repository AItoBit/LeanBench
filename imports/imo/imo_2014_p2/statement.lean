/--
Arithmetic core of IMO 2014 Problem 2.

If `q` is the least positive integer whose square reaches `n`
and `k=q-1`, then

* `k² < n`;
* `n ≤ (k+1)²`;
* `n-k+1 > k(k-1)+1`;
* every `m` with `m²<n` satisfies `m≤k`.

This is the numerical content behind

    k = ⌈√n⌉ - 1.
-/
theorem candidate
    {n q : ℕ}
    (hn : 2 ≤ n)
    (hq : 2 ≤ q)
    (hupper :
      n ≤ q * q)
    (hminimal :
      ∀ t : ℕ,
        t < q →
        t * t < n) :
    let k :=
