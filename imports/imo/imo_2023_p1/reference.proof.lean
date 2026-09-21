by

  intro n hn hcomp

  constructor

  · intro h

    exact
      necessity
        n
        hn
        hcomp
        h

  · intro h

    rcases h with
      ⟨p,
       a,
       hp,
       ha,
       rfl⟩

    exact
      sufficiency
        p
        a
        hp
        ha

/-!
============================================================
18. Explicit local condition for prime powers
============================================================
-/
