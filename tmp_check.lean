-- Comprobacion manual: mismo contenido que genera el evaluador.
-- Borralo cuando termines el diagnostico.
import Mathlib
import LeanBench.Definitions.Common

theorem candidate (n : ℕ) : n + 0 = n :=
  by simp

#print axioms candidate
