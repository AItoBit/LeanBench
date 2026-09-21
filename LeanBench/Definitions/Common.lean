/-
Definiciones compartidas del benchmark.

Reglas:
  * Este archivo NO contiene soluciones ni lemas que resuelvan un problema.
  * Es el unico contexto auxiliar que un participante puede importar.
  * Cualquier cambio aqui invalida las ejecuciones anteriores: publica una version nueva.
-/
import Mathlib

namespace LeanBench

/-- Marcador de version del contexto compartido. Se usa en el informe. -/
def contextVersion : String := "0.1.0"

end LeanBench
