"""Auditoria de la prueba compilada (paso 8).

Politica explicita:
  * Se rechaza `sorryAx`.
  * Se rechaza cualquier axioma que no este en la lista de permitidos.
  * Se aceptan los fundamentos estandar: `propext`, `Classical.choice`,
    `Quot.sound`.
  * Buscar la palabra `sorry` en el texto NO basta: se revisan las
    dependencias reales de la declaracion final.

Prototipo: se analiza la salida de `#print axioms candidate`.
Version robusta: un auditor escrito en Lean que consulte el entorno y emita
JSON estructurado (pendiente, ver README).
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .config import DEFAULT_ALLOWED_AXIOMS, TARGET_DECL

_NO_AXIOMS = re.compile(r"'([A-Za-z0-9_.]+)' does not depend on any axioms")
_AXIOMS = re.compile(r"'([A-Za-z0-9_.]+)' depends on axioms:\s*\[([^\]]*)\]")


@dataclass(frozen=True)
class AuditResult:
    passed: bool
    axioms: tuple
    reason: str = ""

    def to_dict(self) -> dict:
        return {"audit_passed": self.passed, "axioms": list(self.axioms), "audit_reason": self.reason}


def parse_axioms(output: str, decl: str = TARGET_DECL):
    """Devuelve la lista de axiomas, o None si la declaracion no aparece."""
    for m in _NO_AXIOMS.finditer(output):
        if m.group(1) == decl:
            return []
    for m in _AXIOMS.finditer(output):
        if m.group(1) == decl:
            raw = [a.strip() for a in m.group(2).split(",")]
            return [a for a in raw if a]
    return None


def audit(output: str, allowed=DEFAULT_ALLOWED_AXIOMS, decl: str = TARGET_DECL) -> AuditResult:
    if re.search(r"declaration uses 'sorry'", output):
        return AuditResult(False, (), "la declaracion usa 'sorry'")

    axioms = parse_axioms(output, decl)
    if axioms is None:
        return AuditResult(
            False,
            (),
            f"no se encontro la salida de '#print axioms {decl}': "
            "la declaracion esperada no existe o no compilo",
        )

    if "sorryAx" in axioms:
        return AuditResult(False, tuple(axioms), "depende de sorryAx")

    extra = [a for a in axioms if a not in allowed]
    if extra:
        return AuditResult(False, tuple(axioms), f"axiomas no permitidos: {sorted(extra)}")

    return AuditResult(True, tuple(axioms), "")
