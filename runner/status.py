"""Estados de resultado del evaluador (paso 12).

Un codigo de salida 0 NO basta para `ACCEPTED`: Lean acepta declaraciones con
`sorry` emitiendo solo una advertencia. La auditoria de axiomas es obligatoria.
"""

from __future__ import annotations

ACCEPTED = "accepted"
COMPILE_ERROR = "compile_error"
TIMEOUT = "timeout"
RESOURCE_LIMIT = "resource_limit"
AUDIT_REJECTED = "audit_rejected"
INFRASTRUCTURE_ERROR = "infrastructure_error"

ALL = (
    ACCEPTED,
    COMPILE_ERROR,
    TIMEOUT,
    RESOURCE_LIMIT,
    AUDIT_REJECTED,
    INFRASTRUCTURE_ERROR,
)

#: Fallos que NO son fallos matematicos: no deben contarse como "no resuelto".
NON_MATHEMATICAL = (INFRASTRUCTURE_ERROR,)
