"""Un intento completo: renderizar, ejecutar, auditar, clasificar."""

from __future__ import annotations

import re
from pathlib import Path

from . import status as S
from .audit import audit
from .config import DEFAULT_ALLOWED_AXIOMS, Budget
from .execute import execute, isolation_label
from .render import ProofRejected, render

#: Sintomas de un entorno roto: no son fallos matematicos y se informan aparte.
INFRA_PATTERNS = (
    r"unknown module prefix",
    r"unknown package",
    r"no such file or directory",
    r"failed to load",
    r"error: build failed",
)


def classify(execution, audit_result, rejected_reason=None):
    if rejected_reason is not None:
        return S.AUDIT_REJECTED
    if execution.infrastructure_error:
        return S.INFRASTRUCTURE_ERROR
    if execution.timed_out:
        return S.TIMEOUT
    if execution.resource_limited:
        return S.RESOURCE_LIMIT
    # Solo lineas que NO son diagnosticos del archivo del intento: un error de
    # Lean sobre la prueba (aunque mencione "failed to load") es matematico.
    outside = "\n".join(l for l in execution.output.lower().splitlines()
                        if "candidate.lean:" not in l)
    if any(re.search(p, outside) for p in INFRA_PATTERNS):
        return S.INFRASTRUCTURE_ERROR
    if execution.exit_code != 0:
        return S.COMPILE_ERROR
    return S.ACCEPTED if audit_result.passed else S.AUDIT_REJECTED


def evaluate_attempt(
    problem,
    proof,
    run_dir,
    method="unknown",
    attempt=1,
    budget: Budget = None,
    allowed_axioms=DEFAULT_ALLOWED_AXIOMS,
    generation_seconds=0.0,
    extra=None,
    aux: str = "",
    trusted_prefix: str = None,
) -> dict:
    budget = budget or problem.budget
    attempt_dir = Path(run_dir) / "attempts" / f"{problem.id}__{method}__{attempt:03d}"

    record = {
        "problem_id": problem.id,
        "topic": problem.topic,
        "method": method,
        "attempt": attempt,
        "generation_seconds": round(generation_seconds, 3),
        "verification_seconds": 0.0,
        "isolation": isolation_label(budget),
        "attempt_dir": str(attempt_dir),
    }

    try:
        rendered = render(problem, proof, attempt_dir, aux=aux, trusted_prefix=trusted_prefix)
    except ProofRejected as exc:
        record.update(
            status=S.AUDIT_REJECTED,
            audit_passed=False,
            axioms=[],
            audit_reason=f"intento rechazado antes de compilar: {exc.reason}",
            exit_code=None,
            error_head=exc.reason,
        )
        return record

    execution = execute(rendered.path, budget=budget)
    audit_result = audit(execution.output, allowed=allowed_axioms, decl=problem.target_decl)
    result_status = classify(execution, audit_result)

    record.update(execution.to_dict())
    record.update(audit_result.to_dict())
    record["verification_seconds"] = round(execution.wall_seconds, 3)
    record["status"] = result_status
    record["error_head"] = _first_error(execution.output)
    if result_status != S.ACCEPTED:
        record["audit_passed"] = False
    (attempt_dir / "output.txt").write_text(execution.output, encoding="utf-8")
    if extra:
        record.update(extra)
    return record


def _first_error(output: str, limit: int = 400) -> str:
    for line in output.splitlines():
        if "error" in line.lower():
            return line.strip()[:limit]
    return ""
