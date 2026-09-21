"""Tests que necesitan Lean instalado. Se omiten si no hay `lake`.

Cubren el circuito completo: renderizar -> compilar -> auditar -> clasificar.
"""

import shutil

import pytest

from runner import status as S
from runner.config import Budget
from runner.evaluate import evaluate_attempt
from runner.problems import load_split

pytestmark = pytest.mark.skipif(shutil.which("lake") is None, reason="lake no esta instalado")

PROBLEMS = {p.id: p for p in load_split("dev")}
BUDGET = Budget(verification_seconds=120)


def test_referencia_aceptada(tmp_path):
    p = PROBLEMS["nat_add_zero_001"]
    r = evaluate_attempt(p, p.reference_proof, tmp_path, method="reference", budget=BUDGET)
    assert r["status"] == S.ACCEPTED, r.get("error_head")
    assert r["audit_passed"] is True


def test_error_de_tipos_rechazado(tmp_path):
    p = PROBLEMS["nat_add_zero_001"]
    r = evaluate_attempt(p, "by exact (rfl : (1 : Bool) = 1)", tmp_path, method="bad", budget=BUDGET)
    assert r["status"] == S.COMPILE_ERROR


def test_todas_las_referencias_compilan_y_pasan_auditoria(tmp_path):
    fallos = []
    for p in PROBLEMS.values():
        r = evaluate_attempt(p, p.reference_proof, tmp_path, method="reference", budget=BUDGET)
        if r["status"] != S.ACCEPTED:
            fallos.append((p.id, r["status"], r.get("error_head")))
    assert not fallos, fallos


def test_presupuesto_agotado_se_interrumpe_y_se_registra(tmp_path):
    """Un presupuesto de 1 s no alcanza ni para cargar Mathlib."""
    p = PROBLEMS["real_sq_nonneg_001"]
    r = evaluate_attempt(p, "by positivity", tmp_path, method="tiny-budget",
                         budget=Budget(verification_seconds=1))
    assert r["status"] in (S.TIMEOUT, S.RESOURCE_LIMIT)
    assert r["timed_out"] or r["resource_limited"]
