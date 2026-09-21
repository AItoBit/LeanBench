"""Tests de clasificacion de estados y de la ruta de error de infraestructura."""

import os

from runner import status as S
from runner.audit import AuditResult
from runner.evaluate import classify, evaluate_attempt
from runner.execute import ExecutionResult
from runner.problems import load_split

OK = AuditResult(True, ("propext",))
KO = AuditResult(False, ("sorryAx",), "depende de sorryAx")


def _exec(**kw):
    base = dict(exit_code=0, stdout="", stderr="", wall_seconds=0.1,
                timed_out=False, resource_limited=False, infrastructure_error="")
    base.update(kw)
    return ExecutionResult(**base)


def test_prueba_correcta_se_acepta():
    assert classify(_exec(), OK) == S.ACCEPTED


def test_codigo_de_salida_cero_con_sorry_no_es_aceptado():
    assert classify(_exec(exit_code=0), KO) == S.AUDIT_REJECTED


def test_error_de_tipos_es_compile_error():
    assert classify(_exec(exit_code=1, stdout="error: type mismatch"), KO) == S.COMPILE_ERROR


def test_timeout_se_registra():
    assert classify(_exec(timed_out=True, exit_code=-9), KO) == S.TIMEOUT


def test_limite_de_recursos_se_registra():
    assert classify(_exec(resource_limited=True, exit_code=-24), KO) == S.RESOURCE_LIMIT


def test_dependencia_ausente_es_error_de_infraestructura():
    assert classify(_exec(infrastructure_error="no se encontro 'lake'"), KO) == S.INFRASTRUCTURE_ERROR
    assert classify(_exec(exit_code=1, stdout="unknown module prefix 'Mathlib'"), KO) == S.INFRASTRUCTURE_ERROR


def test_intento_rechazado_antes_de_compilar(tmp_path):
    problem = load_split("dev")[0]
    record = evaluate_attempt(problem, "by sorry", tmp_path, method="test")
    assert record["status"] == S.AUDIT_REJECTED
    assert record["audit_passed"] is False
    assert record["verification_seconds"] == 0.0


def test_lake_ausente_produce_infraestructura(tmp_path, monkeypatch):
    monkeypatch.setenv("LEANBENCH_LAKE", os.path.join(str(tmp_path), "lake_inexistente"))
    problem = load_split("dev")[0]
    record = evaluate_attempt(problem, "by simp", tmp_path, method="test")
    assert record["status"] == S.INFRASTRUCTURE_ERROR


def test_el_entorno_de_verificacion_no_lleva_secretos(monkeypatch):
    """Lista negra: pasa el entorno del sistema, quita claves y tokens."""
    from runner.execute import _clean_env

    monkeypatch.setenv("ANTHROPIC_API_KEY", "secreto")
    monkeypatch.setenv("GITHUB_TOKEN", "secreto")
    monkeypatch.setenv("MI_PASSWORD", "secreto")
    monkeypatch.setenv("PATHEXT", ".COM;.EXE")
    env = _clean_env()

    assert "ANTHROPIC_API_KEY" not in env
    assert "GITHUB_TOKEN" not in env
    assert "MI_PASSWORD" not in env
    # Lo que Lean necesita sigue estando.
    assert env.get("PATHEXT") == ".COM;.EXE"
    assert "PATH" in env
