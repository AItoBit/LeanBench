"""Tests de la auditoria de axiomas (pasos 8 y 13)."""

from runner.audit import audit, parse_axioms

ESTANDAR = "'candidate' depends on axioms: [propext, Classical.choice, Quot.sound]"
SORRY = (
    "Candidate.lean:5:0: warning: declaration uses 'sorry'\n"
    "'candidate' depends on axioms: [sorryAx]"
)
SIN_AXIOMAS = "'candidate' does not depend on any axioms"
AJENO = "'otra' does not depend on any axioms"
NUEVO = "'candidate' depends on axioms: [propext, miAxioma]"


def test_sin_axiomas_pasa():
    assert audit(SIN_AXIOMAS).passed


def test_fundamentos_estandar_pasan():
    r = audit(ESTANDAR)
    assert r.passed
    assert "Classical.choice" in r.axioms


def test_sorry_falla_la_auditoria():
    r = audit(SORRY)
    assert not r.passed
    assert "sorry" in r.reason


def test_axioma_nuevo_falla_la_auditoria():
    r = audit(NUEVO)
    assert not r.passed
    assert "miAxioma" in r.reason


def test_declaracion_ausente_falla():
    r = audit(AJENO)
    assert not r.passed
    assert "no se encontro" in r.reason


def test_politica_mas_estricta_rechaza_lo_clasico():
    r = audit(ESTANDAR, allowed=frozenset({"propext"}))
    assert not r.passed


def test_parse_axiomas():
    assert parse_axioms(ESTANDAR) == ["propext", "Classical.choice", "Quot.sound"]
    assert parse_axioms(SIN_AXIOMAS) == []
    assert parse_axioms(AJENO) is None
