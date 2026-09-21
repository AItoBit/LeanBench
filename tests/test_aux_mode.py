"""Tests del modo archivo completo (lemas auxiliares)."""

import json

import pytest

from runner.problems import load_problem
from runner.render import ProofRejected, render, sanitize_aux

STATEMENT = "theorem candidate (x : ℝ) (f : ℝ → ℝ) : f x = f x :="


def test_lema_simple_se_acepta():
    aux = "lemma aux1 (a : ℕ) : a = a := rfl"
    assert sanitize_aux(aux, STATEMENT) == aux


def test_private_docstring_y_simp_se_aceptan():
    aux = "/-- doc -/\n@[simp]\nprivate lemma aux2 : True := trivial\n\nopen Finset in\ntheorem aux3 : True := trivial"
    assert sanitize_aux(aux, STATEMENT)


@pytest.mark.parametrize("aux, motivo", [
    ("def g (n : ℕ) : ℕ := n", "solo se admiten"),
    ("instance : Inhabited ℕ := ⟨0⟩", "solo se admiten"),
    ("@[instance] lemma h : True := trivial", "atributo"),
    ("notation \"ℝ\" => ℕ", "solo se admiten"),
    ("include h\nlemma k : True := trivial", "solo se admiten"),
    ("lemma f : True := trivial", "aparece en el enunciado"),
    ("lemma candidate : True := trivial", "candidate"),
    ("lemma a : False := by\n  sorry", "sorry"),
    ("axiom trampa : False", "solo se admiten"),
])
def test_construcciones_peligrosas_se_rechazan(aux, motivo):
    with pytest.raises(ProofRejected, match=motivo):
        sanitize_aux(aux, STATEMENT)


def _problem(tmp_path, mode):
    d = tmp_path / "p_aux"
    d.mkdir()
    (d / "context.lean").write_text("open Real", encoding="utf-8")
    (d / "statement.lean").write_text("theorem candidate : (1 : ℕ) = 1 :=", encoding="utf-8")
    (d / "ref.lean").write_text("by\n  exact uno", encoding="utf-8")
    meta = {"id": "p_aux", "topic": "t", "source": "s", "family_id": "p_aux", "split": "dev",
            "imports": ["Mathlib"], "statement_file": "statement.lean",
            "reference_file": str(d / "ref.lean"), "formalization_reviewed": True,
            "mode": mode, "context_file": "context.lean"}
    (d / "problem.json").write_text(json.dumps(meta), encoding="utf-8")
    return load_problem(d)


def test_orden_contexto_lemas_enunciado(tmp_path):
    p = _problem(tmp_path, "aux")
    r = render(p, "by\n  exact uno", tmp_path / "out", aux="lemma uno : (1 : ℕ) = 1 := rfl")
    c = r.content
    assert c.index("open Real") < c.index("lemma uno") < c.index("theorem candidate")
    assert c.rstrip().endswith("#print axioms candidate")


def test_modo_proof_no_admite_lemas(tmp_path):
    p = _problem(tmp_path, "proof")
    with pytest.raises(ProofRejected, match="no admite lemas"):
        render(p, "by rfl", tmp_path / "out", aux="lemma uno : True := trivial")
