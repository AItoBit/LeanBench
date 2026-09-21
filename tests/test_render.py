"""Tests del saneado y de la plantilla (paso 13)."""

import pytest

from runner.problems import load_split
from runner.render import ProofRejected, render, sanitize_proof

PROBLEM = load_split("dev")[0]


def test_prueba_valida_se_acepta():
    assert sanitize_proof("by simp") == "by simp"


def test_bloque_de_codigo_se_limpia():
    assert sanitize_proof("```lean\nby simp\n```") == "by simp"


def test_prueba_vacia_se_rechaza():
    with pytest.raises(ProofRejected):
        sanitize_proof("   ")


def test_sorry_se_rechaza_antes_de_compilar():
    with pytest.raises(ProofRejected, match="sorry"):
        sanitize_proof("by sorry")


def test_intento_de_cambiar_el_enunciado_se_rechaza():
    with pytest.raises(ProofRejected, match="nivel superior"):
        sanitize_proof("by simp\n\ntheorem candidate (n : Nat) : True := trivial")


def test_intento_de_importar_la_solucion_se_bloquea():
    with pytest.raises(ProofRejected, match="nivel superior"):
        sanitize_proof("import LeanBench.References\nby simp")


def test_axioma_nuevo_se_rechaza():
    with pytest.raises(ProofRejected):
        sanitize_proof("by exact mine\naxiom mine : False")


def test_native_decide_se_rechaza():
    with pytest.raises(ProofRejected, match="native_decide"):
        sanitize_proof("by native_decide")


def test_set_option_de_confianza_se_rechaza():
    with pytest.raises(ProofRejected, match="skipKernelTC"):
        sanitize_proof("set_option debug.skipKernelTC true in\nby simp")


def test_set_option_no_listado_se_rechaza():
    with pytest.raises(ProofRejected, match="set_option no permitido"):
        sanitize_proof("set_option pp.all true in\nby simp")


def test_set_option_de_recursos_se_permite():
    assert "maxHeartbeats" in sanitize_proof("by\n  set_option maxHeartbeats 400000 in\n  simp")


def test_el_archivo_generado_conserva_el_enunciado(tmp_path):
    rendered = render(PROBLEM, "by simp", tmp_path)
    assert PROBLEM.statement in rendered.content
    assert rendered.content.rstrip().endswith("#print axioms candidate")
    assert rendered.content.count("theorem candidate") == 1


def test_los_comentarios_no_disparan_el_saneado():
    """'sorry' o '## Titulo' dentro de un comentario no son codigo."""
    proof = "by\n/-!\n## Lemas\nNo usamos sorry.\n-/\n  simp -- sin sorry"
    assert sanitize_proof(proof)


def test_sorry_fuera_de_comentario_sigue_rechazado():
    with pytest.raises(ProofRejected, match="sorry"):
        sanitize_proof("by\n  -- comentario\n  sorry")
