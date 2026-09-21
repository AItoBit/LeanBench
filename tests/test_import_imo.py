"""Tests del importador de IMO con archivos sinteticos."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from import_imo import analyse  # noqa: E402


def _write(tmp_path, text, year="2000", p="1"):
    d = tmp_path / year
    d.mkdir(parents=True, exist_ok=True)
    f = d / f"P{p}.lean"
    f.write_text(text, encoding="utf-8")
    return analyse(f, year, p)


def test_teorema_limpio_es_A(tmp_path):
    info = _write(tmp_path, "import Mathlib\n\n/-- Enunciado. -/\n"
                  "theorem imo_2000_p1 (n : ℕ) : n + 0 = n := by\n  simp\n")
    assert info["category"] == "A"
    assert info["statement"].rstrip().endswith(":=")
    assert "theorem candidate (n : ℕ)" in info["statement"]
    assert info["reference"].startswith("by")
    assert info["informal"] == "Enunciado."
    assert info["target_decl"] == "candidate"


def test_namespace_produce_epilogo_y_nombre_completo(tmp_path):
    info = _write(tmp_path, "import Mathlib\n\nnamespace IMO2000P1\n\n"
                  "theorem imo2000_p1 : True := by\n  trivial\n\nend IMO2000P1\n")
    assert info["category"] == "A"
    assert info["epilogue"] == "end IMO2000P1"
    assert info["target_decl"] == "IMO2000P1.candidate"
    assert "end IMO2000P1" not in info["reference"]


def test_definiciones_previas_es_B(tmp_path):
    info = _write(tmp_path, "import Mathlib\n\ndef f (n : ℕ) : ℕ := n\n\n"
                  "theorem imo_2000_p1 : f 0 = 0 := rfl\n")
    assert info["category"] == "B"
    assert "def f" in info["context"]
    assert "def f" not in info["statement"]


def test_lemas_auxiliares_es_C(tmp_path):
    info = _write(tmp_path, "import Mathlib\n\n/-- ayuda -/\nlemma aux : True := trivial\n\n"
                  "/-- Enunciado. -/\ntheorem imo_2000_p1 : True := aux\n")
    assert info["category"] == "C"
    assert info["aux"].startswith("/-- ayuda -/")       # el docstring va con su lema
    assert "Enunciado" not in info["aux"]
    assert info["statement"].startswith("/-- Enunciado. -/")


def test_sorry_y_axiom_se_excluyen(tmp_path):
    assert _write(tmp_path, "import Mathlib\ntheorem imo_2000_p1 : False := by\n  sorry\n",
                  p="2")["category"] == "X"
    assert _write(tmp_path, "import Mathlib\naxiom h : False\ntheorem imo_2000_p1 : False := h\n",
                  p="3")["category"] == "X"


def test_sorry_en_comentario_no_excluye(tmp_path):
    info = _write(tmp_path, "import Mathlib\n/-! Sin `sorry`. -/\n"
                  "theorem imo_2000_p1 : True := by\n  -- no sorry\n  trivial\n", p="4")
    assert info["category"] == "A"


def test_nucleo_parcial_se_marca(tmp_path):
    info = _write(tmp_path, "import Mathlib\n/-! # Algebraic core of the problem -/\n"
                  "theorem imo_2000_p1 : True := trivial\n", p="5")
    assert "core_like" in info["flags"]
