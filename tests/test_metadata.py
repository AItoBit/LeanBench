"""Validacion de metadatos y splits (pasos 6, 15, 19)."""

from collections import Counter, defaultdict

from runner.config import REPO_ROOT
from runner.problems import load_all, load_split

PROBLEMS = load_all()


def test_hay_al_menos_cinco_problemas():
    assert len(PROBLEMS) >= 5


def test_ids_unicos():
    dup = [i for i, n in Counter(p.id for p in PROBLEMS).items() if n > 1]
    assert not dup, f"ids duplicados: {dup}"


def test_todos_revisados():
    sin_revisar = [p.id for p in PROBLEMS if not p.metadata.get("formalization_reviewed")]
    assert not sin_revisar, f"formalizacion sin revisar: {sin_revisar}"


def test_las_referencias_existen():
    faltan = [p.id for p in PROBLEMS if not p.reference_proof_path.exists()]
    assert not faltan, f"faltan soluciones de referencia: {faltan}"


def test_la_referencia_no_contiene_el_enunciado():
    """La referencia guarda solo el cuerpo de la prueba: pasa por la plantilla."""
    for p in PROBLEMS:
        assert "theorem candidate" not in p.reference_proof, p.id


def test_las_familias_no_se_solapan_entre_splits():
    familias = defaultdict(set)
    for name in ("dev", "test"):
        for p in load_split(name):
            familias[p.family_id].add(name)
    solapadas = {f: s for f, s in familias.items() if len(s) > 1}
    assert not solapadas, f"familias repartidas entre splits: {solapadas}"


def test_cada_problema_esta_en_su_split():
    for name in ("dev", "test"):
        for p in load_split(name):
            assert p.split == name, f"{p.id} declara split '{p.split}' pero esta en {name}.txt"


def test_no_hay_soluciones_en_las_definiciones_compartidas():
    common = (REPO_ROOT / "LeanBench" / "Definitions" / "Common.lean").read_text(encoding="utf-8")
    assert "theorem candidate" not in common
