#!/usr/bin/env python3
"""Validacion de metadatos, identificadores y splits (paso 19).

Se ejecuta en CI antes de tocar Lean: falla rapido y con un mensaje claro.
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from runner.problems import load_all, load_split  # noqa: E402

SPLITS = ("dev", "test")


def main() -> int:
    errores = []

    try:
        problems = load_all()
    except Exception as exc:
        print(f"ERROR al cargar los problemas: {exc}")
        return 1

    if len(problems) < 5:
        errores.append(f"v0.1 requiere al menos 5 problemas, hay {len(problems)}")

    for pid, n in Counter(p.id for p in problems).items():
        if n > 1:
            errores.append(f"id duplicado: {pid}")

    for p in problems:
        if not p.metadata.get("formalization_reviewed"):
            errores.append(f"{p.id}: formalizacion sin revisar")
        if not p.reference_proof_path.exists():
            errores.append(f"{p.id}: falta la solucion de referencia {p.reference_proof_path}")
        elif "theorem candidate" in p.reference_proof:
            errores.append(f"{p.id}: la referencia repite el enunciado; debe ser solo la prueba")
        if "Mathlib" not in p.imports:
            errores.append(f"{p.id}: se esperaba 'Mathlib' entre los imports")

    familias = defaultdict(set)
    en_split = set()
    for name in SPLITS:
        try:
            for p in load_split(name):
                familias[p.family_id].add(name)
                en_split.add(p.id)
                if p.split != name:
                    errores.append(f"{p.id}: declara split '{p.split}' pero aparece en {name}.txt")
        except Exception as exc:
            errores.append(f"split '{name}': {exc}")

    for fam, s in familias.items():
        if len(s) > 1:
            errores.append(f"la familia '{fam}' aparece en varios splits: {sorted(s)}")

    huerfanos = sorted({p.id for p in problems} - en_split)
    if huerfanos:
        errores.append(f"problemas que no estan en ningun split: {huerfanos}")

    if errores:
        print("Validacion FALLIDA:")
        for e in errores:
            print(f"  - {e}")
        return 1

    print(f"Validacion correcta: {len(problems)} problemas, splits consistentes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
