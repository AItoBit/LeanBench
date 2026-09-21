#!/usr/bin/env python3
"""Promueve un problema importado al benchmark, DESPUES de revisarlo.

Uso:
    python scripts/promote.py imo_1959_p1 --split dev --reviewer pineapple

Antes de ejecutarlo, revisa la formalizacion (paso 7 del plan):
  1. Estan todas las hipotesis del enunciado original?
  2. El dominio es el correcto (N, Z, R)?
  3. La conclusion coincide con el problema?
  4. Hay hipotesis contradictorias que permitan demostrar cualquier cosa?
  5. Se ha supuesto la conclusion?
  6. Cubre el caso general, o solo un nucleo / caso particular?

Que hace:
  * mueve imports/imo/<id>/ a problems/<id>/
  * mueve la referencia a references/<id>.proof.lean
  * marca formalization_reviewed = true, con revisor y split
  * anade el id a splits/<split>.txt
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))


def main() -> int:
    ap = argparse.ArgumentParser(description="Promueve un problema revisado al benchmark.")
    ap.add_argument("problem_id")
    ap.add_argument("--split", required=True, choices=["dev", "test"])
    ap.add_argument("--reviewer", required=True)
    ap.add_argument("--source", default="imports/imo")
    ap.add_argument("--topic", default=None, help="corrige el tema estimado")
    args = ap.parse_args()

    src = REPO / args.source / args.problem_id
    dst = REPO / "problems" / args.problem_id
    if not (src / "problem.json").exists():
        print(f"No existe {src}")
        return 1
    if dst.exists():
        print(f"Ya existe {dst}: no sobrescribo nada")
        return 1

    meta = json.loads((src / "problem.json").read_text(encoding="utf-8"))
    if meta.get("import_category") not in ("A", "B", "C"):
        print(f"Categoria {meta.get('import_category')}: no se puede promover todavia")
        return 1
    if "core_like" in meta.get("import_flags", []):
        print("Aviso: marcado como 'core_like'. Confirma que formaliza el problema completo.")

    ref_src = src / "reference.proof.lean"
    ref_dst = REPO / "references" / f"{args.problem_id}.proof.lean"
    if ref_dst.exists():
        print(f"Ya existe {ref_dst}: no sobrescribo nada")
        return 1

    meta.update(
        split=args.split,
        formalization_reviewed=True,
        reviewer=args.reviewer,
        reference_file=f"references/{args.problem_id}.proof.lean",
    )
    if args.topic:
        meta.update(topic=args.topic, topic_is_guess=False)

    shutil.move(str(ref_src), str(ref_dst))
    aux_src = src / "reference.aux.lean"
    if aux_src.exists():
        aux_dst = REPO / "references" / f"{args.problem_id}.aux.lean"
        shutil.move(str(aux_src), str(aux_dst))
        meta["reference_aux_file"] = f"references/{args.problem_id}.aux.lean"
    shutil.move(str(src), str(dst))
    (dst / "problem.json").write_text(json.dumps(meta, indent=2, ensure_ascii=False) + "\n",
                                      encoding="utf-8")

    split_file = REPO / "splits" / f"{args.split}.txt"
    with split_file.open("a", encoding="utf-8") as f:
        f.write(args.problem_id + "\n")

    print(f"Promovido {args.problem_id} a '{args.split}'.")
    print("Comprueba con: python scripts/validate_metadata.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
