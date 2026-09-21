"""Compila y audita todas las referencias de una carpeta de problemas.

Pensado para ejecutarse en CI (necesita Mathlib y RAM suficiente):

    python -m runner.check_references imports/imo --jobs 3

Escribe <carpeta>/COMPILE.md y <carpeta>/compile.jsonl con el estado de cada
referencia. Asi sabes cuales de tus pruebas compilan con la version de Mathlib
fijada en lean-toolchain / lake-manifest.json, antes de revisarlas.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from . import status as S
from .config import REPO_ROOT, Budget
from .evaluate import evaluate_attempt
from .problems import load_problem


def main() -> int:
    ap = argparse.ArgumentParser(description="Compila todas las referencias de una carpeta.")
    ap.add_argument("folder", help="p. ej. imports/imo o problems")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--verification-seconds", type=int, default=300)
    args = ap.parse_args()

    folder = (REPO_ROOT / args.folder).resolve()
    dirs = sorted(p for p in folder.iterdir() if (p / "problem.json").exists())
    budget = Budget(verification_seconds=args.verification_seconds)
    run_dir = Path(tempfile.mkdtemp(prefix="leanbench_refs_"))

    def one(d):
        p = load_problem(d)
        r = evaluate_attempt(p, p.reference_proof, run_dir, method="reference", budget=budget,
                             aux=p.reference_aux)
        return {k: r.get(k) for k in ("problem_id", "status", "verification_seconds",
                                      "axioms", "audit_reason", "error_head")}

    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(one, d) for d in dirs]
        for fut in as_completed(futures):
            r = fut.result()
            results.append(r)
            print(f"{r['problem_id']:<24} {r['status']:<20} {r['verification_seconds']}s",
                  flush=True)
    results.sort(key=lambda r: r["problem_id"])

    with (folder / "compile.jsonl").open("w", encoding="utf-8") as f:
        for r in results:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")

    counts = Counter(r["status"] for r in results)
    lines = ["# Compilacion de referencias", "",
             f"Carpeta: `{args.folder}` | referencias: {len(results)}", "",
             "| Estado | Cantidad |", "| ------ | -------- |"]
    lines += [f"| `{k}` | {v} |" for k, v in sorted(counts.items())]
    lines += ["", "| Problema | Estado | Segundos | Detalle |",
              "| -------- | ------ | -------- | ------- |"]
    for r in results:
        detail = (r.get("audit_reason") or r.get("error_head") or "").replace("|", "\\|")[:160]
        lines.append(f"| {r['problem_id']} | `{r['status']}` | {r['verification_seconds']} | {detail} |")
    (folder / "COMPILE.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"\n{dict(counts)}\nInforme: {folder / 'COMPILE.md'}")
    return 0 if counts.get(S.ACCEPTED, 0) == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
