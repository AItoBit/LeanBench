"""Compila y audita todas las referencias de una carpeta de problemas.

Pensado para ejecutarse en CI (necesita Mathlib y RAM suficiente):

    python -m runner.check_references imports/imo --jobs 3

Para cada problema hace dos comprobaciones:

  1. referencia: el prefijo original del autor + enunciado + prueba compila y
     pasa la auditoria de axiomas. Demuestra que el problema tiene solucion.
  2. contexto (solo modo 'aux'): el contexto que ve el participante (defs sin
     los lemas del autor) + enunciado compila con `sorry`. Si falla, el
     participante no podria ni empezar: alguna definicion depende de un lema.

Escribe <carpeta>/COMPILE.md y <carpeta>/compile.jsonl.
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
from .execute import execute
from .problems import load_problem


def check_context(problem, run_dir, budget) -> str:
    """'ok', 'error: ...' o 'timeout'. Solo tiene sentido en modo 'aux'."""
    d = Path(run_dir) / "context_checks" / problem.id
    d.mkdir(parents=True, exist_ok=True)
    imports = "\n".join(f"import {m}" for m in problem.imports)
    context = (problem.context + "\n\n") if problem.context else ""
    epilogue = (problem.epilogue.strip() + "\n") if problem.epilogue.strip() else ""
    text = f"{imports}\n\n{context}{problem.statement} by\n  sorry\n\n{epilogue}"
    path = d / "Context.lean"
    path.write_text(text, encoding="utf-8")
    ex = execute(path, budget=budget)
    if ex.timed_out:
        return "timeout"
    if ex.infrastructure_error:
        return f"error: {ex.infrastructure_error}"
    for line in ex.output.splitlines():
        if ": error" in line or line.startswith("error"):
            return "error: " + line.split("error:", 1)[-1].strip()[:140]
    return "ok" if ex.exit_code == 0 else f"error: exit {ex.exit_code}"


def main() -> int:
    ap = argparse.ArgumentParser(description="Compila todas las referencias de una carpeta.")
    ap.add_argument("folder", help="p. ej. imports/imo o problems")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--verification-seconds", type=int, default=600)
    ap.add_argument("--skip-context", action="store_true")
    args = ap.parse_args()

    folder = (REPO_ROOT / args.folder).resolve()
    dirs = sorted(p for p in folder.iterdir() if (p / "problem.json").exists())
    budget = Budget(verification_seconds=args.verification_seconds)
    run_dir = Path(tempfile.mkdtemp(prefix="leanbench_refs_"))

    def one(d):
        p = load_problem(d)
        r = evaluate_attempt(p, p.reference_proof, run_dir, method="reference", budget=budget,
                             aux=p.reference_aux, trusted_prefix=p.reference_prefix or None)
        out = {k: r.get(k) for k in ("problem_id", "status", "verification_seconds",
                                     "axioms", "audit_reason", "error_head")}
        out["category"] = p.metadata.get("import_category", "")
        out["context"] = ("-" if (args.skip_context or p.mode != "aux")
                          else check_context(p, run_dir, budget))
        return out

    results = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(one, d) for d in dirs]
        for fut in as_completed(futures):
            r = fut.result()
            results.append(r)
            print(f"{r['problem_id']:<24} {r['status']:<20} ctx={r['context'][:30]:<30} "
                  f"{r['verification_seconds']}s", flush=True)
    results.sort(key=lambda r: r["problem_id"])

    with (folder / "compile.jsonl").open("w", encoding="utf-8") as f:
        for r in results:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")

    counts = Counter(r["status"] for r in results)
    ctx_bad = [r for r in results if r["context"] not in ("ok", "-")]
    lines = ["# Compilacion de referencias", "",
             f"Carpeta: `{args.folder}` | referencias: {len(results)}", "",
             "| Estado | Cantidad |", "| ------ | -------- |"]
    lines += [f"| `{k}` | {v} |" for k, v in sorted(counts.items())]
    lines += ["", f"Contextos del participante que NO compilan: **{len(ctx_bad)}**", "",
              "## Fallos", "",
              "| Problema | Cat. | Estado | Segundos | Contexto | Detalle |",
              "| -------- | ---- | ------ | -------- | -------- | ------- |"]

    def detail(r):
        if r["status"] == S.ACCEPTED:
            return ""
        # Primero el error real de Lean; la auditoria solo si no hay error.
        text = r.get("error_head") or r.get("audit_reason") or ""
        if "Candidate.lean:" in text:
            text = text.split("Candidate.lean:", 1)[1]
        return text.replace("|", "\\|")[:200]

    for r in results:
        if r["status"] != S.ACCEPTED or r["context"] not in ("ok", "-"):
            lines.append(f"| {r['problem_id']} | {r['category']} | `{r['status']}` | "
                         f"{r['verification_seconds']} | {r['context'][:60]} | {detail(r)} |")
    lines += ["", "## Todos", "", "| Problema | Estado | Segundos |", "| --- | --- | --- |"]
    lines += [f"| {r['problem_id']} | `{r['status']}` | {r['verification_seconds']} |"
              for r in results]
    (folder / "COMPILE.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"\n{dict(counts)} | contextos con error: {len(ctx_bad)}\nInforme: {folder / 'COMPILE.md'}")
    return 0 if counts.get(S.ACCEPTED, 0) == len(results) and not ctx_bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
