"""Informe reproducible a partir de un results.jsonl (paso 18).

Metrica principal: exito al primer intento.
Metrica secundaria: resuelto dentro de k intentos, indicando SIEMPRE si los
intentos eran independientes o usaban reparacion. No se usa la etiqueta
'pass@k' sin definir su calculo, y aqui se define asi:

    solved_within_k = (problemas con algun intento 'accepted' con indice <= k)
                      / (problemas evaluados)

Con cinco problemas esto es una comprobacion del sistema, no evidencia de
superioridad general de ningun metodo.

Uso:
    python -m runner.report runs/<run_id>
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

from . import status as S


def load_records(run_dir):
    path = Path(run_dir) / "results.jsonl"
    with path.open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def summarize(records, config=None) -> dict:
    by_problem = defaultdict(list)
    for r in records:
        by_problem[r["problem_id"]].append(r)

    evaluated = len(by_problem)
    solved_first, solved_any = [], []
    infra = []
    for pid, rs in by_problem.items():
        rs.sort(key=lambda r: r["attempt"])
        if any(r["status"] == S.ACCEPTED for r in rs):
            solved_any.append(pid)
        if rs and rs[0]["status"] == S.ACCEPTED:
            solved_first.append(pid)
        if any(r["status"] == S.INFRASTRUCTURE_ERROR for r in rs):
            infra.append(pid)

    max_k = max((r["attempt"] for r in records), default=1)
    within_k = {}
    for k in range(1, max_k + 1):
        n = sum(
            1 for rs in by_problem.values()
            if any(r["status"] == S.ACCEPTED and r["attempt"] <= k for r in rs)
        )
        within_k[k] = n

    by_topic = defaultdict(lambda: {"evaluated": 0, "solved": 0})
    for pid, rs in by_problem.items():
        topic = rs[0].get("topic", "?")
        by_topic[topic]["evaluated"] += 1
        if any(r["status"] == S.ACCEPTED for r in rs):
            by_topic[topic]["solved"] += 1

    method = records[0]["method"] if records else "?"
    repair = any(r.get("independent") is False for r in records) or method == "repair"

    return {
        "method": method,
        "attempts_are": "reparacion (usan el error de Lean)" if repair else "independientes",
        "evaluated": evaluated,
        "solved_first_attempt": len(solved_first),
        "solved_any_attempt": len(solved_any),
        "success_rate_first": len(solved_first) / evaluated if evaluated else 0.0,
        "success_rate_any": len(solved_any) / evaluated if evaluated else 0.0,
        "solved_within_k": within_k,
        "status_counts": dict(Counter(r["status"] for r in records)),
        "by_topic": {k: v for k, v in sorted(by_topic.items())},
        "total_generation_seconds": round(sum(r.get("generation_seconds", 0) or 0 for r in records), 2),
        "total_verification_seconds": round(sum(r.get("verification_seconds", 0) or 0 for r in records), 2),
        "total_attempts": len(records),
        "input_tokens": sum(r.get("input_tokens", 0) or 0 for r in records),
        "output_tokens": sum(r.get("output_tokens", 0) or 0 for r in records),
        "cost_usd": round(sum(r.get("cost_usd", 0) or 0 for r in records), 4),
        "solved": sorted(solved_any),
        "failed": sorted(p for p in by_problem if p not in solved_any),
        "infrastructure_failures": sorted(infra),
        "config": config or {},
    }


def to_markdown(summary) -> str:
    cfg = summary.get("config", {})
    lines = [
        f"# Informe LeanBench - {summary['method']}",
        "",
        f"- Ejecucion: `{cfg.get('run_id', '?')}`",
        f"- Split: `{cfg.get('split', '?')}`",
        f"- Commit: `{cfg.get('leanbench_commit', '?')}`",
        f"- Lean: `{cfg.get('lean_version', '?')}`",
        f"- Mathlib: `{cfg.get('mathlib_revision', '?')}`",
        f"- Hash del conjunto de problemas: `{cfg.get('problem_set_hash', '?')[:16]}`",
        f"- Aislamiento: `{cfg.get('isolation', '?')}`",
        f"- Fecha: {cfg.get('created_at', '?')}",
        "",
        "## Resultado",
        "",
        f"- Resueltos al primer intento: **{summary['solved_first_attempt']} / {summary['evaluated']}** "
        f"({summary['success_rate_first']:.0%})",
        f"- Resueltos en cualquier intento: {summary['solved_any_attempt']} / {summary['evaluated']} "
        f"({summary['success_rate_any']:.0%})",
        f"- Los intentos son: {summary['attempts_are']}",
        "",
        "### Resueltos dentro de k intentos",
        "",
        "| k | resueltos |",
        "| - | --------- |",
    ]
    for k, n in summary["solved_within_k"].items():
        lines.append(f"| {k} | {n} / {summary['evaluated']} |")

    lines += ["", "### Por tema", "", "| tema | resueltos / evaluados |", "| ---- | --------------------- |"]
    for topic, v in summary["by_topic"].items():
        lines.append(f"| {topic} | {v['solved']} / {v['evaluated']} |")

    lines += ["", "### Distribucion de estados", "", "| estado | intentos |", "| ------ | -------- |"]
    for st, n in sorted(summary["status_counts"].items()):
        lines.append(f"| `{st}` | {n} |")

    lines += [
        "",
        "### Coste",
        "",
        f"- Intentos totales: {summary['total_attempts']}",
        f"- Tiempo de generacion: {summary['total_generation_seconds']} s",
        f"- Tiempo de verificacion: {summary['total_verification_seconds']} s",
        f"- Tokens: {summary['input_tokens']} entrada / {summary['output_tokens']} salida",
        f"- Coste declarado: {summary['cost_usd']} USD",
        "",
        "### Problemas",
        "",
        f"- Resueltos: {', '.join(summary['solved']) or '(ninguno)'}",
        f"- Fallidos: {', '.join(summary['failed']) or '(ninguno)'}",
    ]
    if summary["infrastructure_failures"]:
        lines += [
            "",
            "> **Aviso:** hubo fallos de infraestructura en "
            f"{', '.join(summary['infrastructure_failures'])}. "
            "No son fallos matematicos y no deben leerse como problemas no resueltos.",
        ]
    lines += [
        "",
        "---",
        "",
        "_Muestra pequena: esto es una comprobacion del sistema de evaluacion, "
        "no evidencia de superioridad general de ningun metodo._",
        "",
    ]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description="Genera el informe de una ejecucion.")
    ap.add_argument("run_dir")
    ap.add_argument("--out", default=None, help="ruta del informe markdown")
    args = ap.parse_args()

    run_dir = Path(args.run_dir)
    cfg_path = run_dir / "run_config.json"
    config = json.loads(cfg_path.read_text(encoding="utf-8")) if cfg_path.exists() else {}
    summary = summarize(load_records(run_dir), config)

    (run_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    md = to_markdown(summary)
    out = Path(args.out) if args.out else run_dir / "report.md"
    out.write_text(md, encoding="utf-8")
    print(md)
    print(f"\nInforme: {out}")


if __name__ == "__main__":
    main()
