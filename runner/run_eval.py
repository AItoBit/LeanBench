"""Orquestador de una ejecucion completa (pasos 14, 16, 17).

Ejemplos:
    python -m runner.run_eval --method reference --split dev
    python -m runner.run_eval --method tactic:simp --split dev
    python -m runner.run_eval --method portfolio --split dev
    python -m runner.run_eval --method model --attempts 4 --split dev
    python -m runner.run_eval --method repair --attempts 4 --split dev

Resultados: runs/<run_id>/results.jsonl + runs/<run_id>/run_config.json
"""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime
from pathlib import Path

from . import status as S
from .config import REPO_ROOT, Budget, build_run_config
from .evaluate import evaluate_attempt
from .problems import load_split
from .models import AnthropicProofGenerator, FixedProofGenerator, split_response

import sys

sys.path.insert(0, str(REPO_ROOT))
from baselines.tactics import SINGLE_TACTICS, portfolio_proofs  # noqa: E402

RUNS_DIR = REPO_ROOT / "runs"


def make_run_id(method: str) -> str:
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    return f"{stamp}__{method.replace(':', '-')}"


def run(method: str, split: str, attempts: int, verification_seconds: int,
        model_name: str) -> Path:
    problems = load_split(split)
    budget = Budget(attempts=attempts, verification_seconds=verification_seconds)
    run_id = make_run_id(method)
    run_dir = RUNS_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    generator = None
    model_meta = {}
    if method in ("model", "repair"):
        generator = AnthropicProofGenerator(model=model_name)
        model_meta = {"generator": generator.name, "model": model_name}

    cfg = build_run_config(
        run_id=run_id,
        method=method,
        split=split,
        budget=budget,
        problem_dirs=[p.directory for p in problems],
        model=model_meta,
        isolation="rlimit+pgroup" if __import__("os").name == "posix" else "timeout_only",
        cache_state="assumed_warm",
    )
    (run_dir / "run_config.json").write_text(
        json.dumps(cfg.to_dict(), indent=2, ensure_ascii=False), encoding="utf-8"
    )

    results_path = run_dir / "results.jsonl"
    with results_path.open("w", encoding="utf-8") as out:
        for problem in problems:
            for record in _attempts_for(problem, method, generator, budget, run_dir):
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                out.flush()
                print(f"{record['problem_id']:<28} {record['method']:<18} "
                      f"attempt {record['attempt']} -> {record['status']}")
                if record["status"] == S.ACCEPTED:
                    break

    print(f"\nResultados: {results_path}")
    return run_dir


def _attempts_for(problem, method, generator, budget, run_dir):
    if method == "reference":
        yield evaluate_attempt(problem, problem.reference_proof, run_dir,
                               method="reference", attempt=1, budget=budget,
                               aux=problem.reference_aux,
                               trusted_prefix=problem.reference_prefix or None)
        return

    if method.startswith("tactic:"):
        name = method.split(":", 1)[1]
        yield evaluate_attempt(problem, SINGLE_TACTICS[name], run_dir,
                               method=method, attempt=1, budget=budget)
        return

    if method == "portfolio":
        for i, (name, proof) in enumerate(portfolio_proofs(), start=1):
            record = evaluate_attempt(problem, proof, run_dir, method="portfolio",
                                      attempt=i, budget=budget,
                                      extra={"tactic": name})
            yield record
            if record["status"] == S.ACCEPTED:
                return
        return

    if method in ("model", "repair"):
        feedback = ""
        for i in range(1, budget.attempts + 1):
            gen = generator.generate_proof(problem, budget, feedback if method == "repair" else "")
            _save_generation(run_dir, problem, method, i, gen)
            if gen.error:
                yield {
                    "problem_id": problem.id, "topic": problem.topic, "method": method,
                    "attempt": i, "status": S.INFRASTRUCTURE_ERROR, "audit_passed": False,
                    "generation_seconds": round(gen.seconds, 3), "verification_seconds": 0.0,
                    "error_head": gen.error, "input_tokens": gen.input_tokens,
                    "output_tokens": gen.output_tokens,
                }
                return
            aux, proof = ("", gen.proof)
            if problem.mode == "aux":
                aux, proof = split_response(gen.proof)
            record = evaluate_attempt(
                problem, proof, run_dir, method=method, attempt=i, budget=budget,
                generation_seconds=gen.seconds, aux=aux,
                extra={"input_tokens": gen.input_tokens, "output_tokens": gen.output_tokens,
                       "cost_usd": gen.cost_usd, "independent": method == "model"},
            )
            yield record
            if record["status"] == S.ACCEPTED:
                return
            feedback = record.get("error_head", "")
        return

    raise SystemExit(f"metodo desconocido: {method}")


def _save_generation(run_dir, problem, method, attempt, gen):
    d = Path(run_dir) / "generations"
    d.mkdir(parents=True, exist_ok=True)
    payload = {
        "problem_id": problem.id, "method": method, "attempt": attempt,
        "prompt": gen.prompt, "raw_response": gen.raw_response,
        "params": gen.params, "seconds": gen.seconds,
        "input_tokens": gen.input_tokens, "output_tokens": gen.output_tokens,
        "error": gen.error,
    }
    (d / f"{problem.id}__{method}__{attempt:03d}.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8"
    )


def main():
    ap = argparse.ArgumentParser(description="Ejecuta una evaluacion de LeanBench.")
    ap.add_argument("--method", default="reference",
                    help="reference | tactic:<nombre> | portfolio | model | repair")
    ap.add_argument("--split", default="dev")
    ap.add_argument("--attempts", type=int, default=1)
    ap.add_argument("--verification-seconds", type=int, default=30)
    ap.add_argument("--model", default="claude-sonnet-4-5")
    args = ap.parse_args()
    run(args.method, args.split, args.attempts, args.verification_seconds, args.model)


if __name__ == "__main__":
    main()
