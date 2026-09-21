"""Configuracion y procedencia de una ejecucion (pasos 3, 10, 17)."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

#: Fundamentos estandar que se aceptan explicitamente (paso 8).
DEFAULT_ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

#: Nombre fijo de la declaracion que debe demostrar el participante.
TARGET_DECL = "candidate"


@dataclass(frozen=True)
class Budget:
    """Presupuesto de un intento. 30 s es un punto de partida, no un estandar."""

    attempts: int = 1
    verification_seconds: int = 30
    generation_seconds: int = 120
    # 0 = sin limite. RLIMIT_AS limita el ESPACIO DE DIRECCIONES, no la RAM:
    # Lean reserva mucho mas de 4 GB virtuales al cargar Mathlib aunque use
    # menos RAM real, asi que un limite bajo lo mata al arrancar. El limite de
    # memoria real debe ponerlo el contenedor (docker --memory, cgroups).
    memory_mb: int = 0
    max_processes: int = 0


@dataclass
class RunConfig:
    """Todo lo necesario para que otra persona identifique que se evaluo."""

    run_id: str
    method: str
    split: str
    budget: Budget = field(default_factory=Budget)
    allowed_axioms: tuple = tuple(sorted(DEFAULT_ALLOWED_AXIOMS))
    leanbench_commit: str = ""
    lean_version: str = ""
    mathlib_revision: str = ""
    problem_set_hash: str = ""
    hardware: str = ""
    os_name: str = ""
    python_version: str = ""
    cache_state: str = "unknown"
    isolation: str = "none"
    model: dict = field(default_factory=dict)
    created_at: str = ""

    def to_dict(self) -> dict:
        d = asdict(self)
        d["budget"] = asdict(self.budget)
        d["allowed_axioms"] = list(self.allowed_axioms)
        return d


def _run(args, cwd=REPO_ROOT) -> str:
    try:
        out = subprocess.run(
            args, cwd=str(cwd), capture_output=True, text=True, timeout=60
        )
        return (out.stdout or "").strip()
    except Exception:
        return ""


def git_commit() -> str:
    return _run(["git", "rev-parse", "HEAD"]) or "unknown"


def git_dirty() -> bool:
    return bool(_run(["git", "status", "--porcelain"]))


def lean_version() -> str:
    return _run(["lake", "env", "lean", "--version"]) or "unknown"


def mathlib_revision() -> str:
    manifest = REPO_ROOT / "lake-manifest.json"
    if not manifest.exists():
        return "unknown"
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return "unparseable"
    for pkg in data.get("packages", []):
        if pkg.get("name") == "mathlib":
            return pkg.get("rev", "unknown")
    return "absent"


def problem_set_hash(problem_dirs) -> str:
    """Hash estable del conjunto de problemas (metadatos + enunciados)."""
    h = hashlib.sha256()
    for d in sorted(Path(p) for p in problem_dirs):
        for name in ("problem.json", "statement.lean"):
            f = d / name
            h.update(d.name.encode())
            h.update(name.encode())
            h.update(f.read_bytes() if f.exists() else b"<missing>")
    return h.hexdigest()


def build_run_config(run_id, method, split, budget, problem_dirs, model=None,
                     isolation="none", cache_state="unknown") -> RunConfig:
    return RunConfig(
        run_id=run_id,
        method=method,
        split=split,
        budget=budget,
        leanbench_commit=git_commit() + ("-dirty" if git_dirty() else ""),
        lean_version=lean_version(),
        mathlib_revision=mathlib_revision(),
        problem_set_hash=problem_set_hash(problem_dirs),
        hardware=f"{platform.machine()} / {os.cpu_count()} cpus",
        os_name=f"{platform.system()} {platform.release()}",
        python_version=sys.version.split()[0],
        cache_state=cache_state,
        isolation=isolation,
        model=model or {},
        created_at=datetime.now(timezone.utc).isoformat(),
    )
