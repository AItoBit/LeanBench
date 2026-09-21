"""Carga de problemas y splits (pasos 6 y 15)."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from .config import REPO_ROOT, Budget

PROBLEMS_DIR = REPO_ROOT / "problems"
SPLITS_DIR = REPO_ROOT / "splits"

REQUIRED_FIELDS = (
    "id",
    "topic",
    "source",
    "family_id",
    "split",
    "imports",
    "statement_file",
    "reference_file",
    "formalization_reviewed",
)


@dataclass(frozen=True)
class Problem:
    id: str
    topic: str
    source: str
    family_id: str
    split: str
    imports: tuple
    statement: str
    reference_proof_path: Path
    directory: Path
    metadata: dict

    @property
    def budget(self) -> Budget:
        b = self.metadata.get("budget", {})
        return Budget(
            attempts=b.get("attempts", 1),
            verification_seconds=b.get("verification_seconds", 30),
        )

    @property
    def reference_proof(self) -> str:
        return self.reference_proof_path.read_text(encoding="utf-8")


def load_problem(problem_dir) -> Problem:
    problem_dir = Path(problem_dir)
    meta = json.loads((problem_dir / "problem.json").read_text(encoding="utf-8"))
    missing = [f for f in REQUIRED_FIELDS if f not in meta]
    if missing:
        raise ValueError(f"{problem_dir.name}: faltan campos {missing}")
    if meta["id"] != problem_dir.name:
        raise ValueError(f"{problem_dir.name}: el id '{meta['id']}' no coincide con la carpeta")
    statement = (problem_dir / meta["statement_file"]).read_text(encoding="utf-8").strip()
    if not statement.rstrip().endswith(":="):
        raise ValueError(f"{meta['id']}: el enunciado debe terminar en ':='")
    return Problem(
        id=meta["id"],
        topic=meta["topic"],
        source=meta["source"],
        family_id=meta["family_id"],
        split=meta["split"],
        imports=tuple(meta["imports"]),
        statement=statement,
        reference_proof_path=REPO_ROOT / meta["reference_file"],
        directory=problem_dir,
        metadata=meta,
    )


def all_problem_dirs():
    return sorted(p for p in PROBLEMS_DIR.iterdir() if (p / "problem.json").exists())


def load_all():
    return [load_problem(d) for d in all_problem_dirs()]


def load_split(name: str):
    path = SPLITS_DIR / f"{name}.txt"
    ids = [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.startswith("#")
    ]
    by_id = {p.id: p for p in load_all()}
    unknown = [i for i in ids if i not in by_id]
    if unknown:
        raise ValueError(f"split '{name}' referencia problemas inexistentes: {unknown}")
    return [by_id[i] for i in ids]
