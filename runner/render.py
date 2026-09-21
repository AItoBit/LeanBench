"""Generacion del archivo de intento (paso 9).

El evaluador controla el contexto y el enunciado. El participante entrega
SOLO el cuerpo de la prueba, que se inserta detras del `:=` del enunciado.

Limitaciones conocidas (documentadas a proposito):
  * El saneado es lexico. Lean admite metaprogramacion, asi que la unica
    frontera real es el aislamiento del proceso (paso 11) + la auditoria de
    axiomas (paso 8). Este modulo es la primera capa, no la unica.
  * Una version robusta deberia analizar la respuesta como un unico termino de
    prueba con el parser de Lean en vez de con expresiones regulares.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from .config import REPO_ROOT, TARGET_DECL

MAX_PROOF_CHARS = 20_000

#: Palabras que abren una declaracion de nivel superior: el participante no
#: puede introducir declaraciones nuevas ni redefinir el enunciado.
TOP_LEVEL_KEYWORDS = (
    "import", "theorem", "lemma", "def", "abbrev", "instance", "axiom",
    "opaque", "example", "structure", "inductive", "class", "macro",
    "macro_rules", "syntax", "elab", "notation", "namespace", "section",
    "end", "attribute", "deriving", "extends", "mutual",
)

#: Construcciones que rompen la confianza en el nucleo o en la auditoria.
FORBIDDEN_TOKENS = (
    "sorry", "sorryAx", "native_decide", "implemented_by", "extern",
    "unsafe", "#exit", "ofReduceBool", "ofReduceNat", "skipKernelTC",
    "trustCompiler", "Lean.Elab", "IO.FS", "System.FilePath", "#eval",
)


class ProofRejected(Exception):
    """El intento se rechaza antes de compilar."""

    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


@dataclass(frozen=True)
class RenderedAttempt:
    path: Path
    content: str
    problem_id: str


def sanitize_proof(proof: str) -> str:
    """Devuelve la prueba normalizada o lanza `ProofRejected`."""
    if proof is None or not proof.strip():
        raise ProofRejected("prueba vacia")
    if len(proof) > MAX_PROOF_CHARS:
        raise ProofRejected(f"prueba demasiado larga (> {MAX_PROOF_CHARS} caracteres)")

    # Los modelos suelen envolver la respuesta en ```lean ... ```
    text = proof.strip()
    if text.startswith("```"):
        text = re.sub(r"^```[a-zA-Z0-9]*\n?", "", text)
        text = re.sub(r"\n?```\s*$", "", text).strip()

    for token in FORBIDDEN_TOKENS:
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])", text):
            raise ProofRejected(f"construccion no permitida: {token}")

    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line or line[0] in " \t":
            continue  # linea indentada: forma parte del cuerpo de la prueba
        head = line.split()[0] if line.split() else ""
        head = head.rstrip(":")
        if head in TOP_LEVEL_KEYWORDS:
            raise ProofRejected(
                f"declaracion de nivel superior no permitida en la linea {lineno}: '{head}'"
            )
        if head.startswith("#"):
            raise ProofRejected(f"comando '#' no permitido en la linea {lineno}")

    if re.search(r"(?<![A-Za-z0-9_])set_option(?![A-Za-z0-9_])", text):
        # Solo se permiten opciones de recursos, nunca de confianza.
        for m in re.finditer(r"set_option\s+([A-Za-z0-9_.]+)", text):
            if m.group(1) not in {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats"}:
                raise ProofRejected(f"set_option no permitido: {m.group(1)}")

    return text


def indent_proof(proof: str) -> str:
    """Indenta el cuerpo para que pertenezca a la declaracion del enunciado."""
    lines = proof.splitlines()
    if not lines:
        return ""
    first = lines[0].strip()
    rest = ["  " + l if l.strip() else "" for l in lines[1:]]
    return "\n".join(["  " + first] + rest)


def render(problem, proof: str, attempt_dir) -> RenderedAttempt:
    """Escribe `Candidate.lean` en `attempt_dir` y lo devuelve."""
    clean = indent_proof(sanitize_proof(proof))
    attempt_dir = Path(attempt_dir)
    attempt_dir.mkdir(parents=True, exist_ok=True)

    imports = "\n".join(f"import {mod}" for mod in problem.imports)
    content = (
        "-- Archivo generado por LeanBench. No editar a mano.\n"
        f"-- problema: {problem.id}\n"
        f"{imports}\n\n"
        f"{problem.statement}\n"
        f"{clean}\n\n"
        f"#print axioms {TARGET_DECL}\n"
    )
    path = attempt_dir / "Candidate.lean"
    path.write_text(content, encoding="utf-8")
    return RenderedAttempt(path=path, content=content, problem_id=problem.id)


def render_reference(problem, attempt_dir) -> RenderedAttempt:
    """La solucion de referencia pasa por la MISMA plantilla que un agente."""
    return render(problem, problem.reference_proof, attempt_dir)


def relative_to_repo(path) -> str:
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)
