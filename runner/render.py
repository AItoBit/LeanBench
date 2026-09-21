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

from .config import REPO_ROOT
from .lexing import mask

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


#: Opciones que solo cambian presupuestos de recursos, nunca la confianza.
RESOURCE_OPTIONS = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats",
                    "synthInstance.maxSize"}


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

    # Las comprobaciones se hacen sobre el codigo sin comentarios ni cadenas:
    # un comentario que diga "sin sorry" o un titulo "## Lemas" no es codigo.
    code = mask(text)

    for token in FORBIDDEN_TOKENS:
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])", code):
            raise ProofRejected(f"construccion no permitida: {token}")

    for lineno, line in enumerate(code.splitlines(), start=1):
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

    if re.search(r"(?<![A-Za-z0-9_])set_option(?![A-Za-z0-9_])", code):
        # Solo se permiten opciones de recursos, nunca de confianza.
        for m in re.finditer(r"set_option\s+([A-Za-z0-9_.]+)", code):
            if m.group(1) not in RESOURCE_OPTIONS:
                raise ProofRejected(f"set_option no permitido: {m.group(1)}")

    return text


#: Atributos permitidos en lemas auxiliares: no cambian el significado del
#: enunciado. Cualquier otro (instance, default_instance, macro...) podria.
ALLOWED_AUX_ATTRIBUTES = {"simp", "local simp"}

_IDENT = re.compile(r"[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1F00-\u1FFF][A-Za-z0-9_'.!?\u00C0-\u024F\u0370-\u03FF\u2080-\u209C\u1F00-\u1FFF]*")


def sanitize_aux(aux: str, statement: str = "") -> str:
    """Valida los lemas auxiliares del modo archivo completo.

    Solo se admiten `theorem`/`lemma` (opcionalmente `private`, con docstring
    y con `@[simp]`). Nada que pueda cambiar como se elabora el enunciado:
    ni `def`, ni `instance`, ni `notation`, ni `open`, ni `namespace`.
    Ademas, ningun lema puede llamarse como un identificador del enunciado,
    para que no pueda suplantar un nombre que el enunciado usa.
    """
    if aux is None or not aux.strip():
        return ""
    if len(aux) > 20 * MAX_PROOF_CHARS:
        raise ProofRejected("lemas auxiliares demasiado largos")
    text = aux.strip("\n")
    code = mask(text)

    for token in FORBIDDEN_TOKENS:
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(token)}(?![A-Za-z0-9_])", code):
            raise ProofRejected(f"construccion no permitida en los lemas: {token}")
    for m in re.finditer(r"set_option\s+([A-Za-z0-9_.]+)", code):
        if m.group(1) not in RESOURCE_OPTIONS:
            raise ProofRejected(f"set_option no permitido en los lemas: {m.group(1)}")

    names = []
    for lineno, line in enumerate(code.splitlines(), start=1):
        if not line.strip() or line[0] in " \t":
            continue
        rest = line.strip()
        for attr in re.findall(r"@\[([^\]]*)\]", rest):
            if attr.strip() not in ALLOWED_AUX_ATTRIBUTES:
                raise ProofRejected(f"atributo no permitido en la linea {lineno}: @[{attr}]")
        rest = re.sub(r"^(?:@\[[^\]]*\]\s*)*", "", rest)
        if not rest:
            continue  # atributo solo en su linea; se aplica al lema siguiente
        m = re.match(r"(?:private\s+)?(theorem|lemma)\s+([^\s(:{\[⦃]+)", rest)
        if m:
            names.append(m.group(2))
            continue
        if re.match(r"set_option\s+\S+\s+\S+\s+in\s*$", rest):
            continue
        if re.match(r"(open|omit)\s+[^\n]*\bin\s*$", rest):
            continue  # `open X in` / `omit h in` solo afectan al lema siguiente
        if re.match(r"(termination_by|decreasing_by)\b", rest):
            continue  # clausulas del lema anterior
        # `include` NO se admite: anadiria hipotesis tambien al enunciado.
        head = rest.split()[0]
        raise ProofRejected(
            f"en los lemas auxiliares solo se admiten theorem/lemma (linea {lineno}: '{head}')")

    stmt_idents = set(_IDENT.findall(mask(statement))) if statement else set()
    stmt_last = {i.split(".")[-1] for i in stmt_idents} | stmt_idents
    for n in names:
        if n == "candidate" or n.split(".")[-1] == "candidate":
            raise ProofRejected("un lema auxiliar no puede llamarse 'candidate'")
        if n in stmt_last or n.split(".")[-1] in stmt_last:
            raise ProofRejected(f"el lema '{n}' usa un nombre que aparece en el enunciado")
    return text


def indent_proof(proof: str) -> str:
    """Coloca la prueba detras del `:=` del enunciado.

    La primera linea va en la misma linea que `:=` (asi `by`/`calc` quedan
    donde el autor los escribio). Las demas se conservan tal cual, salvo que
    alguna empiece en la columna 0: entonces todas se indentan 2 espacios,
    porque Lean no acepta el cuerpo de una declaracion en la columna 0.
    """
    lines = proof.splitlines()
    if not lines:
        return ""
    first, rest = lines[0].strip(), lines[1:]
    if any(l.strip() and not l[0].isspace() for l in rest):
        rest = ["  " + l if l.strip() else "" for l in rest]
    return "\n".join([" " + first] + rest)


def render(problem, proof: str, attempt_dir, aux: str = "") -> RenderedAttempt:
    """Escribe `Candidate.lean` en `attempt_dir` y lo devuelve.

    Orden: imports, contexto confiable, lemas del participante (solo en modo
    'aux'), enunciado confiable + prueba del participante, epilogo, auditoria.
    """
    if aux and aux.strip() and problem.mode != "aux":
        raise ProofRejected("este problema no admite lemas auxiliares")
    clean_aux = sanitize_aux(aux, problem.statement) if problem.mode == "aux" else ""
    clean = indent_proof(sanitize_proof(proof))
    attempt_dir = Path(attempt_dir)
    attempt_dir.mkdir(parents=True, exist_ok=True)

    imports = "\n".join(f"import {mod}" for mod in problem.imports)
    epilogue = (problem.epilogue.strip() + "\n\n") if problem.epilogue.strip() else ""
    context = (problem.context + "\n\n") if problem.context else ""
    aux_block = (
        "-- >>> lemas del participante\n" + clean_aux + "\n-- <<< fin de los lemas\n\n"
    ) if clean_aux else ""
    content = (
        "-- Archivo generado por LeanBench. No editar a mano.\n"
        f"-- problema: {problem.id}\n"
        f"{imports}\n\n"
        f"{context}"
        f"{aux_block}"
        f"{problem.statement}{clean}\n\n"
        f"{epilogue}"
        f"#print axioms {problem.target_decl}\n"
    )
    path = attempt_dir / "Candidate.lean"
    path.write_text(content, encoding="utf-8")
    return RenderedAttempt(path=path, content=content, problem_id=problem.id)


def render_reference(problem, attempt_dir) -> RenderedAttempt:
    """La solucion de referencia pasa por la MISMA plantilla que un agente."""
    return render(problem, problem.reference_proof, attempt_dir, aux=problem.reference_aux)


def relative_to_repo(path) -> str:
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)
