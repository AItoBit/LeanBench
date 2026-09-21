#!/usr/bin/env python3
"""Importador de formalizaciones IMO a LeanBench.

Uso:
    python scripts/import_imo.py C:\\Users\\Usuario\\Downloads\\IMO-main\\IMO-main

Lee <carpeta>/<anio>/P<n>.lean, clasifica cada archivo y convierte los que se
pueden convertir sin reescribir la prueba. Escribe en imports/imo/:

    imports/imo/<id>/problem.json           metadatos (formalization_reviewed: false)
    imports/imo/<id>/statement.lean         contexto + enunciado, termina en ':='
    imports/imo/<id>/reference.proof.lean   tu prueba original, sin tocar
    imports/imo/REPORT.md                   tabla con la clasificacion
    imports/imo/classification.json         lo mismo, para scripts

Nada de esto entra en el benchmark hasta que lo revises y lo promuevas con
scripts/promote.py. El importador NO decide si la formalizacion es fiel al
enunciado original: eso es revision humana (paso 7 del plan).

Categorias:
    A  enunciado limpio: solo el teorema (y `open`/`namespace`).
    B  con definiciones: el enunciado necesita defs/estructuras previas,
       pero no hay lemas auxiliares.
    C  con lemas auxiliares: la prueba depende de lemas propios declarados
       antes. Se importan en modo archivo completo: los lemas van a
       reference.aux.lean y el evaluador los valida con sanitize_aux.
    X  excluido: sin teorema principal, usa `sorry`/`admit`, declara
       `axiom`, usa `native_decide`, o el evaluador rechazaria la prueba.

Marca aparte (no excluye): `core_like`, el texto sugiere que es un nucleo,
caso particular o version parcial del problema. Revisalo con especial cuidado.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from runner.lexing import mask  # noqa: E402
from runner.render import ProofRejected, sanitize_aux, sanitize_proof  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
OUT = REPO / "imports" / "imo"

# ---------------------------------------------------------------- lexing


MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
DECL_KW = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance",
    "axiom", "class", "example", "opaque",
)
OTHER_KW = (
    "namespace", "section", "end", "open", "variable", "universe", "set_option",
    "attribute", "import", "notation", "infix", "infixl", "infixr", "prefix",
    "postfix", "macro", "macro_rules", "syntax", "elab", "local", "scoped",
    "noncomputable", "mutual", "deriving", "initialize", "export", "include", "omit",
)
CMD_RE = re.compile(
    rf"^{ATTRS}{MODIFIERS}(?P<kw>{'|'.join(DECL_KW + OTHER_KW)}|#[a-zA-Z_]+)\b(?P<rest>[^\n]*)",
    re.M,
)


def commands(src: str, masked: str):
    """Divide el archivo en comandos de nivel superior (columna 0)."""
    starts = [m for m in CMD_RE.finditer(masked)]
    cmds = []
    for idx, m in enumerate(starts):
        start = m.start()
        end = starts[idx + 1].start() if idx + 1 < len(starts) else len(src)
        kw = m.group("kw")
        rest = m.group("rest").strip()
        name = ""
        if kw in DECL_KW:
            mm = re.match(r"([^\s(:{\[⦃]+)", rest)
            name = mm.group(1) if mm else ""
        cmds.append({"kw": kw, "name": name, "start": start, "end": end,
                     "head": rest})

    # a) Un docstring `/-- -/` pertenece al comando SIGUIENTE, no al anterior.
    for i in range(1, len(cmds)):
        seg = src[cmds[i - 1]["start"]:cmds[i]["start"]]
        stripped = seg.rstrip()
        if stripped.endswith("-/"):
            j = stripped.rfind("/--")
            k = stripped.rfind("/-!")
            if j != -1 and j > k and j > 0:
                pos = cmds[i - 1]["start"] + j
                if pos > cmds[i - 1]["start"]:
                    cmds[i - 1]["end"] = pos
                    cmds[i]["start"] = pos

    # b) `open X in` / `set_option o v in` modifican solo el comando siguiente.
    merged = []
    for c in cmds:
        if merged and merged[-1].get("prefix_in"):
            prev = merged.pop()
            c = dict(c, start=prev["start"])
        text_masked = masked[c["start"]:c["end"]].strip()
        if c["kw"] in ("open", "set_option", "omit") and re.search(r"\bin$", text_masked):
            c = dict(c, prefix_in=True)
        merged.append(c)
    for c in merged:
        c["text"] = src[c["start"]:c["end"]]
    return merged


def docstring_before(src: str, pos: int) -> str:
    """Docstring `/-- ... -/` pegado justo antes de `pos`, si lo hay."""
    before = src[:pos].rstrip()
    if not before.endswith("-/"):
        return ""
    i = before.rfind("/--")
    if i == -1:
        return ""
    return before[i + 3:-2].strip()


def module_doc(src: str) -> str:
    m = re.search(r"/-!(.*?)-/", src, re.S)
    return m.group(1).strip() if m else ""


def find_signature_end(masked_decl: str) -> int:
    """Indice del primer `:=` a profundidad 0 (fin del enunciado) o -1."""
    depth = 0
    pending = 0  # `let x := v` / `have h := p` dentro del TIPO consumen un `:=`
    opens, closes = "([{⟨⦃", ")]}⟩⦄"
    i = 0
    while i < len(masked_decl) - 1:
        c = masked_decl[i]
        if c in opens:
            depth += 1
        elif c in closes:
            depth -= 1
        elif depth == 0 and re.match(r"(let|have)\b", masked_decl[i:i + 5]) and (
                i == 0 or not (masked_decl[i - 1].isalnum() or masked_decl[i - 1] in "_.'")):
            pending += 1
        elif depth == 0 and masked_decl.startswith(":=", i):
            if pending:
                pending -= 1
            else:
                return i
        i += 1
    return -1


TRIVIAL_PREAMBLE = {"open", "namespace", "section", "end", "universe", "set_option",
                    "variable", "noncomputable", "import", "include", "omit"}
STATEMENT_CONTEXT = {"def", "abbrev", "structure", "inductive", "instance", "class",
                     "attribute", "notation", "infix", "infixl", "infixr", "prefix",
                     "postfix", "local", "scoped", "opaque", "deriving", "mutual",
                     "export"}
CORE_WORDS = re.compile(
    r"\b(core|partial|simplified|special case|particular case|version of|"
    r"reduction|weaker|restricted|variant|lemma behind|finite version|"
    r"algebraic core|only the|we only|does not formalize|not formalized)\b",
    re.I,
)


def topic_guess(text: str) -> str:
    t = text
    if re.search(r"EuclideanGeometry|EuclideanSpace|∠|Affine|Sphere|dist |inner", t):
        return "geometry"
    if re.search(r"SimpleGraph|Fintype\.card|Finset\.card|Equiv\.Perm|Function\.Injective", t):
        return "combinatorics"
    if re.search(r"∣|Nat\.Prime|Prime|ZMod|Nat\.gcd|Int\.gcd| % |Nat\.Coprime|IsSquare", t):
        return "number_theory"
    return "algebra"


# ------------------------------------------------------------ classify


def analyse(path: Path, year: str, pnum: str) -> dict:
    src = path.read_text(encoding="utf-8").replace("\r\n", "\n")
    masked = mask(src)
    cmds = commands(src, masked)
    pid = f"imo_{year}_p{pnum}"
    info = {"id": pid, "file": f"{year}/{path.name}", "year": int(year),
            "problem": int(pnum), "category": None, "reasons": [], "flags": []}

    code = masked
    if re.search(r"\bsorry\b|\badmit\b", code):
        info["reasons"].append("usa sorry/admit")
    if any(c["kw"] == "axiom" for c in cmds):
        info["reasons"].append("declara axiom")
    if re.search(r"\bnative_decide\b", code):
        info["reasons"].append("usa native_decide (la auditoria lo rechaza)")

    foreign = [m for m in re.findall(r"^import\s+(\S+)", masked, re.M)
               if m.split(".")[0] not in ("Mathlib", "Batteries", "Std", "Lean", "Init", "Aesop")]
    if foreign:
        info["reasons"].append(f"importa modulos externos al proyecto: {foreign}")

    if re.search(r"^[ \t]+(?:private\s+|protected\s+)?(?:lemma|theorem)\s+\S", masked, re.M):
        info["reasons"].append("declaraciones indentadas: el importador solo separa comandos en la columna 0")

    thms = [c for c in cmds if c["kw"] in ("theorem", "lemma")]
    if not thms:
        info["reasons"].append("no hay teorema principal")
        info["category"] = "X"
        return info

    imo_named = [c for c in thms if re.search(r"imo", c["name"], re.I)]
    main = (imo_named or thms)[-1]
    info["main_theorem"] = main["name"]
    mi = cmds.index(main)
    before, after = cmds[:mi], cmds[mi + 1:]

    helper_lemmas = [c["name"] for c in before if c["kw"] in ("theorem", "lemma", "example")]
    context_decls = [c for c in before if c["kw"] in STATEMENT_CONTEXT]
    odd_before = [c["kw"] for c in before
                  if c["kw"] not in TRIVIAL_PREAMBLE | STATEMENT_CONTEXT
                  and c["kw"] not in ("theorem", "lemma", "example", "axiom")]
    decls_after = [c["name"] or c["kw"] for c in after
                   if c["kw"] in DECL_KW and c["kw"] != "example"]

    # Enunciado y prueba
    main_masked = masked[main["start"]:main["end"]]
    sig_end = find_signature_end(main_masked)
    if sig_end == -1:
        info["reasons"].append("el teorema principal no usa ':=' (ecuaciones o 'where')")

    if CORE_WORDS.search(src):
        info["flags"].append("core_like")
    if "variable" in [c["kw"] for c in before]:
        info["flags"].append("usa variable")

    if info["reasons"]:
        info["category"] = "X"
        return info

    header = src[main["start"]:main["start"] + sig_end]
    body = src[main["start"] + sig_end + 2:main["end"]].rstrip()
    # Quita comandos de cierre que hayan quedado pegados (p. ej. `end X`)
    header_renamed = re.sub(
        rf"(\b(?:theorem|lemma)\s+){re.escape(main['name'])}(?=[\s(:{{\[⦃])",
        r"\1candidate", header, count=1)
    if header_renamed == header:
        info["reasons"].append("no se pudo renombrar el teorema principal")
        info["category"] = "X"
        return info
    header_renamed = re.sub(r"^(\s*)lemma\b", r"\1theorem", header_renamed, flags=re.M)

    short = main["name"].split(".")[-1]
    # Solo referencias al propio teorema: `imo_x.parts.a` es OTRO lema (en el
    # namespace `imo_x`) y no debe renombrarse.
    body = re.sub(rf"(?<![\w.]){re.escape(main['name'])}(?![\w'.])", "candidate", body)
    if short != main["name"]:
        body = re.sub(rf"(?<![\w.]){re.escape(short)}(?![\w'.])", "candidate", body)

    try:
        sanitize_proof(body)
    except ProofRejected as exc:
        info["reasons"].append(f"el evaluador rechazaria la prueba: {exc.reason}")
        info["category"] = "X"
        return info

    # Pila de namespaces/sections abiertos en el teorema principal
    stack = []
    for c in before:
        if c["kw"] == "namespace":
            stack.append(("namespace", c["head"].split()[0] if c["head"] else ""))
        elif c["kw"] == "section":
            stack.append(("section", c["head"].split()[0] if c["head"] else ""))
        elif c["kw"] == "noncomputable" and c["head"].startswith("section"):
            parts = c["head"].split()
            stack.append(("section", parts[1] if len(parts) > 1 else ""))
        elif c["kw"] == "end" and stack:
            stack.pop()
    ns_path = ".".join(n for kind, n in stack if kind == "namespace" and n)
    epilogue = "\n".join(f"end {n}".rstrip() for _, n in reversed(stack))
    target = f"{ns_path}.candidate" if ns_path else "candidate"

    segs = []  # (kind, short_name, text) en el orden original
    for c in before:
        if c["kw"] in ("import", "example"):
            continue
        text = src[c["start"]:c["end"]].rstrip()
        if not text.strip():
            continue
        is_lemma = c["kw"] in ("theorem", "lemma")
        segs.append(("lemma" if is_lemma else "ctx", c["name"].split(".")[-1], text))

    # Si una definicion del contexto usa un lema del autor (p. ej. dentro de un
    # `Equiv` o un subtipo), ese lema tiene que ir en el contexto: sin el, el
    # participante no podria ni compilar el enunciado. Se calcula por punto fijo.
    def uses(text, name):
        return bool(name) and re.search(rf"(?<![\w'.]){re.escape(name)}(?![\w'])", mask(text))
    keep = set()
    changed = True
    while changed:
        changed = False
        ctx_texts = [t for k, n, t in segs if k == "ctx" or n in keep]
        for k, n, t in segs:
            if k == "lemma" and n not in keep and any(uses(ct, n) for ct in ctx_texts if ct is not t):
                keep.add(n)
                changed = True
    if keep:
        info["flags"].append(f"lemas del autor en el contexto: {len(keep)}")

    context_parts, aux_parts, prefix_parts = [], [], []
    for k, n, t in segs:
        prefix_parts.append(t)  # orden original: lo que compila el autor
        (aux_parts if (k == "lemma" and n not in keep) else context_parts).append(t)
    context = "\n\n".join(context_parts)
    aux = "\n\n".join(aux_parts)

    imports = re.findall(r"^import\s+(\S+)", masked, re.M)
    imports = [m for m in dict.fromkeys(imports)] or ["Mathlib"]

    statement = header_renamed.rstrip() + " :="
    if aux:
        try:
            sanitize_aux(aux, statement)
        except ProofRejected as exc:
            info["reasons"].append(f"el evaluador rechazaria los lemas: {exc.reason}")
            info["category"] = "X"
            return info

    if helper_lemmas:
        info["category"] = "C"
    elif context_decls or odd_before:
        info["category"] = "B"
    else:
        info["category"] = "A"
    if decls_after:
        info["flags"].append(f"declaraciones despues del teorema: {decls_after[:3]}")

    mdoc = re.match(r"\s*/--(.*?)-/", src[main["start"]:main["end"]], re.S)
    informal = (mdoc.group(1).strip() if mdoc else "") or module_doc(src)
    info.update(
        imports=imports,
        context=context,
        prefix="\n\n".join(prefix_parts),
        statement=statement,
        aux=aux,
        # Si la prueba empezaba en una linea nueva, se conserva su indentacion.
        reference=(re.sub(r"^[ \t]*\n", "", body) if re.match(r"[ \t]*\n", body)
                   else body.lstrip(" ")) if body.strip() else "",
        epilogue=epilogue,
        target_decl=target,
        informal=informal,
        topic=topic_guess(header),
        helper_lemmas=helper_lemmas,
    )
    return info


# ------------------------------------------------------------- output


def write_problem(info: dict, source_url: str) -> None:
    d = OUT / info["id"]
    d.mkdir(parents=True, exist_ok=True)
    (d / "statement.lean").write_text(info["statement"] + "\n", encoding="utf-8")
    (d / "reference.proof.lean").write_text(info["reference"] + "\n", encoding="utf-8")
    if info["context"]:
        (d / "context.lean").write_text(info["context"] + "\n", encoding="utf-8")
    if info["aux"]:
        (d / "reference.aux.lean").write_text(info["aux"] + "\n", encoding="utf-8")
        # La referencia se compila con el prefijo ORIGINAL (lemas dentro de sus
        # namespaces y secciones). El participante ve el contexto sin lemas.
        (d / "reference.prefix.lean").write_text(info["prefix"] + "\n", encoding="utf-8")
    meta = {
        "id": info["id"],
        "topic": info["topic"],
        "topic_is_guess": True,
        "source": "imo",
        "source_detail": {"year": info["year"], "problem": info["problem"],
                          "file": info["file"], "repository": source_url},
        "family_id": info["id"],
        "split": "unassigned",
        "imports": info["imports"],
        "informal_statement": info["informal"],
        "mode": "aux",
        "context_file": "context.lean" if info["context"] else None,
        "statement_file": "statement.lean",
        "reference_file": f"imports/imo/{info['id']}/reference.proof.lean",
        "reference_aux_file": (f"imports/imo/{info['id']}/reference.aux.lean"
                               if info["aux"] else None),
        "reference_prefix_file": (f"imports/imo/{info['id']}/reference.prefix.lean"
                                  if info["aux"] else None),
        "target_decl": info["target_decl"],
        "epilogue": info["epilogue"],
        "import_category": info["category"],
        "import_flags": info["flags"],
        "formalization_reviewed": False,
        "reviewer": "",
        "formalization_author": "AItoBit",
        "license": "Apache-2.0",
        "budget": {"attempts": 1, "verification_seconds": 120},
    }
    (d / "problem.json").write_text(json.dumps(meta, indent=2, ensure_ascii=False) + "\n",
                                    encoding="utf-8")


def write_report(results) -> str:
    cats = Counter(r["category"] for r in results)
    imported = [r for r in results if r["category"] in ("A", "B", "C")]
    core = [r for r in imported if "core_like" in r["flags"]]
    lines = [
        "# Importacion IMO",
        "",
        f"Archivos analizados: **{len(results)}**",
        "",
        "| Categoria | Significado | Archivos |",
        "| --------- | ----------- | -------- |",
        f"| A | Enunciado limpio: se importa tal cual | {cats['A']} |",
        f"| B | Necesita definiciones previas: se importa con ellas | {cats['B']} |",
        f"| C | Usa lemas auxiliares propios: se importan como parte de la referencia | {cats['C']} |",
        f"| X | Excluido (ver motivo) | {cats['X']} |",
        "",
        f"Importados a `imports/imo/`: **{len(imported)}**. "
        f"De ellos, {len(core)} tienen la marca `core_like`: revisa con cuidado si "
        "formalizan el problema completo o solo una parte.",
        "",
        "Ninguno entra en el benchmark hasta que lo revises y lo promuevas:",
        "",
        "```",
        "python scripts/promote.py imo_1959_p1 --split dev",
        "```",
        "",
        "## Excluidos (X)",
        "",
        "| Problema | Motivo |",
        "| -------- | ------ |",
    ]
    for r in results:
        if r["category"] == "X":
            lines.append(f"| {r['id']} | {'; '.join(r['reasons'])} |")
    lines += ["", "## Importados (A, B y C)", "",
              "| Problema | Cat. | Tema (estimado) | Marcas |",
              "| -------- | ---- | --------------- | ------ |"]
    for r in results:
        if r["category"] in ("A", "B", "C"):
            lines.append(f"| {r['id']} | {r['category']} | {r.get('topic', '')} | "
                         f"{', '.join(r['flags']) or ''} |")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="Importa formalizaciones IMO a LeanBench.")
    ap.add_argument("source", help="carpeta con <anio>/P<n>.lean")
    ap.add_argument("--repository", default="https://github.com/AItoBit/IMO")
    args = ap.parse_args()

    src_root = Path(args.source)
    files = sorted(src_root.glob("[12][0-9][0-9][0-9]/[Pp]*.lean"))
    if not files:
        print(f"No encontre archivos <anio>/P<n>.lean en {src_root}")
        return 1

    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)

    results = []
    for f in files:
        m = re.fullmatch(r"[Pp](\d+)\.lean", f.name)
        if not m:
            continue
        info = analyse(f, f.parent.name, m.group(1))
        results.append(info)
        if info["category"] in ("A", "B", "C"):
            write_problem(info, args.repository)

    slim = [{k: v for k, v in r.items()
             if k not in ("statement", "reference", "informal", "context", "aux", "prefix")}
            for r in results]
    (OUT / "classification.json").write_text(
        json.dumps(slim, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    report = write_report(results)
    (OUT / "REPORT.md").write_text(report, encoding="utf-8")

    cats = Counter(r["category"] for r in results)
    print(f"Analizados: {len(results)}  |  A: {cats['A']}  B: {cats['B']}  "
          f"C: {cats['C']}  X: {cats['X']}")
    print(f"Informe: {OUT / 'REPORT.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
