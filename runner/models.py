"""Interfaz de generacion de pruebas (paso 16).

    generate_proof(problem, budget) -> proof_text

El modelo recibe SOLO los datos permitidos: imports, definiciones compartidas y
enunciado formal. Nunca la solucion de referencia ni el resto del repositorio.
La llamada a la API ocurre FUERA del entorno de verificacion.
"""

from __future__ import annotations

import os
import re
import time
from dataclasses import dataclass, field

from .config import Budget

SYSTEM_PROMPT = (
    "Eres un asistente de Lean 4 con Mathlib. Recibes un enunciado formal y "
    "devuelves UNICAMENTE el cuerpo de la prueba que va despues de ':='. "
    "No repitas el enunciado, no escribas imports ni declaraciones nuevas, "
    "no uses sorry. Responde solo con codigo Lean."
)


AUX_MARKER = "-- LEMAS"
PROOF_MARKER = "-- PRUEBA"


def split_response(text: str):
    """Separa (lemas, prueba) de una respuesta en modo archivo completo."""
    t = text.strip()
    if t.startswith("```"):
        t = re.sub(r"^```[a-zA-Z0-9]*\n?", "", t)
        t = re.sub(r"\n?```\s*$", "", t)
    if PROOF_MARKER in t:
        before, after = t.split(PROOF_MARKER, 1)
        aux = before.replace(AUX_MARKER, "", 1).strip()
        return aux, after.strip()
    return "", t


def build_prompt(problem, error_feedback: str = "") -> str:
    parts = [
        "Imports permitidos:",
        "\n".join(f"import {m}" for m in problem.imports),
        "",
        "Contexto (definiciones previas):",
        getattr(problem, "context", "") or "(ninguno)",
        "",
        "Enunciado formal (no lo modifiques):",
        problem.statement,
        "",
        "Devuelve solo el cuerpo de la prueba.",
    ]
    if getattr(problem, "mode", "proof") == "aux":
        parts[-1] = (
            "Puedes declarar lemas auxiliares (solo `lemma`/`theorem`). Responde con este formato:\n"
            f"{AUX_MARKER}\n<tus lemas, o nada>\n{PROOF_MARKER}\n<cuerpo de la prueba>"
        )
    if error_feedback:
        parts += ["", "El intento anterior fallo con este error de Lean:", error_feedback,
                  "", "Corrige la prueba."]
    return "\n".join(parts)


@dataclass
class GenerationResult:
    proof: str
    seconds: float
    prompt: str
    raw_response: str = ""
    input_tokens: int = 0
    output_tokens: int = 0
    cost_usd: float = 0.0
    error: str = ""
    params: dict = field(default_factory=dict)


class ProofGenerator:
    """Interfaz minima que debe cumplir cualquier metodo."""

    name = "abstract"

    def generate_proof(self, problem, budget: Budget, error_feedback: str = "") -> GenerationResult:
        raise NotImplementedError


class FixedProofGenerator(ProofGenerator):
    """Devuelve siempre la misma prueba. Sirve para tacticas y para tests."""

    def __init__(self, proof: str, name: str = "fixed"):
        self.proof = proof
        self.name = name

    def generate_proof(self, problem, budget=None, error_feedback="") -> GenerationResult:
        return GenerationResult(proof=self.proof, seconds=0.0, prompt="", raw_response=self.proof)


class AnthropicProofGenerator(ProofGenerator):
    """Generador con la API de Anthropic. Requiere ANTHROPIC_API_KEY.

    La clave no entra nunca en el proceso de verificacion: `execute.py` limpia
    el entorno antes de lanzar Lean.
    """

    def __init__(self, model: str = "claude-sonnet-4-5", temperature: float = 1.0,
                 max_tokens: int = 2048):
        self.model = model
        self.name = f"anthropic:{model}"
        self.temperature = temperature
        self.max_tokens = max_tokens

    def generate_proof(self, problem, budget: Budget = None, error_feedback: str = "") -> GenerationResult:
        prompt = build_prompt(problem, error_feedback)
        params = {"model": self.model, "temperature": self.temperature,
                  "max_tokens": self.max_tokens}
        start = time.monotonic()
        try:
            import anthropic  # dependencia opcional
        except ImportError:
            return GenerationResult("", 0.0, prompt, error="falta el paquete 'anthropic'", params=params)
        if not os.environ.get("ANTHROPIC_API_KEY"):
            return GenerationResult("", 0.0, prompt, error="falta ANTHROPIC_API_KEY", params=params)

        client = anthropic.Anthropic()
        try:
            msg = client.messages.create(
                system=SYSTEM_PROMPT,
                messages=[{"role": "user", "content": prompt}],
                **params,
            )
        except Exception as exc:  # error de red o de API: no es fallo matematico
            return GenerationResult("", time.monotonic() - start, prompt,
                                    error=f"{type(exc).__name__}: {exc}", params=params)

        seconds = time.monotonic() - start
        text = "".join(b.text for b in msg.content if getattr(b, "type", "") == "text")
        return GenerationResult(
            proof=text,
            seconds=seconds,
            prompt=prompt,
            raw_response=text,
            input_tokens=getattr(msg.usage, "input_tokens", 0),
            output_tokens=getattr(msg.usage, "output_tokens", 0),
            params=params,
        )
