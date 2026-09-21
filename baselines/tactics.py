"""Metodos de referencia sin modelo (paso 14).

Pregunta inicial: cuantos problemas resuelve ya la automatizacion disponible?
Sin esta linea base no se puede afirmar que un agente aporte una mejora.
"""

from __future__ import annotations

SINGLE_TACTICS = {
    "simp": "by simp",
    "omega": "by omega",
    "aesop": "by aesop",
    "ring": "by ring",
    "positivity": "by positivity",
    "decide": "by decide",
}

#: Estrategia en cascada: prueba varias tacticas dentro de un presupuesto total.
PORTFOLIO_ORDER = ["simp", "omega", "ring", "positivity", "aesop", "decide"]


def single(name: str) -> str:
    return SINGLE_TACTICS[name]


def portfolio_proofs():
    """Devuelve (nombre, prueba) en el orden en que se deben intentar."""
    return [(n, SINGLE_TACTICS[n]) for n in PORTFOLIO_ORDER]
