"""Ejecucion de un intento (pasos 10 y 11).

Se invoca `lake env lean <archivo>` con `subprocess` y argumentos separados:
nunca se construye una orden de shell a partir de texto generado.

Aislamiento:
  * En POSIX se aplican limites de CPU, memoria y numero de procesos con
    `resource.setrlimit`, y el intento corre en su propio grupo de procesos
    para poder matar a todos los hijos al agotarse el tiempo.
  * Esto es un minimo, NO un sandbox. Antes de evaluar respuestas de modelos
    conviene ejecutar dentro de un contenedor sin red, con las dependencias en
    solo lectura y sin acceso a `references/`. Ver README, paso 11.
  * En Windows no hay `setrlimit`: solo se aplica el timeout y se registra
    `isolation="timeout_only"`.
"""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from .config import REPO_ROOT, Budget

POSIX = os.name == "posix"


@dataclass
class ExecutionResult:
    exit_code: int
    stdout: str
    stderr: str
    wall_seconds: float
    timed_out: bool
    resource_limited: bool
    infrastructure_error: str = ""

    @property
    def output(self) -> str:
        return self.stdout + ("\n" if self.stdout and self.stderr else "") + self.stderr

    def to_dict(self) -> dict:
        return {
            "exit_code": self.exit_code,
            "wall_seconds": round(self.wall_seconds, 3),
            "timed_out": self.timed_out,
            "resource_limited": self.resource_limited,
            "infrastructure_error": self.infrastructure_error,
        }


def isolation_label(budget: Budget) -> str:
    return "rlimit+pgroup" if POSIX else "timeout_only"


def _preexec(budget: Budget):
    if not POSIX:
        return None
    import resource

    def apply():
        os.setsid()
        cpu = max(1, int(budget.verification_seconds) + 5)
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
        mem = budget.memory_mb * 1024 * 1024
        try:
            resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
        except ValueError:
            pass
        try:
            resource.setrlimit(resource.RLIMIT_NPROC, (budget.max_processes, budget.max_processes))
        except ValueError:
            pass
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    return apply


#: Nombres (o fragmentos) de variables que NUNCA entran en la verificacion.
#: Lista negra, no lista blanca: elan, lake y lean necesitan muchas variables
#: del sistema (en Windows APPDATA, LOCALAPPDATA, COMSPEC, PATHEXT,
#: PROGRAMDATA...) y quitarlas los deja colgados sin ningun mensaje de error.
SECRET_PATTERNS = (
    "KEY", "TOKEN", "SECRET", "PASSWORD", "PASSWD", "CREDENTIAL",
    "AUTH", "COOKIE", "LICENSE",
)
SECRET_PREFIXES = (
    "ANTHROPIC_", "OPENAI_", "AWS_", "AZURE_", "GCP_", "GOOGLE_", "GITHUB_", "HF_",
)
#: Nombres que contienen un patron pero no son secretos.
SECRET_ALLOWLIST = ("PATHEXT", "PROCESSOR_ARCHITECTURE")


def _is_secret(name: str) -> bool:
    upper = name.upper()
    if upper in SECRET_ALLOWLIST:
        return False
    if upper.startswith(SECRET_PREFIXES):
        return True
    return any(p in upper for p in SECRET_PATTERNS)


def _clean_env() -> dict:
    """Entorno completo menos los secretos: ninguna clave de API llega a Lean."""
    env = {k: v for k, v in os.environ.items() if not _is_secret(k)}
    env["LEANBENCH_SANDBOX"] = "1"
    return env


def execute(candidate_file, budget: Budget = None, cwd=REPO_ROOT) -> ExecutionResult:
    budget = budget or Budget()
    candidate_file = Path(candidate_file)
    # LEANBENCH_LAKE permite apuntar a otro binario (o a uno inexistente en los
    # tests, para comprobar la ruta 'infrastructure_error').
    lake = os.environ.get("LEANBENCH_LAKE", "lake")
    args = [lake, "env", "lean", str(candidate_file)]

    start = time.monotonic()
    try:
        proc = subprocess.Popen(
            args,
            cwd=str(cwd),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=_clean_env(),
            preexec_fn=_preexec(budget) if POSIX else None,
            start_new_session=False,
            creationflags=subprocess.CREATE_NEW_PROCESS_GROUP if sys.platform == "win32" else 0,
        )
    except FileNotFoundError as exc:
        return ExecutionResult(-1, "", "", 0.0, False, False, f"no se encontro 'lake': {exc}")
    except OSError as exc:
        return ExecutionResult(-1, "", "", 0.0, False, False, f"fallo al lanzar lean: {exc}")

    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=budget.verification_seconds)
    except subprocess.TimeoutExpired:
        timed_out = True
        _kill(proc)
        try:
            stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout, stderr = "", ""
    wall = time.monotonic() - start

    exit_code = proc.returncode if proc.returncode is not None else -1
    resource_limited = False
    if POSIX and exit_code < 0:
        sig = -exit_code
        if sig in (signal.SIGXCPU, signal.SIGKILL) and not timed_out:
            resource_limited = True
    if "out of memory" in (stderr or "").lower() or "deep recursion" in (stderr or "").lower():
        resource_limited = True

    return ExecutionResult(
        exit_code=exit_code,
        stdout=stdout or "",
        stderr=stderr or "",
        wall_seconds=wall,
        timed_out=timed_out,
        resource_limited=resource_limited,
    )


def _kill(proc) -> None:
    try:
        if POSIX:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        else:
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                capture_output=True,
                check=False,
            )
    except Exception:
        try:
            proc.kill()
        except Exception:
            pass
