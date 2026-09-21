"""Diagnostico: que variante de lanzamiento cuelga a Lean en Windows.

Uso:  python diagnose.py

Compara cuatro formas de invocar `lake env lean` sobre el mismo archivo.
Borralo cuando el diagnostico este hecho.
"""

import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from runner.execute import _clean_env  # noqa: E402

RAIZ = Path(__file__).resolve().parent
ARCHIVO = RAIZ / "tmp_check.lean"
LIMITE = 90

NEW_GROUP = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)


def probar(nombre, archivo, env, creationflags, capturar=True):
    print(f"\n--- {nombre} ---", flush=True)
    inicio = time.monotonic()
    kwargs = dict(cwd=str(RAIZ), text=True, encoding="utf-8", errors="replace",
                  env=env, creationflags=creationflags)
    if capturar:
        kwargs.update(stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        proc = subprocess.Popen(["lake", "env", "lean", str(archivo)], **kwargs)
        salida, error = proc.communicate(timeout=LIMITE)
        seg = time.monotonic() - inicio
        texto = ((salida or "") + (error or "")).strip().replace("\n", " | ")[:200]
        print(f"  OK en {seg:.1f}s  exit={proc.returncode}")
        print(f"  salida: {texto or '(vacia)'}")
    except subprocess.TimeoutExpired:
        proc.kill()
        print(f"  COLGADO: sin terminar en {LIMITE}s")
    except Exception as exc:
        print(f"  ERROR: {type(exc).__name__}: {exc}")


if not ARCHIVO.exists():
    sys.exit(f"falta {ARCHIVO}")

print(f"python {sys.version.split()[0]} | lake en {shutil.which('lake')}")

# 1. Lo mas simple posible: entorno heredado, sin banderas, archivo del proyecto.
probar("1. entorno heredado, sin banderas", ARCHIVO, None, 0)

# 2. Igual, pero con el entorno filtrado del evaluador.
probar("2. entorno filtrado (_clean_env)", ARCHIVO, _clean_env(), 0)

# 3. Igual que 1, pero con el grupo de procesos nuevo.
probar("3. grupo de procesos nuevo", ARCHIVO, None, NEW_GROUP)

# 4. Igual que 1, pero con el archivo en la carpeta temporal (como en pytest).
tmp = Path(tempfile.mkdtemp(prefix="leanbench_diag_"))
copia = tmp / "Candidate.lean"
shutil.copy(ARCHIVO, copia)
probar("4. archivo en carpeta temporal", copia, None, 0)

# 5. Igual que 1, pero sin capturar la salida (sin tuberias).
probar("5. sin tuberias (salida directa a la consola)", ARCHIVO, None, 0, capturar=False)

print("\nLa primera que diga COLGADO es la causa.")
