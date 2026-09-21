# Archivos que debes BORRAR a mano

No puedo borrar archivos en tu disco desde aqui. Borra estos antes de commitear:

| Archivo | Por que |
| ------- | ------- |
| `Mathlib.lean` | Es un Mathlib falso (un archivo vacio con un comentario). Mientras exista, `import Mathlib` no importa Mathlib y el evaluador miente. |
| `LeanBench/Basic.lean` | Plantilla de `lake new` (`def hello := "world"`), ya no se usa. |
| `problems/nat_add_zero_001.json` | Sustituido por `problems/nat_add_zero_001/problem.json`. |
| `problems/statement.txt` | Sustituido por `problems/<id>/statement.lean`. |
| `references/nat_add_zero_001.lean` | Sustituido por `references/nat_add_zero_001.proof.lean`. |
| `.github/workflows/update.yml` | Actualiza dependencias solo: rompe la regla de versiones fijadas. |
| `.github/workflows/create-release.yml` | Plantilla del generador de proyectos. |
| `runs/attempt_temp/` | Resto de una prueba manual; `runs/` ya esta en `.gitignore`. |
| `runner/__pycache__/`, `tests/__pycache__/` | Cache de Python. |

En PowerShell:

```powershell
cd C:\Users\Usuario\Downloads\leanbench\LeanBench
Remove-Item Mathlib.lean, LeanBench\Basic.lean, problems\nat_add_zero_001.json, `
  problems\statement.txt, references\nat_add_zero_001.lean, `
  .github\workflows\update.yml, .github\workflows\create-release.yml -Force
Remove-Item runs, runner\__pycache__, tests\__pycache__ -Recurse -Force
```

Despues:

```powershell
git init            # si aun no es un repositorio
lake update mathlib
Copy-Item .lake\packages\mathlib\lean-toolchain lean-toolchain -Force
lake exe cache get
lake build
python scripts\validate_metadata.py
pytest -q
```
