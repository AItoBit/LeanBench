# LeanBench v0.1

Evaluador de pruebas en Lean 4: recibe intentos de demostración, los compila con
Lean, audita sus axiomas y genera un informe reproducible.

**Qué mide esta versión:** dado un enunciado formal fijo, ¿puede un sistema
producir una prueba que Lean acepte dentro de un presupuesto determinado?

No evalúa traducción de lenguaje natural a Lean. Eso es otra tarea y necesita
otra evaluación.

---

## 1. Instalación

Requisitos: Git, elan/Lean 4, Lake, Python 3.11+ y VS Code con la extensión
Lean 4 (opcional pero recomendable).

```bash
# 1. Dependencias de Lean (Mathlib de verdad, no un módulo vacío)
lake update mathlib

# 2. Alinear la versión de Lean con la que exige Mathlib
#    (copia .lake/packages/mathlib/lean-toolchain sobre ./lean-toolchain)
cp .lake/packages/mathlib/lean-toolchain lean-toolchain

# 3. Caché precompilada y construcción
lake exe cache get
lake build

# 4. Comprobación
lake env lean --version
python scripts/validate_metadata.py
pytest -q
```

**Terminado cuando** `pytest -q` pasa sin omitir `tests/test_lean_integration.py`,
es decir cuando las cinco referencias compilan y superan la auditoría.

> `lake update` **solo** se ejecuta fuera de una evaluación. Si actualizas Lean o
> Mathlib, publica una versión nueva del benchmark y revalida los problemas.

---

## 2. Estructura

| Ruta | Contenido |
| ---- | --------- |
| `LeanBench/Definitions/` | Definiciones compartidas. Sin soluciones. |
| `problems/<id>/` | `problem.json` (metadatos) y `statement.lean` (enunciado). |
| `references/` | Soluciones de referencia: **solo el cuerpo de la prueba**. |
| `splits/` | Listas de problemas por uso (`dev`, `test`). |
| `runner/` | Generación de archivos, ejecución, auditoría e informes. |
| `baselines/` | Tácticas con las que comparar. |
| `tests/` | Tests del evaluador. |
| `scripts/` | Validación de metadatos. |
| `reports/` | Informes publicados. |
| `runs/` | Intentos y logs. Excluida de Git. |

Las referencias guardan únicamente la prueba, así que pasan por la **misma
plantilla** que un agente: si la plantilla se rompe, CI se entera.

---

## 3. Uso

```bash
# Línea base: las propias soluciones de referencia
python -m runner.run_eval --method reference --split dev

# Una táctica suelta
python -m runner.run_eval --method tactic:simp --split dev

# Cascada de tácticas con presupuesto total
python -m runner.run_eval --method portfolio --split dev

# Modelo: intentos independientes
python -m runner.run_eval --method model --attempts 4 --split dev

# Modelo: reparación usando el error de Lean
python -m runner.run_eval --method repair --attempts 4 --split dev

# Informe
python -m runner.report runs/<run_id>
```

Cada ejecución escribe `runs/<run_id>/` con `run_config.json` (commit, versiones
de Lean y Mathlib, hash del conjunto de problemas, presupuestos, hardware,
fecha, configuración del modelo), `results.jsonl` (una línea por intento),
`generations/` (prompt completo, respuesta original, parámetros, tokens) y
`attempts/` (archivo generado y salida de Lean).

Para usar un modelo: `pip install anthropic` y `export ANTHROPIC_API_KEY=...`.
La clave nunca entra en el proceso de verificación: `execute.py` limpia el
entorno antes de lanzar Lean.

---

## 4. Anatomía de un problema

| Componente | Quién lo controla |
| ---------- | ----------------- |
| Contexto (`import Mathlib`, definiciones) | el evaluador |
| Enunciado (`theorem candidate ... :=`) | el evaluador |
| Prueba (`by simp`) | el participante |

El participante entrega **solo** el cuerpo de la prueba. `runner/render.py` lo
sanea, lo inserta detrás del `:=` y añade `#print axioms candidate`.

---

## 5. Política de auditoría

* Se rechaza `sorryAx`.
* Se rechaza cualquier axioma nuevo introducido para resolver el problema.
* Se aceptan los fundamentos estándar: `propext`, `Classical.choice`, `Quot.sound`.
* Se rechazan `native_decide`, `implemented_by`, `unsafe` y las `set_option` que
  afectan a la confianza (solo se permiten `maxHeartbeats`, `maxRecDepth`,
  `synthInstance.maxHeartbeats`).

Buscar la palabra `sorry` no basta: se leen las dependencias reales de la
declaración final. Un código de salida 0 tampoco basta, porque Lean acepta
declaraciones con `sorry` emitiendo solo una advertencia.

---

## 6. Estados de resultado

| Estado | Significado |
| ------ | ----------- |
| `accepted` | Prueba válida del enunciado esperado y auditoría aprobada. |
| `compile_error` | Error de sintaxis, tipos o tácticas. |
| `timeout` | Se agotó el tiempo permitido. |
| `resource_limit` | Se superó otro límite de recursos. |
| `audit_rejected` | Axiomas o modificaciones no permitidas. |
| `infrastructure_error` | Falló el entorno o el evaluador. |

Los fallos de infraestructura se informan aparte y nunca se convierten en
fallos matemáticos.

---

## 7. Métricas del informe

* **Éxito al primer intento** (métrica principal).
* **Resuelto dentro de k intentos**, definido como:
  `problemas con algún intento aceptado de índice ≤ k / problemas evaluados`,
  indicando siempre si los intentos eran independientes o de reparación.
* Resultados por tema, tiempos de generación y verificación por separado,
  tokens, coste y distribución de errores.

No se usa la etiqueta `pass@k` sin definir su cálculo. Con cinco problemas, los
resultados son una comprobación del sistema, no evidencia de superioridad
general.

---

## 8. Aislamiento (limitación conocida)

Lean admite metaprogramación: una prueba propuesta por un agente es **código
ejecutable**. `runner/execute.py` aplica, en POSIX, límites de CPU, memoria y
procesos con `setrlimit`, ejecuta en un grupo de procesos propio, mata a todos
los hijos al agotarse el tiempo y limpia el entorno de secretos.

**Esto no es un sandbox.** En Windows solo se aplica el tiempo máximo
(`isolation: timeout_only` en el informe). Antes de evaluar respuestas de
modelos en serio, ejecuta dentro de un contenedor con dependencias en solo
lectura, sin red, con directorio temporal propio y sin acceso a `references/`.
Las llamadas a la API se hacen fuera del entorno de verificación.

El saneado de `render.py` es léxico. La versión robusta debe analizar la
respuesta con el parser de Lean como un único término de prueba y comprobar que
la declaración final tiene el tipo esperado.

---

## 9. Splits

Con cinco problemas todo es **desarrollo** (`splits/dev.txt`). `splits/test.txt`
está vacío a propósito y se congelará al ampliar la colección.

Reglas al crecer: las variantes de un mismo problema (`family_id`) se mantienen
en un único conjunto, `test` se congela antes de comparar métodos, y se documenta
la posible coincidencia con datos públicos. Reservar problemas no garantiza que
un modelo preentrenado no los haya visto; es una limitación declarada.

---

## 10. Estado de v0.1 y siguiente paso

Listo: cinco problemas revisados, cinco referencias auditadas, versiones
fijadas, evaluador con límites y estados, tests que detectan pruebas inválidas,
baselines de tácticas, informe reproducible y CI.

Pendiente: auditor escrito en Lean con salida estructurada, sandbox real,
ampliar a 20 problemas y responder a la pregunta:

> ¿Cuánto mejora la reparación basada en errores de Lean frente a generar
> nuevos intentos, con el mismo presupuesto?

---

## 11. Importar formalizaciones IMO

```bash
# 1. Clasificar e importar (Python puro, no necesita Lean)
python scripts/import_imo.py C:\ruta\a\IMO-main\IMO-main
#    -> imports/imo/<id>/  +  imports/imo/REPORT.md

# 2. Comprobar en CI que las referencias compilan con el Mathlib fijado
#    (workflow manual: ci/check_imports.yml movido a .github/workflows/)

# 3. Revisar la formalizacion a mano y promoverla al benchmark
python scripts/promote.py imo_1959_p1 --split dev --reviewer pineapple
```

Categorias del importador:

| Cat. | Significado | Que pasa |
| ---- | ----------- | -------- |
| A | Solo el teorema | Se importa |
| B | Necesita definiciones previas | Se importa con ellas como contexto confiable |
| C | Usa lemas auxiliares propios | Se importa en modo archivo completo |
| X | `sorry`, `axiom`, `native_decide` o sin teorema principal | Excluido |

La marca `core_like` indica que el texto habla de un nucleo, caso particular o
version parcial. Lean acepta la prueba, pero puede no ser el problema IMO
completo: revisalo antes de promoverlo y nunca lo cuentes como "IMO resuelto"
sin decirlo.

Nada importado entra en el benchmark sin `formalization_reviewed: true`.

### Modo archivo completo (`"mode": "aux"`)

El participante puede entregar, ademas del cuerpo de la prueba, lemas
auxiliares. El archivo se monta asi, y solo lo marcado es del participante:

```
imports                      (confiable)
context.lean                 (confiable: defs, open, namespace)
lemas auxiliares             <- participante
enunciado                    (confiable)
cuerpo de la prueba          <- participante
epilogo + #print axioms      (confiable)
```

En los lemas solo se admiten `theorem`/`lemma` (con `private`, docstrings,
`@[simp]`, `open X in`, `omit h in`). Se rechaza todo lo que podria cambiar
como se elabora el enunciado: `def`, `instance`, `notation`, `macro`,
`include`, `open` sin `in`, otros atributos, y cualquier lema que se llame
como un identificador del enunciado.

Un modelo responde en este formato:

```
-- LEMAS
lemma ayuda ... := ...
-- PRUEBA
by
  ...
```
