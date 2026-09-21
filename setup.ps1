<#
  LeanBench - puesta a punto de v0.1

  Uso (PowerShell, dentro de la carpeta LeanBench):

      powershell -ExecutionPolicy Bypass -File .\setup.ps1

  Que hace:
    1. Aparta los archivos sobrantes a _to_delete\  (no borra nada: los mueve).
    2. Coloca el workflow de CI en .github\workflows\.
    3. Inicializa Git si hace falta.
    4. Trae Mathlib de verdad, alinea lean-toolchain, cache y build.
    5. Valida metadatos y ejecuta los tests.

  El paso 4 descarga varios GB la primera vez. Puede tardar 10-30 minutos.
#>

$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot

function Paso($n, $texto) {
    Write-Host ""
    Write-Host "=== $n. $texto ===" -ForegroundColor Cyan
}

# ---------------------------------------------------------------- 1. limpieza
Paso 1 "Apartando archivos sobrantes a _to_delete\"

$papelera = Join-Path $PSScriptRoot "_to_delete"
New-Item -ItemType Directory -Force -Path $papelera | Out-Null

$sobrantes = @(
    "Mathlib.lean",                        # Mathlib FALSO: es lo mas importante
    "LeanBench\Basic.lean",                # plantilla de lake new
    "problems\nat_add_zero_001.json",      # sustituido por problems\<id>\problem.json
    "problems\statement.txt",              # sustituido por problems\<id>\statement.lean
    "references\nat_add_zero_001.lean",    # sustituido por *.proof.lean
    ".github\workflows\update.yml",        # actualiza dependencias: rompe el paso 3
    ".github\workflows\create-release.yml",# plantilla del generador
    "runs",
    "runner\__pycache__",
    "tests\__pycache__"
)

foreach ($item in $sobrantes) {
    if (Test-Path $item) {
        $destino = Join-Path $papelera ($item -replace '\\', '__')
        if (Test-Path $destino) { Remove-Item $destino -Recurse -Force }
        Move-Item -Path $item -Destination $destino -Force
        Write-Host "  apartado: $item"
    } else {
        Write-Host "  (ya no estaba) $item" -ForegroundColor DarkGray
    }
}

# Los .olean del Mathlib falso deben desaparecer o seguiran ocultando al real.
if (Test-Path ".lake\build") {
    Remove-Item ".lake\build" -Recurse -Force
    Write-Host "  borrado: .lake\build (contenia el Mathlib.olean falso)"
}

# ------------------------------------------------------------------- 2. CI
Paso 2 "Colocando el workflow de CI"

New-Item -ItemType Directory -Force -Path ".github\workflows" | Out-Null
if (Test-Path "lean_action_ci.yml") {
    Move-Item -Path "lean_action_ci.yml" `
              -Destination ".github\workflows\lean_action_ci.yml" -Force
    Write-Host "  .github\workflows\lean_action_ci.yml"
} else {
    Write-Host "  (no encontre lean_action_ci.yml en la raiz)" -ForegroundColor Yellow
}

# ------------------------------------------------------------------ 3. Git
Paso 3 "Git"

if (-not (Test-Path ".git")) {
    git init | Out-Null
    Write-Host "  repositorio inicializado"
} else {
    Write-Host "  ya es un repositorio"
}

# --------------------------------------------------------------- 4. Mathlib
Paso 4 "Mathlib (esto tarda: descarga varios GB la primera vez)"

lake update mathlib
if ($LASTEXITCODE -ne 0) { throw "lake update fallo" }

$toolchain = ".lake\packages\mathlib\lean-toolchain"
if (Test-Path $toolchain) {
    Copy-Item $toolchain "lean-toolchain" -Force
    Write-Host "  lean-toolchain alineado con Mathlib: $(Get-Content lean-toolchain)"
} else {
    throw "no encontre $toolchain"
}

lake exe cache get
if ($LASTEXITCODE -ne 0) { Write-Host "  aviso: 'cache get' fallo; el build sera muy lento" -ForegroundColor Yellow }

lake build
if ($LASTEXITCODE -ne 0) { throw "lake build fallo" }

# ------------------------------------------------------- 5. validacion y tests
Paso 5 "Validacion y tests"

python -m pip install --quiet pytest
python scripts\validate_metadata.py
if ($LASTEXITCODE -ne 0) { throw "la validacion de metadatos fallo" }

python -m pytest -q
if ($LASTEXITCODE -ne 0) { throw "los tests fallaron" }

# ------------------------------------------------------------------ 6. listo
Paso 6 "Listo"

Write-Host ""
Write-Host "Circuito completo verificado." -ForegroundColor Green
Write-Host "Revisa _to_delete\ y borralo cuando estes conforme."
Write-Host ""
Write-Host "Siguiente:" -ForegroundColor Cyan
Write-Host "  python -m runner.run_eval --method reference --split dev"
Write-Host "  python -m runner.run_eval --method portfolio --split dev"
Write-Host "  python -m runner.report runs\<run_id>"
