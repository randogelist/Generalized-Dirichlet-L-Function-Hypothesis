@echo off
setlocal EnableExtensions DisableDelayedExpansion
cd /d "%~dp0"
set "GRH_ROOT=%CD%"
if not "%~1"=="" if /i not "%~1"=="full" goto usage
if not "%~2"=="" goto usage
if not defined GRH_LEAN_EXE if defined RH_LEAN_EXE set "GRH_LEAN_EXE=%RH_LEAN_EXE%"
if not defined GRH_LEAN_EXE if defined LEAN_EXE set "GRH_LEAN_EXE=%LEAN_EXE%"
if not defined GRH_LEAN_EXE set "GRH_LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not exist "%GRH_LEAN_EXE%" goto missing_lean
if not defined GRH_MATHLIB_ROOT set "GRH_MATHLIB_ROOT=-"
if not exist ".grh-cache" mkdir ".grh-cache"
if not exist ".grh-cache" goto fail
rem Atomic directory acquisition. A stale lock is never removed automatically.
2>nul mkdir ".grh-cache\writer-lock"
if errorlevel 1 goto locked
rem Never inherit unrecorded import overrides. Child imports are configured by the driver.
set "LEAN_PATH="
set "LEAN_SRC_PATH="
"%GRH_LEAN_EXE%" --run "scripts\cache\Build.lean" "%GRH_ROOT%" "%GRH_LEAN_EXE%" "full" "%GRH_MATHLIB_ROOT%"
set "GRH_EXIT=%ERRORLEVEL%"
rd ".grh-cache\writer-lock" >nul 2>&1
exit /b %GRH_EXIT%
:usage
echo Usage: run.cmd [full]
echo GRH_MATHLIB_ROOT selects an existing Lean 4.33.0 cached Mathlib checkout.
exit /b 2
:missing_lean
echo GOODWORKFLOWFRONTIER::v0_1_0_construction::ERROR=LEAN_4_33_NOT_FOUND_SET_GRH_LEAN_EXE
:fail
echo GOODWORKFLOWFRONTIER::v0_1_0_construction::SUMMARY=FAIL;GRH_PROVED=NO;RH_PROVED=NO
exit /b 2
:locked
echo GOODWORKFLOWFRONTIER::v0_1_0_construction::ERROR=ACTIVE_OR_STALE_WRITER_LOCK
exit /b 2
