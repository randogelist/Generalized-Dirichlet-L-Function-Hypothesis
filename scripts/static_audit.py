#!/usr/bin/env python3
"""Check source identity, import closure and audit coverage; does not run Lean."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
errors = []


def require(ok, message):
    if not ok:
        errors.append(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text):
    """Mask strings and nested comments while retaining newlines."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        char, pair = text[i], text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                out.append('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                i += 1
        elif string:
            if char == '\\' and i + 1 < len(text):
                out.append('  ')
                i += 2
            else:
                if char == '"':
                    string = False
                out.append('\n' if char == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.append('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.append(' ' * (end - i))
            i = end
        elif char == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(char)
            i += 1
    require(depth == 0 and not string, 'Unclosed source comment or string')
    return ''.join(out)


sources = json.loads((ROOT / 'provenance/source-files.json').read_text())
new_sources = json.loads((ROOT / 'provenance/new-source-files.json').read_text())
historical = json.loads((ROOT / 'provenance/historical-evidence.json').read_text())
theorems = json.loads((ROOT / 'provenance/theorem-audit.json').read_text())
status = json.loads((ROOT / 'provenance/status.json').read_text())
require(len(sources) == 25, 'Expected 25 original mathematical modules')
source_paths = {entry['path'] for entry in sources}
require(len(source_paths) == len(sources), 'Duplicate source manifest path')
for entry in sources:
    path = ROOT / entry['path']
    require(path.is_file(), f'Missing original source: {path}')
    if path.is_file():
        require(digest(path) == entry['sha256'], f'Original source changed: {entry["path"]}')
        require(path.stat().st_size == entry['bytes'], f'Source byte count: {entry["path"]}')
    require(entry['unchanged'] is True and entry['native_replay'] == 'NOT_RUN',
            f'Unexpected source provenance claim: {entry["path"]}')
require(len(new_sources) == 2, 'Expected first-factor source and focused audit additions')
new_paths = {entry['path'] for entry in new_sources}
require(new_paths == {'RHToGRHFirstFactorFrontier.lean', 'GRHFinal/FirstFactorAudit.lean'},
        'Unexpected new-source manifest paths')
require(not (source_paths & new_paths), 'New sources overlap preserved originals')
for entry in new_sources:
    path = ROOT / entry['path']
    require(path.is_file(), f'Missing new source: {entry["path"]}')
    if path.is_file():
        require(digest(path) == entry['sha256'], f'New source hash: {entry["path"]}')
        require(path.stat().st_size == entry['bytes'], f'New source byte count: {entry["path"]}')
    require(entry['unchanged_from_reviewed_candidate'] is True and
            entry['native_verification'] == 'NOT_RUN',
            f'Unexpected new-source verification claim: {entry["path"]}')
for notice in historical['notices']:
    path = ROOT / notice['path']
    require(path.is_file(), f'Missing historical notice: {path}')
    if path.is_file():
        require(digest(path) == notice['sha256'], f'Historical notice changed: {notice["path"]}')

plan = [line.strip() for line in (ROOT / 'build-modules.txt').read_text().splitlines()
        if line.strip() and not line.lstrip().startswith('#')]
require(len(plan) == len(set(plan)) == 28, 'Expected 28 distinct build modules')
require(len({p.casefold() for p in plan}) == len(plan), 'Windows module case collision')
require({p + '.lean' for p in plan} == source_paths | new_paths | {'GRHFinal/Audit.lean'},
        'Build plan differs from original closure, new first-factor sources, and main audit')
seen, external_imports = set(), set()
for module in plan:
    require(bool(re.fullmatch(r'[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*', module)),
            f'Invalid module name: {module}')
    path = ROOT / (module + '.lean')
    require(path.is_file(), f'Missing build module: {module}')
    if not path.is_file():
        continue
    code = lean_code(path.read_text())
    bad = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', code)
    require(not bad, f'Forbidden proof tokens in {module}: {bad}')
    for dependency in re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', code, re.M):
        dep = dependency.replace('.', '/')
        if (ROOT / (dep + '.lean')).is_file():
            require(dep in seen, f'{module}: import {dep} absent or out of order')
        else:
            external_imports.add(dependency)
            require(dependency == 'Mathlib' or dependency.startswith('Mathlib.'),
                    f'{module}: unresolved non-Mathlib import {dependency}')
    seen.add(module)

audit_modules = [module for module in plan if module.endswith('Audit')]
require(audit_modules == ['GRHFinal/FirstFactorAudit', 'GRHFinal/Audit'],
        'Expected focused first-factor audit followed by main audit')
audit_code = '\n'.join(lean_code((ROOT / (module + '.lean')).read_text())
                       for module in audit_modules)
printed = re.findall(r'^\s*#print\s+axioms\s+(\S+)', audit_code, re.M)
records = theorems['theorems']
require(len(printed) == len(set(printed)) == len(records) == 136,
        'Expected 136 distinct prepared axiom reports')
require(set(printed) == {x['name'] for x in records}, 'Axiom audit and theorem index differ')
for entry in records:
    path = ROOT / entry['source_path']
    require(path.is_file(), f'Theorem source missing: {entry["name"]}')
    if path.is_file():
        require(digest(path) == entry['source_sha256'], f'Theorem hash: {entry["name"]}')
        require(entry['declaration_header'] in path.read_text(), f'Theorem signature: {entry["name"]}')
    require(entry['native_verification'] == 'NOT_RUN', f'Unsupported native claim: {entry["name"]}')
required_endpoints = {
    'RHToGRHFrontier.RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT',
    'RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT',
    'RHToGRHCrossCayley.RH_IFF_GRH_OF_CROSS_CAYLEY_TRANSFER',
    'CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH',
    'CayleyGRHStrong.TEXTBOOK_ALL_CHARACTERS_GRH_A_TIER_ATLAS',
    'RHToGRHCompletedLFactor.COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH',
    'RHToGRHFirstFactor.FIRST_FACTOR_IFF_FOUR_FACTORS',
    'RHToGRHFirstFactor.FIRST_FACTOR_IFF_RH_IMPLIES_GRH',
}
require(required_endpoints <= set(printed), 'Required endpoint omitted from axiom audit')
require(theorems['native_status'] == 'NOT_RUN', 'Unsupported native theorem audit status')
require(status['native_build'] == status['native_axiom_audit'] == 'NOT_RUN',
        'Initial assembly must not claim a native pass')
require(status['rh_to_grh_lift'] == 'OPEN', 'Open transfer premise was changed')
require(status['first_completed_l_factor_nonvanishing_under_rh'] == 'OPEN' and
        status['first_factor_reduction'] == 'SOURCE_PROOF_NATIVE_NOT_RUN',
        'First-factor reduction was presented as a discharged or verified input')
require(status['unconditional_rh_iff_grh_proved'] is False and
        status['rh_proved'] is False and status['grh_proved'] is False,
        'Unsupported unconditional theorem claim')
workflow = status['workflow_definition']
require(digest(ROOT / workflow['path']) == workflow['sha256'], 'Workflow source hash mismatch')
require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0',
        'Unexpected Lean version')
runner = (ROOT / 'run.cmd').read_bytes()
require(b'\n' not in runner.replace(b'\r\n', b''), 'Windows runner requires CRLF')
require([p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.cmd')] == ['run.cmd'],
        'Expected one native CMD entry point')

for doc in [ROOT / 'README.md', *sorted((ROOT / 'docs').glob('*.md'))]:
    for target in re.findall(r'\]\(([^)]+)\)', doc.read_text()):
        target = target.split('#', 1)[0]
        if not target or '://' in target:
            continue
        require((doc.parent / target).is_file(), f'{doc.name}: broken link {target}')

report = {
    'kind': 'STATIC_SOURCE_IDENTITY_AND_IMPORT_CHECKS_ONLY_NOT_LEAN',
    'status': 'FAIL' if errors else 'PASS',
    'original_source_modules_checked': len(sources),
    'new_source_files_checked': len(new_sources),
    'historical_notices_checked': len(historical['notices']),
    'active_build_modules': len(plan),
    'prepared_axiom_reports': len(printed),
    'prepared_explicit_signature_checks': len(re.findall(r'^\s*#check\s+@', audit_code, re.M)),
    'external_imports': sorted(external_imports),
    'active_source_sha256': {m + '.lean': digest(ROOT / (m + '.lean')) for m in plan},
    'reviewed_tooling_sha256': {p: digest(ROOT / p) for p in
                              ['run.cmd', 'scripts/cache/Build.lean', 'scripts/static_audit.py', 'docs/BUILD.md']},
    'native_build': 'NOT_RUN', 'native_axiom_audit': 'NOT_RUN',
    'rh_to_grh_lift': 'OPEN', 'unconditional_rh_iff_grh_proved': False,
    'first_completed_l_factor_nonvanishing_under_rh': 'OPEN',
    'errors': errors,
}
(ROOT / 'provenance/static-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if not k.endswith('_sha256')}, indent=2))
sys.exit(bool(errors))
