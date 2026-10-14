#!/usr/bin/env python3
"""Build local Lean import dependencies using the existing offline cache.

Examples:
  python3 build_local.py Matmul.RectangularPrograms --jobs 2
  python3 build_local.py --all -DmaxRecDepth=10000

This runner never executes Lake, downloads packages, or writes to the shared
toolchain/mathlib installation. Lean output and logs stay in .lake/build.

Optional environment variables (shared with check_lean.py):
  MATMUL_LEAN       Actual executable from an existing Lean toolchain.
  MATMUL_PACKAGES   Existing Lake packages directory with compiled libraries.
  MATMUL_LEAN_PATH  Compiled library directories separated by os.pathsep.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import time

import check_lean as local_env

ROOT = local_env.ROOT
BUILD = local_env.BUILD
BUILD_ROOT = ROOT / '.lake/build'
LOGS = BUILD_ROOT / 'logs'
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
IMPORT_START = re.compile(r'^\s*(?:(?:public|private)\s+)?import\s+', re.MULTILINE)


class BuildError(Exception):
    pass


def uncomment(text: str) -> str:
    """Replace nested Lean comments and strings with whitespace, keeping lines."""
    result = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i + 2] = [' ', ' ']
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                result[i:i + 2] = [' ', ' ']
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    result[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                result[i:i + 2] = [' ', '\n' if text[i + 1] == '\n' else ' ']
                i += 2
            else:
                if text[i] != '\n':
                    result[i] = ' '
                if text[i] == '"':
                    quoted = False
                i += 1
        elif text.startswith('/-', i):
            result[i:i + 2] = [' ', ' ']
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end == -1 else end
            result[i:end] = [' '] * (end - i)
            i = end
        elif text[i] == '"':
            result[i] = ' '
            quoted = True
            i += 1
        else:
            i += 1
    return ''.join(result)


def imports(path: Path) -> tuple[str, ...]:
    """Read ordinary and public/private imports, including indented continuations."""
    source = uncomment(path.read_text())
    found: list[str] = []
    for match in IMPORT_START.finditer(source):
        position = match.end()
        line_end = source.find('\n', position)
        line_end = len(source) if line_end == -1 else line_end
        line = source[position:line_end]
        for name in line.split():
            if not MODULE_NAME.fullmatch(name):
                raise BuildError(f'Unsupported import token {name!r} in {path}')
            found.append(name)
        # Lean permits one import command to continue on indented module lines.
        position = line_end + 1
        while position < len(source):
            end = source.find('\n', position)
            end = len(source) if end == -1 else end
            continuation = source[position:end]
            tokens = continuation.split()
            if not continuation.startswith((' ', '\t')) or not tokens:
                break
            if not all(MODULE_NAME.fullmatch(token) for token in tokens):
                break
            # These can start a subsequent command, never an import module name.
            if tokens[0] in {'namespace', 'section', 'end', 'open', 'variable',
                             'noncomputable', 'set_option', 'def', 'theorem',
                             'lemma', 'example', 'public', 'private', 'import'}:
                break
            found.extend(tokens)
            position = end + 1
    return tuple(dict.fromkeys(found))


def module_path(name: str, suffix: str) -> Path:
    if not MODULE_NAME.fullmatch(name):
        raise BuildError(f'Unsupported module name: {name!r}')
    return Path(*name.split('.')).with_suffix(suffix)


def target_name(value: str) -> str:
    candidate = Path(value)
    if candidate.suffix == '.lean' or candidate.is_absolute() or '/' in value:
        path = candidate if candidate.is_absolute() else Path.cwd() / candidate
        if not path.exists() and not candidate.is_absolute():
            path = ROOT / candidate
        try:
            relative = path.resolve().relative_to(ROOT)
        except ValueError as error:
            raise BuildError(f'Target must be inside {ROOT}: {value}') from error
        if relative.suffix != '.lean':
            raise BuildError(f'Target must be a Lean source: {value}')
        name = '.'.join(relative.with_suffix('').parts)
    else:
        name = value
    module_path(name, '.lean')
    if not (ROOT / module_path(name, '.lean')).is_file():
        raise BuildError(f'Local source does not exist: {name}')
    return name


@dataclass(frozen=True)
class Module:
    name: str
    source: Path
    local_imports: tuple[str, ...]
    external_imports: tuple[Path, ...]


def graph(targets: list[str], env: dict[str, str],
          config: local_env.Configuration) -> dict[str, Module]:
    search_paths = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep) if p]
    # Lean's built-in Init/Lean/Std modules live in its own library directory.
    search_paths.append(config.lean.parent.parent / 'lib/lean')
    modules: dict[str, Module] = {}
    visiting: list[str] = []

    def visit(name: str) -> None:
        if name in modules:
            return
        if name in visiting:
            raise BuildError('Cyclic local imports: ' + ' -> '.join([*visiting, name]))
        visiting.append(name)
        source = ROOT / module_path(name, '.lean')
        local, external = [], []
        for imported in imports(source):
            local_source = ROOT / module_path(imported, '.lean')
            if local_source.is_file():
                local.append(imported)
                visit(imported)
            else:
                relative = module_path(imported, '.olean')
                cached = next((p / relative for p in search_paths
                               if (p / relative).is_file()), None)
                if cached is None:
                    raise BuildError(f'{name} imports {imported}, but neither a local '
                                     'source nor a cached .olean was found. '
                                     'No packages will be downloaded.')
                external.append(cached)
        visiting.pop()
        modules[name] = Module(name, source, tuple(local), tuple(external))

    for target in targets:
        visit(target)
    return modules


def artifact_fingerprint(path: Path) -> dict:
    stat = path.stat()
    return {'path': str(path), 'size': stat.st_size, 'mtime_ns': stat.st_mtime_ns}


def compile_module(module: Module, options: list[str], env: dict[str, str],
                   config: local_env.Configuration, force: bool) -> tuple[str, bool, str]:
    relative = module_path(module.name, '.olean')
    output = BUILD / relative
    metadata = output.with_suffix('.olean.build.json')
    log_path = LOGS / module_path(module.name, '.log')
    output.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    signature = {
        'source_sha256': hashlib.sha256(module.source.read_bytes()).hexdigest(),
        'lean': artifact_fingerprint(config.lean),
        'options': options,
        'dependencies': [artifact_fingerprint(path) for path in
                         [*(BUILD / module_path(dep, '.olean')
                            for dep in module.local_imports), *module.external_imports]],
    }
    if not force and output.is_file() and metadata.is_file():
        try:
            if json.loads(metadata.read_text()) == signature:
                return module.name, True, 'cached'
        except (OSError, ValueError):
            pass
    temporary_root = BUILD_ROOT / 'tmp'
    temporary_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='lean-', dir=temporary_root) as temporary:
        temporary_path = Path(temporary)
        temporary_output = temporary_path / relative
        temporary_output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(config.lean), '-R', str(ROOT), *options,
                   '-o', str(temporary_output), str(module.source)]
        started = time.monotonic()
        result = subprocess.run(command, env=env, cwd=ROOT, capture_output=True, text=True)
        elapsed = time.monotonic() - started
        log = (f'$ {shlex.join(command)}\n'
               f'Exit: {result.returncode}; elapsed: {elapsed:.2f}s\n\n'
               f'{result.stdout}{result.stderr}')
        log_path.write_text(log)
        if result.returncode:
            return module.name, False, f'failed ({elapsed:.2f}s); log: {log_path}'
        if not temporary_output.is_file():
            return module.name, False, f'Lean emitted no .olean; log: {log_path}'
        # Recent Lean versions can emit additional .olean.server/private artifacts.
        for produced in temporary_path.rglob('*'):
            if produced.is_file():
                destination = BUILD / produced.relative_to(temporary_path)
                destination.parent.mkdir(parents=True, exist_ok=True)
                produced.replace(destination)
        metadata.write_text(json.dumps(signature, indent=2) + '\n')
    return module.name, True, f'built ({elapsed:.2f}s)'


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('targets', nargs='*', help='local module names or .lean paths')
    parser.add_argument('--all', action='store_true', help='build every local Lean source')
    parser.add_argument('--jobs', type=int, default=1, choices=range(1, 5))
    parser.add_argument('--force', action='store_true', help='ignore incremental build signatures')
    parser.add_argument('-D', dest='defines', action='append', default=[], metavar='NAME=VALUE')
    parser.add_argument('--maxRecDepth', '--max-rec-depth', dest='max_rec_depth', type=int)
    parser.add_argument('--lean-arg', action='append', default=[], metavar='ARG',
                        help='extra Lean flag; use --lean-arg=-T100000 for flags starting with -')
    args = parser.parse_args()
    try:
        config = local_env.configuration()
        targets = [target_name(value) for value in args.targets]
        if args.all:
            targets.extend('.'.join(path.relative_to(ROOT).with_suffix('').parts)
                           for path in ROOT.rglob('*.lean') if '.lake' not in path.parts)
        targets = list(dict.fromkeys(targets))
        if not targets:
            parser.error('provide a target or --all')
        env = config.environment()
        modules = graph(targets, env, config)
        options = ['-D' + define for define in args.defines]
        if args.max_rec_depth is not None:
            options.append('-DmaxRecDepth=' + str(args.max_rec_depth))
        options.extend(args.lean_arg)
        print(f'Building {len(modules)} local modules using cached dependencies '
              f'({args.jobs} worker(s)).', flush=True)
        pending, completed, failed = set(modules), set(), False
        active = {}
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            while pending or active:
                if not failed:
                    ready = sorted(name for name in pending
                                   if set(modules[name].local_imports) <= completed)
                    for name in ready[:args.jobs - len(active)]:
                        future = executor.submit(compile_module, modules[name], options,
                                                 env, config, args.force)
                        active[future] = name
                        pending.remove(name)
                if not active:
                    if failed:
                        break
                    raise BuildError('No buildable modules remain; dependency graph is inconsistent.')
                finished, _ = wait(active, return_when=FIRST_COMPLETED)
                for future in finished:
                    name = active.pop(future)
                    try:
                        _, success, message = future.result()
                    except Exception as error:
                        success, message = False, f'runner error: {error}'
                    print(f'{name}: {message}', flush=True)
                    if success:
                        completed.add(name)
                    else:
                        failed = True
        if failed:
            print(f'Build failed; {len(pending)} modules were not started.', file=sys.stderr)
            return 1
        print(f'All {len(completed)} local modules passed. Artifacts: {BUILD}', flush=True)
        return 0
    except (BuildError, local_env.ConfigurationError, OSError) as error:
        print(f'Build error: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
