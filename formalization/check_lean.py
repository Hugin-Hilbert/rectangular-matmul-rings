#!/usr/bin/env python3
"""Check Lean sources against an existing toolchain and compiled dependency cache.

No Lake update, package installation, toolchain installation, or downloads.
All newly generated artifacts stay under this project's formalization folder.

Optional environment variables:
  MATMUL_LEAN       Path to the actual Lean executable, not an elan shim.
  MATMUL_PACKAGES   Directory containing existing Lake packages.
  MATMUL_LEAN_PATH  Compiled library directories, separated by os.pathsep.

Otherwise, use an installed toolchain matching lean-toolchain or an actual Lean
binary on PATH, and .lake/packages in this folder or its parent. The original
development machine's installed toolchain and cache remain a final fallback.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / '.lake/build/lib/lean'
_LOCAL_LEAN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.0-rc1/bin/lean'
_LOCAL_PACKAGES = Path.home() / 'leanWorkflow/leanflowVerify/.lake/packages'


class ConfigurationError(Exception):
    """An explicit path is invalid or an installed dependency is unavailable."""


def _directory(value: str, variable: str) -> Path:
    if not value.strip():
        raise ConfigurationError(f'{variable} must not be empty.')
    path = Path(value).expanduser().resolve()
    if not path.is_dir():
        raise ConfigurationError(f'{variable} directory does not exist: {path}')
    return path


def _actual_lean(path: Path) -> Path | None:
    path = path.expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        return None
    # Invoking an elan shim could install a toolchain. Resolve installed binaries
    # directly instead, even when PATH points to ~/.elan/bin/lean.
    if path.name in {'elan', 'elan.exe'}:
        return None
    elan_home = Path(os.environ.get('ELAN_HOME', '~/.elan')).expanduser().resolve()
    if path.parent == elan_home / 'bin':
        return None
    # Elan also installs hardlinks, whose resolved basename remains "lean".
    for name in ('elan', 'elan.exe'):
        sibling = path.parent / name
        try:
            if sibling.is_file() and path.samefile(sibling):
                return None
        except OSError:
            continue
    return path


def _lean_executable() -> Path:
    if 'MATMUL_LEAN' in os.environ:
        value = os.environ['MATMUL_LEAN']
        if not value.strip():
            raise ConfigurationError('MATMUL_LEAN must not be empty.')
        lean = _actual_lean(Path(value))
        if lean is None:
            raise ConfigurationError(
                'MATMUL_LEAN must name an existing executable Lean binary '
                f'(not an elan shim): {value}')
        return lean

    candidates = []
    toolchain_file = ROOT / 'lean-toolchain'
    if toolchain_file.is_file():
        # Elan stores leanprover/lean4:v4.x as leanprover--lean4---v4.x.
        toolchain = toolchain_file.read_text().strip()
        if toolchain and '/' not in toolchain.replace('leanprover/lean4:', ''):
            directory = toolchain.replace('/', '--').replace(':', '---')
            elan_home = Path(os.environ.get('ELAN_HOME', '~/.elan')).expanduser()
            candidates.append(elan_home / 'toolchains' / directory / 'bin/lean')
    on_path = shutil.which('lean')
    if on_path:
        candidates.append(Path(on_path))
    candidates.append(_LOCAL_LEAN)
    for candidate in candidates:
        lean = _actual_lean(candidate)
        if lean is not None:
            return lean
    raise ConfigurationError(
        'No installed Lean executable was found. Set MATMUL_LEAN to the actual '
        'binary from an existing toolchain; this runner does not install one.')


@dataclass(frozen=True)
class Configuration:
    lean: Path
    dependency_paths: tuple[Path, ...]

    def environment(self) -> dict[str, str]:
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join(map(str, (BUILD, *self.dependency_paths)))
        return env


def configuration() -> Configuration:
    """Resolve existing paths without invoking Lake, elan, or any installer."""
    lean = _lean_executable()
    dependencies = []
    if 'MATMUL_LEAN_PATH' in os.environ:
        value = os.environ['MATMUL_LEAN_PATH']
        if not value.strip() or not any(value.split(os.pathsep)):
            raise ConfigurationError('MATMUL_LEAN_PATH must not be empty.')
        dependencies.extend(_directory(part, 'MATMUL_LEAN_PATH')
                            for part in value.split(os.pathsep) if part)
    if 'MATMUL_PACKAGES' in os.environ:
        packages = _directory(os.environ['MATMUL_PACKAGES'], 'MATMUL_PACKAGES')
    elif 'MATMUL_LEAN_PATH' in os.environ:
        packages = None
    else:
        packages = next((candidate for candidate in
                         (ROOT / '.lake/packages', ROOT.parent / '.lake/packages',
                          _LOCAL_PACKAGES) if candidate.is_dir()), None)
    if packages is not None:
        cached = sorted(path.resolve() for path in
                        packages.glob('*/.lake/build/lib/lean') if path.is_dir())
        if 'MATMUL_PACKAGES' in os.environ and not cached:
            raise ConfigurationError(
                f'MATMUL_PACKAGES contains no compiled package libraries: {packages}')
        dependencies.extend(cached)
    dependencies = tuple(dict.fromkeys(dependencies))
    if not dependencies:
        raise ConfigurationError(
            'No compiled dependency libraries were found. Set MATMUL_PACKAGES '
            'to an existing Lake packages directory or MATMUL_LEAN_PATH to '
            'compiled library directories. No packages will be downloaded.')
    return Configuration(lean, dependencies)


def environment():
    """Return a Lean environment using the selected installed dependencies."""
    return configuration().environment()


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('files', nargs='+', type=Path, help='Lean sources within this folder')
    parser.add_argument('--compile', action='store_true', help='write local .olean artifacts')
    args = parser.parse_args()
    try:
        config = configuration()
        env = config.environment()
        for file in args.files:
            path = file.resolve()
            if not path.is_file() or path.suffix != '.lean':
                raise ConfigurationError(f'Lean source does not exist: {file}')
            try:
                relative = path.relative_to(ROOT)
            except ValueError as error:
                raise ConfigurationError(f'Lean source must be inside {ROOT}: {file}') from error
            command = [str(config.lean), '-R', str(ROOT)]
            if args.compile:
                output = (BUILD / relative).with_suffix('.olean')
                output.parent.mkdir(parents=True, exist_ok=True)
                command += ['-o', str(output)]
            command.append(str(path))
            result = subprocess.run(command, env=env, cwd=ROOT)
            if result.returncode:
                return result.returncode
    except (ConfigurationError, OSError) as error:
        print(f'Check error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
