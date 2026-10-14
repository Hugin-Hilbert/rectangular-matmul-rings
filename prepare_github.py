#!/usr/bin/env python3
"""Create a source archive for GitHub without caches or local workspace state."""

import argparse
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
TOP_LEVEL = (
    'README.md', 'extension-notes.md', 'LICENSE', 'NOTICE', 'CITATION.cff', '.gitignore',
    'arbitrary-rings.tex', 'arbitrary-rings.pdf',
    'verify_integral_constructions.py', 'prepare_github.py',
)
FORMALIZATION_FILES = {
    'README.md', 'PROVENANCE.txt', 'env-provenance.txt', 'verification.json',
    'check_lean.py', 'build_local.py', 'lean-toolchain', 'UPSTREAM-LICENSE',
    'dependency-pins.json',
    'proof-correspondence.md',
    'FixedPointTheorems/MIT_LICENSE',
}
ARCHIVE_ROOT = 'rectangular-matmul-rings'


def source_files():
    selected = [ROOT / name for name in TOP_LEVEL]
    selected.extend(ROOT / 'formalization' / name for name in FORMALIZATION_FILES)
    selected.extend((ROOT / 'formalization').rglob('*.lean'))
    selected.append(ROOT / 'licenses/omega-nine-quarters-all-fields.NOTICE')
    for path in sorted(set(selected)):
        relative = path.relative_to(ROOT)
        if any(part in {'.lake', '__pycache__', '.git'} for part in relative.parts):
            continue
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'Required source is not a regular file: {relative}')
        yield path, relative


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'dist/rectangular-matmul-rings.zip')
    args = parser.parse_args()
    try:
        sources = list(source_files())
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(args.output, 'w', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=9) as archive:
            for path, relative in sources:
                archive.write(path, f'{ARCHIVE_ROOT}/{relative.as_posix()}')
    except (OSError, ValueError) as error:
        parser.exit(1, f'Archive error: {error}\n')
    print(f'Created {args.output} ({len(sources)} files, {args.output.stat().st_size} bytes).')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
