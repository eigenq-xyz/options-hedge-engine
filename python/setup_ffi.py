"""
Build script for the Lean 4 Cython FFI extension.

Usage (from python/ directory):
    uv run python setup_ffi.py build_ext --inplace

Prerequisites:
- `lake build` must have been run in lean/ to generate C IR files
- `lean` must be on PATH (managed by elan)
"""

import os
import subprocess
import sys
from pathlib import Path

from Cython.Build import cythonize
from setuptools import Extension, setup


def find_lean_prefix() -> Path:
    """Locate the active Lean toolchain prefix via `lean --print-prefix`."""
    try:
        result = subprocess.run(
            ["lean", "--print-prefix"],
            capture_output=True,
            text=True,
            check=True,
        )
        return Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        sys.exit(f"ERROR: could not find Lean toolchain — is `lean` on PATH? ({e})")


def find_lake_ir(repo_root: Path) -> Path:
    """Return the Lake C IR output directory for OptionHedge."""
    ir_dir = repo_root / "lean" / ".lake" / "build" / "ir" / "OptionHedge"
    if not ir_dir.is_dir():
        sys.exit(
            f"ERROR: Lake IR directory not found at {ir_dir}\n" "Run `cd lean && lake build` first."
        )
    return ir_dir


def main() -> None:
    # Repo root is one directory up from python/
    repo_root = Path(__file__).parent.parent.resolve()
    lean_prefix = find_lean_prefix()
    ir_dir = find_lake_ir(repo_root)

    lean_include = str(lean_prefix / "include")
    lean_lib_dir = str(lean_prefix / "lib" / "lean")

    # Lean C source files to compile alongside the Cython extension.
    # Only Basic and Accounting are needed — proofs (Invariants) and tests
    # are not required at runtime.
    lean_c_sources = [
        str(ir_dir / "Basic.c"),
        str(ir_dir / "Accounting.c"),
    ]
    for src in lean_c_sources:
        if not os.path.isfile(src):
            sys.exit(f"ERROR: expected Lake-generated C file not found: {src}")

    pyx_file = str(Path(__file__).parent / "src" / "hedge_engine" / "ffi" / "lean_ffi.pyx")

    extension = Extension(
        name="hedge_engine.ffi.lean_ffi",
        sources=[pyx_file] + lean_c_sources,
        include_dirs=[lean_include],
        library_dirs=[lean_lib_dir],
        libraries=["leanshared"],
        # Embed rpath so the extension finds libleanshared.dylib at import time
        # without requiring manual LD_LIBRARY_PATH / DYLD_LIBRARY_PATH.
        runtime_library_dirs=[lean_lib_dir],
        extra_compile_args=["-Wno-unused-parameter", "-Wno-unused-label"],
        language="c",
    )

    setup(
        name="hedge-engine-ffi",
        ext_modules=cythonize(
            [extension],
            compiler_directives={
                "language_level": "3",
                "boundscheck": False,
                "wraparound": False,
            },
        ),
    )


if __name__ == "__main__":
    main()
