"""
Setup script for building Cython extensions with Lean FFI.

This compiles lean_ffi.pyx and links against Lean's runtime library.
"""

import subprocess
from pathlib import Path

from Cython.Build import cythonize
from setuptools import Extension, setup

# Find Lean installation
LEAN_ROOT = Path.home() / ".elan" / "toolchains"
lean_dirs = list(LEAN_ROOT.glob("leanprover--lean4*"))
if not lean_dirs:
    raise RuntimeError("Lean 4 not found in ~/.elan/toolchains/")

LEAN_DIR = lean_dirs[0]  # Use first found version
LEAN_INCLUDE = LEAN_DIR / "include"
LEAN_LIB = LEAN_DIR / "lib" / "lean"

# Find our Lean project's build artifacts
PROJECT_ROOT = Path(__file__).parent.parent.parent.parent
LEAN_PROJECT = PROJECT_ROOT / "lean"
LEAN_BUILD = LEAN_PROJECT / ".lake" / "build"

if not LEAN_BUILD.exists():
    print("Building Lean project first...")
    subprocess.run(["lake", "build"], cwd=LEAN_PROJECT, check=True)

# Lean object files to link
LEAN_OBJS = list((LEAN_BUILD / "lib").glob("**/*.o"))
if not LEAN_OBJS:
    raise RuntimeError(f"No Lean .o files found in {LEAN_BUILD / 'lib'}")

extensions = [
    Extension(
        "hedge_engine.ffi.lean_ffi",
        sources=["src/hedge_engine/ffi/lean_ffi.pyx"],
        include_dirs=[str(LEAN_INCLUDE)],
        library_dirs=[str(LEAN_LIB)],
        libraries=["leanrt"],
        extra_objects=[str(obj) for obj in LEAN_OBJS],
        extra_compile_args=["-std=c11"],
    )
]

setup(
    ext_modules=cythonize(extensions, compiler_directives={"language_level": "3"}),
)
