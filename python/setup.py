"""
Setup script for building Cython extensions with Lean FFI.

Compiles the four FFI-relevant Lean C IR files (Accounting, Basic, Options,
Numeric) into object files using leanc, then links them into the Cython
extension together with libleanrt, libStd, libInit, and libgmp.

The proof files (Invariants, OptionInvariants) are intentionally excluded:
they import Mathlib (for omega/simp tactics) but contain no runtime-callable
code — all their content is erased at the C level as proofs.

Build:
    cd python && python setup.py build_ext --inplace
"""

import platform
import subprocess
from pathlib import Path

from Cython.Build import cythonize
from setuptools import Extension, setup

# ── Lean toolchain ───────────────────────────────────────────────────────────
# Read the pinned toolchain version from lean-toolchain.
PROJECT_ROOT = Path(__file__).parent.parent
LEAN_TOOLCHAIN_FILE = PROJECT_ROOT / "lean" / "lean-toolchain"
if not LEAN_TOOLCHAIN_FILE.exists():
    raise RuntimeError(
        f"lean/lean-toolchain not found at {LEAN_TOOLCHAIN_FILE}"
    )

toolchain_id = LEAN_TOOLCHAIN_FILE.read_text().strip()
# e.g. "leanprover/lean4:v4.27.0-rc1" → "leanprover--lean4---v4.27.0-rc1"
tc_dir = toolchain_id.replace("/", "--").replace(":", "---")

ELAN_TOOLCHAINS = Path.home() / ".elan" / "toolchains"
LEAN_TC = ELAN_TOOLCHAINS / tc_dir
if not LEAN_TC.exists():
    raise RuntimeError(
        f"Lean toolchain {tc_dir} not found in ~/.elan/toolchains/\n"
        f"Run: elan toolchain install {toolchain_id}"
    )

LEAN_INCLUDE = LEAN_TC / "include"
LEAN_LIB_DIR = LEAN_TC / "lib" / "lean"
LEAN_ROOT_LIB = LEAN_TC / "lib"
LEANC = LEAN_TC / "bin" / "leanc"

# ── Lean project C IR files ──────────────────────────────────────────────────
LEAN_PROJECT = PROJECT_ROOT / "lean"
LEAN_IR = LEAN_PROJECT / ".lake" / "build" / "ir" / "OptionHedge"

# Only the four modules that contain FFI-callable runtime code.
# Invariants.c and OptionInvariants.c depend on Mathlib (for proof tactics)
# and contain no runtime-callable symbols — exclude them.
FFI_MODULES = ["Accounting", "Basic", "Options"]

if not LEAN_IR.exists():
    print("Lean IR not found; running `lake build` first …")
    subprocess.run(["lake", "build"], cwd=LEAN_PROJECT, check=True)

# ── Compile each C IR file to a .o object file ───────────────────────────────
BUILD_OBJ_DIR = LEAN_PROJECT / ".lake" / "build" / "ffi_objs"
BUILD_OBJ_DIR.mkdir(parents=True, exist_ok=True)

lean_obj_files: list[str] = []
for module in FFI_MODULES:
    c_src = LEAN_IR / f"{module}.c"
    obj_out = BUILD_OBJ_DIR / f"{module}.o"
    if not c_src.exists():
        raise RuntimeError(
            f"Expected C IR file not found: {c_src}\n"
            "Run `cd lean && lake build` to regenerate."
        )
    print(f"  leanc -c {c_src.name} → {obj_out.name}")
    subprocess.run(
        [
            str(LEANC),
            "-c",
            f"-I{LEAN_INCLUDE}",
            "-fvisibility=default",
            "-o",
            str(obj_out),
            str(c_src),
        ],
        check=True,
    )
    lean_obj_files.append(str(obj_out))

# ── Cython extension ─────────────────────────────────────────────────────────
# Lean runtime + stdlib static libraries (must be resolved from toolchain,
# not system libs).  libuv and libleanrt must be force-loaded so that their
# symbols survive the macOS linker's dead-code stripping pass.
lean_static_libs = [
    str(LEAN_LIB_DIR / "libStd.a"),
    str(LEAN_LIB_DIR / "libInit.a"),
    str(LEAN_ROOT_LIB / "libgmp.a"),
]
force_load_libs = [
    str(LEAN_LIB_DIR / "libleanrt.a"),
    str(LEAN_ROOT_LIB / "libuv.a"),
]
# libuv must be a dynamic dependency recorded in the .so so that the OS
# loads it automatically when Python imports the extension.  On macOS with
# Homebrew, libuv.dylib lives in /opt/homebrew/lib; on Linux it is a system
# package (e.g. libuv1-dev).
if platform.system() == "Darwin":
    libuv_dirs = ["/opt/homebrew/lib", "/usr/local/lib"]
else:
    libuv_dirs = [
        "/usr/lib",
        "/usr/local/lib",
        "/usr/lib/x86_64-linux-gnu",
        "/usr/lib/aarch64-linux-gnu",
    ]

libuv_lib_dir = next(
    (
        d
        for d in libuv_dirs
        if (Path(d) / "libuv.dylib").exists()
        or (Path(d) / "libuv.so").exists()
        or (Path(d) / "libuv.so.1").exists()
    ),
    None,
)
if libuv_lib_dir is None:
    raise RuntimeError(
        "libuv dynamic library not found.  "
        "Install it: brew install libuv  (macOS) or "
        "apt install libuv1-dev  (Linux)"
    )

if platform.system() == "Darwin":
    link_args = [
        f"-Wl,-force_load,{LEAN_LIB_DIR / 'libleanrt.a'}",
        f"-Wl,-rpath,{libuv_lib_dir}",
    ]
else:
    # GNU ld: -force_load equivalent is --whole-archive around the target archive
    link_args = [
        f"-Wl,--whole-archive,{LEAN_LIB_DIR / 'libleanrt.a'}",
        "-Wl,--no-whole-archive",
        f"-Wl,-rpath,{libuv_lib_dir}",
    ]

extensions = [
    Extension(
        "hedge_engine.ffi.lean_ffi",
        sources=["src/hedge_engine/ffi/lean_ffi.pyx"],
        include_dirs=[str(LEAN_INCLUDE)],
        library_dirs=[libuv_lib_dir],
        libraries=["uv"],
        extra_objects=lean_obj_files + lean_static_libs,
        extra_compile_args=["-fvisibility=default"],
        extra_link_args=link_args,
    )
]

setup(
    ext_modules=cythonize(
        extensions,
        compiler_directives={"language_level": "3"},
    ),
)
