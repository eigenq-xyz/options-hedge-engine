"""FFI module for calling Lean 4 accounting kernel from Python.

Exports match the Lean @[export hedge_*] functions in Accounting.lean.

All functions call directly into the Lean kernel compiled to C via the
Cython extension (lean_ffi.so).  Build it with:

    cd python && python setup.py build_ext --inplace

Lean's runtime depends on libuv.  On macOS/Linux, libuv must be installed
as a system or Homebrew library.  We pre-load it with RTLD_GLOBAL so that
its symbols are in the process namespace when the extension is dlopen'd.
"""

import ctypes
import ctypes.util

__all__ = [
    "initialize_lean",
    "portfolio_value",
    "position_value",
    "sum_position_values",
    "get_position",
    "apply_trade",
    "settle_option",
]

# Pre-load libuv into the global namespace so the Lean runtime can find it.
# ctypes.util.find_library may not search Homebrew paths on macOS, so we
# also probe common installation directories directly.
_libuv_probes: list[str | None] = [
    ctypes.util.find_library("uv"),  # system / ldconfig
    "/opt/homebrew/lib/libuv.dylib",  # Homebrew arm64
    "/usr/local/lib/libuv.dylib",  # Homebrew x86 / manual
    "/usr/lib/libuv.so.1",  # Debian/Ubuntu
    "/usr/lib/x86_64-linux-gnu/libuv.so.1",  # Ubuntu multiarch
]
_libuv_candidates: list[str] = [p for p in _libuv_probes if p is not None]
for _libuv_path in _libuv_candidates:
    try:
        ctypes.CDLL(_libuv_path, mode=ctypes.RTLD_GLOBAL)
        break
    except OSError:
        continue

from .lean_ffi import (  # type: ignore[import-untyped]  # noqa: E402
    apply_trade,
    get_position,
    initialize_lean,
    portfolio_value,
    position_value,
    settle_option,
    sum_position_values,
)

initialize_lean()
