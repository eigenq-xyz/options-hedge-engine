"""FFI module for calling the Lean 4 verified accounting layer from Python.

Exports match the Lean @[export hedge_*] functions in Accounting.lean.

All functions call directly into the Lean kernel compiled to C via the
Cython extension (lean_ffi.so).  Build it with:

    cd python && python setup.py build_ext --inplace

Lean's runtime depends on libleanrt and libuv.  On Linux, libleanrt.so is
linked dynamically (libleanrt.a is not PIC-safe for shared objects).  Both
libraries are pre-loaded with RTLD_GLOBAL so their symbols are available
when the Cython extension is dlopen'd.
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

# Pre-load libleanrt and libuv into the global namespace before importing the
# Cython extension.  The extension records NEEDED entries for both, but
# pre-loading with RTLD_GLOBAL guarantees symbol visibility on all platforms.
_preload_candidates: list[list[str | None]] = [
    [ctypes.util.find_library("leanrt")],  # libleanrt.so (Linux only)
    [
        ctypes.util.find_library("uv"),
        "/opt/homebrew/lib/libuv.dylib",  # Homebrew arm64
        "/usr/local/lib/libuv.dylib",  # Homebrew x86 / manual
        "/usr/lib/libuv.so.1",  # Debian/Ubuntu
        "/usr/lib/x86_64-linux-gnu/libuv.so.1",  # Ubuntu multiarch
    ],
]
for _candidates in _preload_candidates:
    for _path in _candidates:
        if _path is None:
            continue
        try:
            ctypes.CDLL(_path, mode=ctypes.RTLD_GLOBAL)
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
