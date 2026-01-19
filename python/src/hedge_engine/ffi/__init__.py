"""FFI module for calling Lean 4 accounting kernel from Python."""

__all__ = ["initialize_lean", "calc_nav_stub"]

try:
    from .lean_ffi import calc_nav_stub, initialize_lean
except ImportError:
    # Cython extension not built yet
    def initialize_lean():
        """Stub: Lean runtime initialization."""
        pass

    def calc_nav_stub():
        """Stub: NAV calculation."""
        return 0
