"""
Basic smoke tests for v0.1-scaffold.

Real tests will be added as functionality is implemented:
- v0.2: FFI bindings tests
- v0.5: Certificate emission tests
- v0.10: ETL tests
"""


def test_imports():
    """Verify package imports correctly."""
    import hedge_engine  # noqa: F401

    assert hedge_engine.__version__ == "0.1.0"


def test_submodules_exist():
    """Verify expected submodules are present."""
    import hedge_engine.ffi  # noqa: F401, E401
    # bindings, certificate, etl modules will be added in later milestones
