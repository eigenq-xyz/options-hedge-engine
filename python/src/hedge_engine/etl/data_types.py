"""Pydantic schemas for raw market data ingested from WRDS or flat files.

These types live at the boundary between external data sources and the
engine.  Validation happens here; downstream code can trust the types.
"""

from pydantic import BaseModel, Field, field_validator


class UnderlyingSnapshot(BaseModel):
    """A single observation of an underlying asset price.

    Attributes:
        ticker: Exchange ticker symbol (e.g. ``"SPY"``).
        date: Observation date in ISO-8601 format (``"YYYY-MM-DD"``).
        close: Closing price in dollars (positive).
    """

    ticker: str
    date: str
    close: float = Field(gt=0)

    @field_validator("ticker")
    @classmethod
    def ticker_nonempty(cls, v: str) -> str:
        if not v.strip():
            raise ValueError("ticker must not be empty")
        return v.upper()

    @field_validator("date")
    @classmethod
    def date_format(cls, v: str) -> str:
        import re

        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", v):
            raise ValueError(f"date must be YYYY-MM-DD, got {v!r}")
        return v


class OptionSnapshot(BaseModel):
    """A single observation of a European option.

    Attributes:
        underlying_ticker: Ticker of the underlying asset.
        date: Observation date in ISO-8601 format.
        expiry: Option expiry date in ISO-8601 format.
        strike: Strike price in dollars (positive).
        option_type: ``"call"`` or ``"put"``.
        mid_price: Mid-market option price in dollars (non-negative).
        implied_vol: Implied volatility as a fraction (e.g. 0.20 for 20%).
        underlying_price: Contemporaneous underlying spot price in dollars.
            Optional; populated from ``spotprice`` in OptionMetrics ``opprcd``.
    """

    underlying_ticker: str
    date: str
    expiry: str
    strike: float = Field(gt=0)
    option_type: str
    mid_price: float = Field(ge=0)
    implied_vol: float = Field(gt=0)
    underlying_price: float | None = Field(default=None, gt=0)

    @field_validator("option_type")
    @classmethod
    def option_type_valid(cls, v: str) -> str:
        mapping = {"c": "call", "call": "call", "p": "put", "put": "put"}
        normalised = mapping.get(v.lower())
        if normalised is None:
            raise ValueError(
                f"option_type must be 'call'/'C' or 'put'/'P', got {v!r}"
            )
        return normalised

    @field_validator("underlying_ticker")
    @classmethod
    def ticker_nonempty(cls, v: str) -> str:
        if not v.strip():
            raise ValueError("underlying_ticker must not be empty")
        return v.upper()
