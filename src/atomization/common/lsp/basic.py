from abc import ABC, abstractmethod
from typing import Generic, TypeVar
from atomization.common.lsp.transport import JsonRpcTransport

Symbol = TypeVar("Symbol")
Ref = TypeVar("Ref")


class AtomizerPlugin(ABC, Generic[Symbol, Ref]):
    def __init__(self, transport: JsonRpcTransport):
        self.transport = transport
        self.symbols: list[Symbol] = []
        self.refs: list[Ref] = []

    @abstractmethod
    async def initialize(self) -> None:
        """send initialize & initialized() to LSP"""

    @abstractmethod
    async def open_file(self, uri: str, text: str) -> None:
        """notify server about a new/changed file"""

    @abstractmethod
    async def request_all_symbols(self) -> list[Symbol]:
        """populate `symbols` via workspace/symbol or equivalent"""

    @abstractmethod
    async def request_references(self, sym: Symbol) -> list[Ref]:
        """for a given symbol, populate `refs` via textDocument/references"""
