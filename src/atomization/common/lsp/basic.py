from abc import ABC, abstractmethod
from typing import Callable, Generic, TypeVar
from atomization.common.lsp.transport import JsonRpcTransport

Symbol = TypeVar("Symbol")
Ref = TypeVar("Ref")


class AtomizerPlugin(ABC, Generic[Symbol, Ref]):
    def __init__(self, transport: JsonRpcTransport):
        self.transport = transport
        self.symbols: list[Symbol] = []
        self.refs: list[Ref] = []

    @abstractmethod
    def initialize(self) -> None:
        """send initialize & initialized() to LSP"""

    @abstractmethod
    def open_file(self, uri: str, text: str) -> None:
        """notify server about a new/changed file"""

    @abstractmethod
    def request_all_symbols(self, on_symbols: Callable[[list[Symbol]], None]) -> None:
        """populate `symbols` via workspace/symbol or equivalent"""

    @abstractmethod
    def request_references(
        self, sym: Symbol, on_refs: Callable[[list[Ref]], None]
    ) -> None:
        """for a given symbol, populate `refs` via textDocument/references"""
