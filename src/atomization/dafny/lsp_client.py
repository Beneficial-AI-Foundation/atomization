from dataclasses import dataclass
import logging
import asyncio
from atomization.common.lsp.basic import AtomizerPlugin


@dataclass
class DafnySymbol:
    name: str
    uri: str
    position: dict


@dataclass
class DafnyRef:
    caller: str
    uri: str
    range: dict


class DafnyAtomizer(AtomizerPlugin[DafnySymbol, DafnyRef]):
    def __init__(self, transport):
        super().__init__(transport)
        self.logger = logging.getLogger(f"{__name__}.{self.__class__.__name__}")
        self._initialized = asyncio.Event()

    async def initialize(self):
        """Initialize the LSP client with proper capabilities."""
        # Send initialize request with proper client capabilities
        init_params = {
            "processId": None,
            "clientInfo": {"name": "atomization-dafny-client", "version": "1.0.0"},
            "capabilities": {
                "workspace": {
                    "symbol": {
                        "symbolKind": {
                            "valueSet": list(range(1, 26))  # Support all symbol kinds
                        }
                    }
                },
                "textDocument": {
                    "references": {},
                    "synchronization": {
                        "didOpen": True,
                        "didChange": True,
                        "didClose": True,
                    },
                },
            },
            "workspaceFolders": None,
        }

        try:
            result = await self.transport.send("initialize", init_params)
            self.logger.info(f"LSP Server initialized: {result}")

            # Send initialized notification
            await self.transport.notify("initialized", {})
            self._initialized.set()

        except Exception as e:
            raise RuntimeError(f"Failed to initialize Dafny LSP server: {e}")

    async def open_file(self, uri: str, text: str):
        self.logger.debug(f"Opening file: {uri}")
        await self.transport.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": uri,
                    "languageId": "dafny",
                    "version": 1,
                    "text": text,
                }
            },
        )

    async def request_all_symbols(self) -> list[DafnySymbol]:
        result = await self.transport.send("workspace/symbol", {"query": ""})
        self.logger.debug(f"workspace/symbol response: {result}")

        syms = []
        if result:
            for s in result:
                if s["kind"] == 12:  # Method
                    syms.append(
                        DafnySymbol(
                            s["name"],
                            s["location"]["uri"],
                            s["location"]["range"]["start"],
                        )
                    )
        self.logger.info(f"Found {len(syms)} symbols with kind 12")
        return syms

    async def request_all_symbols_debug(self) -> list[dict]:
        """Request all symbols without filtering by kind for debugging."""
        result = await self.transport.send("workspace/symbol", {"query": ""})
        self.logger.debug(f"workspace/symbol response: {result}")

        all_symbols = []
        if result:
            for s in result:
                symbol_info = {
                    "name": s.get("name", "unknown"),
                    "kind": s.get("kind", -1),
                    "uri": s.get("location", {}).get("uri", "unknown"),
                    "range": s.get("location", {}).get("range", {}),
                }
                all_symbols.append(symbol_info)
        self.logger.info(f"Found {len(all_symbols)} total symbols")
        return all_symbols

    async def request_references(self, sym: DafnySymbol) -> list[DafnyRef]:
        result = await self.transport.send(
            "textDocument/references",
            {
                "textDocument": {"uri": sym.uri},
                "position": sym.position,
                "context": {"includeDeclaration": False},
            },
        )
        return [DafnyRef(sym.name, r["uri"], r["range"]) for r in result or []]
