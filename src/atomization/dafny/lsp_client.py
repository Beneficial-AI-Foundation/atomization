from dataclasses import dataclass
import logging
import time
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
        self.initialized = False

    def initialize(self):
        """Initialize the LSP client with proper capabilities."""

        def on_init_response(result):
            self.logger.info(f"LSP Server initialized: {result}")
            # Send initialized notification
            self.transport.notify("initialized", {})
            self.initialized = True

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

        self.transport.send("initialize", init_params, on_init_response)

        # Wait for initialization to complete
        timeout = 5.0
        start_time = time.time()
        while not self.initialized and (time.time() - start_time) < timeout:
            time.sleep(0.1)

        if not self.initialized:
            raise RuntimeError("Failed to initialize Dafny LSP server")

    def open_file(self, uri: str, text: str):
        self.logger.debug(f"Opening file: {uri}")
        self.transport.notify(
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

    def request_all_symbols(self, on_symbols):
        def handler(result):
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
            on_symbols(syms)

        self.transport.send("workspace/symbol", {"query": ""}, handler)

    def request_all_symbols_debug(self, on_symbols):
        """Request all symbols without filtering by kind for debugging."""

        def handler(result):
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
            on_symbols(all_symbols)

        self.transport.send("workspace/symbol", {"query": ""}, handler)

    def request_references(self, sym: DafnySymbol, on_refs):
        def handler(result):
            rs = [DafnyRef(sym.name, r["uri"], r["range"]) for r in result]
            on_refs(rs)

        self.transport.send(
            "textDocument/references",
            {
                "textDocument": {"uri": sym.uri},
                "position": sym.position,
                "context": {"includeDeclaration": False},
            },
            handler,
        )
