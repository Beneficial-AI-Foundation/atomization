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

    async def initialize(self) -> None:
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
                # Capture Classes (5), Methods (6), and Functions (12)
                # Kind 5 = Class, Kind 6 = Method, Kind 12 = Function
                if s["kind"] in (5, 6, 12):
                    syms.append(
                        DafnySymbol(
                            s["name"],
                            s["location"]["uri"],
                            s["location"]["range"]["start"],
                        )
                    )
        self.logger.info(
            f"Found {len(syms)} symbols (Classes: kind 5, Methods: kind 6, Functions: kind 12)"
        )
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

    async def build_dependency_graph(
        self, symbols: list[DafnySymbol], source_content: str = ""
    ) -> dict[str, list[str]]:
        """Build a dependency graph showing which symbols depend on which other symbols.

        Args:
            symbols: List of DafnySymbol objects to analyze
            source_content: Original source code to analyze

        Returns:
            Dict mapping symbol names to lists of symbols they depend on
        """
        dependencies = {}
        {sym.name for sym in symbols}

        for symbol in symbols:
            self.logger.debug(f"Analyzing dependencies for symbol: {symbol.name}")
            symbol_deps = set()

            # Analyze dependencies in the symbol's code
            if source_content:
                deps_in_code = self._find_dependencies_in_code(
                    symbol, symbols, source_content
                )
                symbol_deps.update(deps_in_code)

            dependencies[symbol.name] = list(symbol_deps)

        return dependencies

    def _find_dependencies_in_code(
        self, symbol: DafnySymbol, all_symbols: list[DafnySymbol], source_content: str
    ) -> set[str]:
        """Find dependencies by analyzing the symbol's code content."""
        dependencies = set()

        # Get the symbol's code block
        lines = source_content.split("\n")
        start_line = symbol.position.get("line", 0)

        if start_line >= len(lines):
            return dependencies

        # Extract the symbol's code block (similar to jsonify_vlib logic)
        current_line = start_line
        symbol_code_lines = []
        brace_count = 0
        in_block = False

        while current_line < len(lines):
            line = lines[current_line]
            symbol_code_lines.append(line)

            # Count braces to find the end of the block
            for char in line:
                if char == "{":
                    brace_count += 1
                    in_block = True
                elif char == "}":
                    brace_count -= 1

            # If we've closed all braces and we were in a block, we're done
            if in_block and brace_count == 0:
                break

            current_line += 1

        # Analyze the extracted code for references to other symbols
        symbol_code = "\n".join(symbol_code_lines)

        for other_symbol in all_symbols:
            if other_symbol.name != symbol.name:
                # Simple text search for symbol name
                # This could be improved with proper parsing to avoid false positives
                if self._symbol_referenced_in_code(other_symbol.name, symbol_code):
                    dependencies.add(other_symbol.name)

        return dependencies

    def _symbol_referenced_in_code(self, symbol_name: str, code: str) -> bool:
        """Check if a symbol is referenced in the given code."""
        import re

        # Look for the symbol name as a whole word (not part of another identifier)
        # This is a simple heuristic - proper analysis would use AST parsing
        pattern = r"\b" + re.escape(symbol_name) + r"\b"

        # Exclude the line where the symbol is defined (to avoid self-references)
        lines = code.split("\n")
        for i, line in enumerate(lines):
            # Skip the first line if it contains the symbol definition
            if i == 0 and (
                "function " + symbol_name in line
                or "method " + symbol_name in line
                or "class " + symbol_name in line
            ):
                continue

            # Skip method definitions within classes (these are containment, not dependencies)
            if "method " + symbol_name + "(" in line:
                continue

            # Look for actual function/method calls or references
            if re.search(pattern, line):
                # Additional filtering to avoid false positives
                # Skip if it's just a method definition line
                if re.match(r"\s*method\s+" + re.escape(symbol_name), line):
                    continue
                return True

        return False
