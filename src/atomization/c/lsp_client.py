import json
from dataclasses import dataclass
from pathlib import Path
from typing import List
import asyncio
from pygls.lsp.client import LanguageClient
from pygls.lsp.types import (
    InitializeParams,
    TextDocumentItem,
    DidOpenTextDocumentParams,
    Position,
    Range,
    SymbolKind,
    DocumentSymbol,
    SymbolInformation,
)

@dataclass
class CAtom:
    termtype: str  # "function", "struct", "typedef", etc.
    identifier: str
    lineno: int
    signature: str  # Function signature or type definition
    code: str  # Function body or type implementation
    deps: list['CAtom']  # Dependencies (functions called, types used, etc.)

    def jsonify(self) -> dict:
        return {
            "termtype": self.termtype,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "code": self.code,
            "deps": [dep.jsonify() for dep in self.deps],
        }

class CAtomizer:
    def __init__(self, filename: Path):
        self.filename = filename
        self.client = None
        self.atoms: list[CAtom] = []

    async def initialize(self):
        """Initialize the LSP client and connect to clangd"""
        self.client = LanguageClient()
        await self.client.connect_tcp("localhost", 8080)  # Default clangd port
        
        # Initialize the LSP connection
        init_params = InitializeParams(
            process_id=None,
            root_uri=str(self.filename.parent),
            capabilities={}
        )
        await self.client.initialize(init_params)
        await self.client.initialized()

    async def get_document_symbols(self) -> list[DocumentSymbol]:
        """Get all symbols (functions, structs, etc.) from the document"""
        doc = TextDocumentItem(
            uri=str(self.filename),
            language_id="c",
            version=1,
            text=self.filename.read_text()
        )
        
        # Open the document
        await self.client.text_document_did_open(
            DidOpenTextDocumentParams(text_document=doc)
        )
        
        # Get document symbols
        symbols = await self.client.document_symbol(
            text_document=doc
        )
        return symbols

    async def atomize(self) -> list[CAtom]:
        """Extract atoms from the C source file"""
        if not self.client:
            await self.initialize()
        
        symbols = await self.get_document_symbols()
        # TODO: Process symbols and create CAtom instances
        return self.atoms

    def jsonify(self) -> str:
        """Convert atoms to JSON string"""
        atoms = asyncio.run(self.atomize())
        return json.dumps([atom.jsonify() for atom in atoms])

async def main():
    # Example usage
    atomizer = CAtomizer(Path("example.c"))
    result = await atomizer.atomize()
    print(json.dumps([atom.jsonify() for atom in result], indent=2))

if __name__ == "__main__":
    asyncio.run(main())
