import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass
class CAtom:
    termtype: str  # "function", "struct", "typedef", etc.
    identifier: str
    lineno: int
    signature: str  # Function signature or type definition
    code: str  # Function body or type implementation
    deps: list["CAtom"]  # Dependencies (functions called, types used, etc.)

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
        self.atoms: list[CAtom] = []
        self.clangd_process: subprocess.Popen[str] | None = None
        self.request_id = 1

    def _start_clangd(self) -> None:
        """Start clangd process"""
        print("Starting clangd server", file=sys.stderr)
        # Start clangd as a server with background indexing and other optimizations
        self.clangd_process = subprocess.Popen(
            [
                "clangd",
                "--background-index",
                "--header-insertion=never",
                "--pch-storage=memory",
                "--log=verbose",
                "--pretty",
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,  # Line buffered
        )
        print("clangd server started", file=sys.stderr)

        # Check if process is running
        if self.clangd_process.poll() is not None:
            raise RuntimeError("clangd failed to start")

        # Give clangd a moment to initialize and monitor stderr
        print("Waiting for clangd to initialize...", file=sys.stderr)
        start_time = time.time()
        while time.time() - start_time < 5:  # 5 second timeout
            # Check stderr for any output
            stderr_line = self.clangd_process.stderr.readline()
            if stderr_line:
                print(
                    f"clangd stderr during init: {stderr_line.strip()}", file=sys.stderr
                )

            # Check if process is still running
            if self.clangd_process.poll() is not None:
                raise RuntimeError(
                    "clangd process ended unexpectedly during initialization"
                )

            time.sleep(0.1)

        print("Initialization wait complete", file=sys.stderr)

    def _read_response(self, timeout: float = 5.0) -> dict:
        """Read a response from clangd with timeout"""
        if not self.clangd_process:
            raise RuntimeError("clangd process not started")

        print("Waiting for response...", file=sys.stderr)
        start_time = time.time()

        while True:
            # Check for timeout
            if time.time() - start_time > timeout:
                print(
                    f"Timeout after {timeout} seconds. Process state:", file=sys.stderr
                )
                print(
                    f"  Process running: {self.clangd_process.poll() is None}",
                    file=sys.stderr,
                )
                print(f"  Return code: {self.clangd_process.poll()}", file=sys.stderr)
                raise RuntimeError(
                    f"Timeout waiting for response after {timeout} seconds"
                )

            # Check if process is still running
            if self.clangd_process.poll() is not None:
                print(
                    "clangd process ended unexpectedly. Last stderr output:",
                    file=sys.stderr,
                )
                stderr_output = self.clangd_process.stderr.read()
                if stderr_output:
                    print(stderr_output, file=sys.stderr)
                raise RuntimeError("clangd process ended unexpectedly")

            # Check for stderr output
            stderr_line = self.clangd_process.stderr.readline()
            if stderr_line:
                print(f"clangd stderr: {stderr_line.strip()}", file=sys.stderr)

            # Check for stdout output
            stdout_line = self.clangd_process.stdout.readline()
            if stdout_line:
                print(f"Received line: {stdout_line.strip()}", file=sys.stderr)
                try:
                    response = json.loads(stdout_line)
                    if "id" in response:  # This is a response to our request
                        print(
                            f"Got response: {json.dumps(response, indent=2)}",
                            file=sys.stderr,
                        )
                        return response
                except json.JSONDecodeError:
                    print(
                        f"Failed to parse JSON: {stdout_line.strip()}", file=sys.stderr
                    )
                    continue

            # Small sleep to prevent busy waiting
            time.sleep(0.1)

    def _send_lsp_request(self, method: str, params: dict) -> dict:
        """Send an LSP request to clangd"""
        if not self.clangd_process:
            self._start_clangd()
            if not self.clangd_process:
                raise RuntimeError("Failed to start clangd process")

            # Initialize LSP
            init_request = {
                "jsonrpc": "2.0",
                "id": self.request_id,
                "method": "initialize",
                "params": {
                    "processId": None,
                    "rootUri": str(self.filename.parent.absolute()),
                    "capabilities": {
                        "textDocument": {
                            "documentSymbol": {
                                "symbolKind": {
                                    "valueSet": [
                                        1,
                                        2,
                                        3,
                                        4,
                                        5,
                                        6,
                                        7,
                                        8,
                                        9,
                                        10,
                                        11,
                                        12,
                                        13,
                                        14,
                                        15,
                                        16,
                                        17,
                                        18,
                                        19,
                                        20,
                                        21,
                                        22,
                                        23,
                                        24,
                                        25,
                                        26,
                                    ]
                                }
                            }
                        }
                    },
                },
            }
            print(
                f"Sending initialize request: {json.dumps(init_request, indent=2)}",
                file=sys.stderr,
            )

            # Format message according to LSP spec
            message = json.dumps(init_request)
            content_length = len(message.encode("utf-8"))
            header = f"Content-Length: {content_length}\r\n\r\n"

            print(f"Sending header: {header.strip()}", file=sys.stderr)
            print(f"Sending message: {message}", file=sys.stderr)

            # Send header and message
            if self.clangd_process.stdin is None:
                raise RuntimeError("clangd process stdin is None")

            # Send as bytes to ensure proper encoding
            header_bytes = header.encode("utf-8")
            message_bytes = message.encode("utf-8")

            print(f"Sending {len(header_bytes)} bytes of header", file=sys.stderr)
            print(f"Sending {len(message_bytes)} bytes of message", file=sys.stderr)

            self.clangd_process.stdin.buffer.write(header_bytes)
            self.clangd_process.stdin.buffer.write(message_bytes)
            self.clangd_process.stdin.buffer.flush()
            self.request_id += 1

            # Wait for initialize response
            print("Waiting for initialize response...", file=sys.stderr)
            init_response = self._read_response()
            if "error" in init_response:
                print(
                    f"Initialize error: {json.dumps(init_response['error'], indent=2)}",
                    file=sys.stderr,
                )
                raise RuntimeError(
                    f"Failed to initialize clangd: {init_response['error']}"
                )

            # Send initialized notification
            initialized = {"jsonrpc": "2.0", "method": "initialized", "params": {}}
            print("Sending initialized notification", file=sys.stderr)

            # Format message according to LSP spec
            message = json.dumps(initialized)
            content_length = len(message.encode("utf-8"))
            header = f"Content-Length: {content_length}\r\n\r\n"

            # Send as bytes
            header_bytes = header.encode("utf-8")
            message_bytes = message.encode("utf-8")

            self.clangd_process.stdin.buffer.write(header_bytes)
            self.clangd_process.stdin.buffer.write(message_bytes)
            self.clangd_process.stdin.buffer.flush()

            # Send didOpen notification for the file
            did_open = {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": f"file://{self.filename.absolute()}",
                        "languageId": "c",
                        "version": 1,
                        "text": self.filename.read_text(),
                    }
                },
            }
            print("Sending didOpen notification", file=sys.stderr)

            # Format message according to LSP spec
            message = json.dumps(did_open)
            content_length = len(message.encode("utf-8"))
            header = f"Content-Length: {content_length}\r\n\r\n"

            # Send as bytes
            header_bytes = header.encode("utf-8")
            message_bytes = message.encode("utf-8")

            self.clangd_process.stdin.buffer.write(header_bytes)
            self.clangd_process.stdin.buffer.write(message_bytes)
            self.clangd_process.stdin.buffer.flush()

        # Send the actual request
        request = {
            "jsonrpc": "2.0",
            "id": self.request_id,
            "method": method,
            "params": params,
        }
        self.request_id += 1

        print(f"Sending request: {json.dumps(request, indent=2)}", file=sys.stderr)

        # Format message according to LSP spec
        message = json.dumps(request)
        content_length = len(message.encode("utf-8"))
        header = f"Content-Length: {content_length}\r\n\r\n"

        # Send as bytes
        header_bytes = header.encode("utf-8")
        message_bytes = message.encode("utf-8")

        self.clangd_process.stdin.buffer.write(header_bytes)
        self.clangd_process.stdin.buffer.write(message_bytes)
        self.clangd_process.stdin.buffer.flush()

        response = self._read_response()
        if "error" in response:
            raise RuntimeError(f"LSP request failed: {response['error']}")
        return response.get("result", {})

    def _get_document_symbols(self) -> list[dict]:
        """Get document symbols from clangd"""
        params = {"textDocument": {"uri": f"file://{self.filename.absolute()}"}}
        response = self._send_lsp_request("textDocument/documentSymbol", params)
        return response if isinstance(response, list) else []

    def _get_symbol_text(self, symbol: dict) -> str:
        """Get the text content of a symbol"""
        # Read the file content
        with open(self.filename) as f:
            lines = f.readlines()

        # Get the range of the symbol
        start_line = symbol["range"]["start"]["line"]
        end_line = symbol["range"]["end"]["line"]

        # Extract the text
        return "".join(lines[start_line : end_line + 1])

    def atomize(self) -> list[CAtom]:
        """Extract atoms from the C source file"""
        symbols = self._get_document_symbols()

        for symbol in symbols:
            kind = symbol.get("kind", 0)
            if kind == 12:  # Function
                atom = CAtom(
                    termtype="function",
                    identifier=symbol["name"],
                    lineno=symbol["range"]["start"]["line"],
                    signature=symbol.get("detail", ""),
                    code=self._get_symbol_text(symbol),
                    deps=[],  # Will be populated later
                )
                self.atoms.append(atom)
            elif kind == 23:  # Struct
                atom = CAtom(
                    termtype="struct",
                    identifier=symbol["name"],
                    lineno=symbol["range"]["start"]["line"],
                    signature=symbol.get("detail", ""),
                    code=self._get_symbol_text(symbol),
                    deps=[],
                )
                self.atoms.append(atom)

        return self.atoms

    def jsonify(self) -> str:
        """Convert atoms to JSON string"""
        return json.dumps([atom.jsonify() for atom in self.atoms])

    def __del__(self):
        """Clean up clangd process"""
        if self.clangd_process:
            print("Terminating clangd process", file=sys.stderr)
            self.clangd_process.terminate()
            self.clangd_process.wait()


if __name__ == "__main__":
    # Example usage
    atomizer = CAtomizer(Path.cwd() / "examples" / "refinedc" / "src" / "example.c")
    atoms = atomizer.atomize()
    print(json.dumps([atom.jsonify() for atom in atoms], indent=2))
