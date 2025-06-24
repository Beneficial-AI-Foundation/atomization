# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Development Environment

This project uses Nix flakes for environment management. To set up the development environment:

```bash
nix develop
uv sync
```

This provides access to:

- Python 3.12+ with uv package manager
- Coq with coq-lsp and dune
- Lean 4 (via elan)
- Isabelle/HOL
- Dafny
- Additional tools: nodejs, jq, graphviz

## Common Commands

### Testing

```bash
uv run pytest                    # Run local tests (excludes networked tests)
PYTEST_ADDOPTS="" uv run pytest  # Run all tests including networked (on server)
uv run pytest test/specific_test.py  # Run specific test file
uv run pytest test/test_dafny_lsp.py -v  # Run with verbose output
```

### Linting and Formatting

```bash
uv run ruff check --fix          # Lint and auto-fix code
uv run ruff format               # Format code
uv run pyright                   # Type checking
```

### Running the Atomizer

```bash
uv run atomize <code_id>         # Atomize code with given database ID
uv run atomize test              # Test database connection
uv run atomize delete <package_id>  # Delete package and cleanup
```

### Dry Run Examples (No Database)

```bash
uv run dry dafny examples/dafny/sum.dfy      # Test Dafny LSP atomization
uv run dry rocq examples/coq/example.v      # Test Coq atomization
uv run dry_coq <filename>                   # Dry run Coq atomizer on examples/coq/<filename>.v
```

### Docker Usage (Production)

```bash
docker-compose run --remove-orphans atomization test
docker-compose run atomization <code_id>
docker-compose run atomization delete <package_id>
```

## Architecture

### Async LSP Architecture

The system is built around async Language Server Protocol (LSP) clients for real-time code analysis:

**Core LSP Framework** (`src/atomization/common/lsp/`):

- `JsonRpcTransport`: Async JSON-RPC transport using `asyncio` subprocess communication
- `AtomizerPlugin`: Abstract base class defining async LSP interface
- All LSP operations use `async/await` patterns instead of blocking calls

**Key LSP Methods**:

- `async def initialize()`: Setup LSP server capabilities
- `async def open_file()`: Notify server about file changes
- `async def request_all_symbols()`: Extract symbols via `workspace/symbol`
- `async def build_dependency_graph()`: Analyze symbol dependencies

### Dafny LSP Implementation

**DafnyAtomizer** (`src/atomization/dafny/lsp_client.py`):

- Captures Classes (kind 5), Methods (kind 6), and Functions (kind 12)
- Performs dependency analysis by parsing symbol references in code
- Extracts full symbol definitions including specifications and proofs
- Outputs JSON format: `{"data": {"symbol_name": [["dependencies"], "source_code"]}}`

**Two-tier Architecture**:

- `atomize_dafny_async()`: Core async implementation returning symbols + dependencies
- `atomize_dafny()`: Synchronous wrapper for backward compatibility
- `atomize_dafny_with_deps()`: Returns both symbols and dependency graph

### Multi-Language Support

1. **Dafny**: LSP-based with dependency analysis, creates snippets in database
2. **Coq/Rocq**: Uses coqpyt library for parsing and analysis
3. **Lean**: Uses PyPantograph (optional dependency), creates atoms in database
4. **Isabelle**: Scala backend integration, creates atoms in database

### Database Schema

**MySQL database (`verilib`) tables**:

- `codes`: Source code entries with language metadata
- `packages`: Atomized packages linking to original code
- `snippets`: Code fragments (Dafny only)
- `atoms`: Atomic program elements with dependencies (Lean, Isabelle)
- `atomsdependencies`: Dependency relationships between atoms

### Testing Architecture

**Test Organization**:

- `test/`: Local tests (run by default)
- `test/networked/`: Database integration tests (require `PYTEST_ADDOPTS=""`)
- Async tests use `@pytest.mark.asyncio` with proper fixtures
- LSP tests include timing delays (`await asyncio.sleep()`) for server processing

## Important Implementation Details

### LSP Timing Considerations

- LSP servers need processing time after `textDocument/didOpen` before `workspace/symbol` requests
- Use `await asyncio.sleep(2-3)` delays in tests and atomization functions
- This is due to server-side parsing, not async implementation issues

### Dependency Management

- Lean atomizer depends on `pantograph` which may fail to build
- Use optional imports with graceful degradation:
  ```python
  try:
      from atomization.lean.atomizer import atomize_lean
  except ImportError:
      atomize_lean = None
  ```

### Symbol Dependency Analysis

- Text-based analysis using regex patterns to find symbol references
- Filters out self-references and method definitions within classes
- Distinguishes between actual function calls and symbol definitions
- Returns dependency mappings compatible with vlib JSON schema

## Environment Configuration

Required environment variables:

- `DB_PASSWORD`: MySQL database password
- `DB_HOST`: Database host (defaults to localhost)

Database connection details are configured in `.env` file.
