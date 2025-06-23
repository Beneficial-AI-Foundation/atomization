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
uv run test                    # Run the full test suite
uv run pytest test/specific_test.py  # Run specific test file
```

### Linting and Formatting

```bash
uv run ruff check             # Lint code
uv run ruff format            # Format code
uv run pyright               # Type checking
```

### Running the Atomizer

```bash
uv run main <code_id>         # Atomize code with given database ID
uv run main test              # Test database connection
uv run main delete <package_id>  # Delete package and cleanup
uv run main delete-atoms <code_id>  # Delete atoms for code
```

### Docker Usage (Production)

```bash
docker-compose run --remove-orphans atomization test
docker-compose run atomization <code_id>
docker-compose run atomization delete <package_id>
```

### Dry Run Examples

```bash
uv run dry_coq <filename>     # Dry run Coq atomizer on examples/coq/<filename>.v
uv run dry rocq <filepath>    # Dry run Coq atomizer on arbitrary file
```

## Architecture

### Core Components

The atomizer supports multiple formal verification languages:

1. **Dafny Atomizer** (`src/atomization/dafny/`): Breaks Dafny code into spec, code, and proof atoms
2. **Coq Atomizer** (`src/atomization/coq/`): Processes Coq/Rocq files using coqpyt
3. **Lean Atomizer** (`src/atomization/lean/`): Handles Lean 4 code via PyPantograph
4. **Isabelle Atomizer** (`src/atomization/isabelle/`): Processes Isabelle/HOL theories with Scala backend

### LSP Integration

The system includes Language Server Protocol (LSP) clients for enhanced code analysis:

**Common LSP Framework** (`src/atomization/common/lsp/`):

- `JsonRpcTransport`: JSON-RPC transport layer over subprocess communication
- `AtomizerPlugin`: Abstract base class for language-specific LSP clients

**Dafny LSP Client** (`src/atomization/dafny/lsp_client.py`):

- `DafnyAtomizer`: Concrete implementation for Dafny LSP integration
- Supports symbol discovery via `workspace/symbol` requests
- Enables reference finding via `textDocument/references` requests
- Handles file opening with `textDocument/didOpen` notifications

The LSP clients enable:

- Symbol extraction from workspace
- Reference tracking across files
- Real-time code analysis through language servers
- Enhanced dependency analysis for atomization

### Database Integration

The system integrates with a MySQL database (`verilib`) containing:

- `codes` table: Source code entries with language metadata
- `packages` table: Atomized packages linking to original code
- `snippets` table: Code fragments (for Dafny only currently)
- `atoms` table: Atomic program elements with dependencies
- `atomsdependencies` table: Dependency relationships between atoms

### Language Support Matrix

| Language | Snippet Creation | Atom Creation | Database Tables          |
| -------- | ---------------- | ------------- | ------------------------ |
| Dafny    | ✅               | ❌            | packages, snippets       |
| Lean     | ❌               | ✅            | atoms, atomsdependencies |
| Isabelle | ❌               | ✅            | atoms, atomsdependencies |
| Coq      | ❌               | ❌            | (snippets planned)       |

### Atom Types

The atomizer categorizes code elements into:

- **spec**: Specifications (requires, ensures, etc.)
- **code**: Executable code (methods, functions)
- **proof**: Proof elements (lemmas, assertions, invariants)
- **spec+code**: Combined specification and implementation headers

## Environment Configuration

The application requires these environment variables:

- `DB_PASSWORD`: MySQL database password
- `DB_HOST`: Database host (defaults to localhost)

Database connection details are configured in `.env` file.

## Testing Strategy

Tests are organized in `test/` directory mirroring `src/` structure:

- Unit tests for individual atomizers
- Database integration tests
- Language-specific test files for each supported language

Examples for each language are provided in `examples/` directory for development and testing.
