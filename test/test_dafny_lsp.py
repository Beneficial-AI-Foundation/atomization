import pytest
import logging
from pathlib import Path
from atomization.dafny.lsp_client import DafnyAtomizer, DafnySymbol
from atomization.common.lsp.transport import JsonRpcTransport

# Enable debug logging for LSP communication
logging.basicConfig(level=logging.DEBUG)
logging.getLogger("atomization.dafny.lsp_client").setLevel(logging.DEBUG)
logging.getLogger("atomization.common.lsp.transport").setLevel(logging.DEBUG)


@pytest.fixture
def dafny_example_files():
    """Fixture providing paths to Dafny example files."""
    examples_dir = Path(__file__).parent.parent / "examples" / "dafny"
    return {
        "sum": examples_dir / "sum.dfy",
        "class_example": examples_dir / "class_example.dfy",
        "fibonacci": examples_dir / "fibonacci.dfy",
    }


@pytest.fixture
def dafny_lsp_client():
    """Fixture providing a Dafny LSP client instance."""
    # Use dafny command from the environment (should be available via nix develop)
    transport = JsonRpcTransport(["dafny", "server"])
    client = DafnyAtomizer(transport)
    client.initialize()
    yield client
    # Cleanup: terminate the subprocess
    if client.transport.proc:
        client.transport.proc.terminate()


def test_symbol_kinds_from_examples(dafny_lsp_client, dafny_example_files):
    """Test symbol discovery and verify what 'kind' values are returned."""
    collected_symbols = []

    def collect_symbols(symbols):
        collected_symbols.extend(symbols)

    # Test with sum.dfy - contains a function
    sum_content = dafny_example_files["sum"].read_text()
    sum_uri = f"file://{dafny_example_files['sum'].absolute()}"

    dafny_lsp_client.open_file(sum_uri, sum_content)
    dafny_lsp_client.request_all_symbols(collect_symbols)

    # Wait a moment for LSP response (in real usage you'd use proper async handling)
    import time

    time.sleep(2)

    # Test with class_example.dfy - contains methods and classes
    class_content = dafny_example_files["class_example"].read_text()
    class_uri = f"file://{dafny_example_files['class_example'].absolute()}"

    dafny_lsp_client.open_file(class_uri, class_content)
    dafny_lsp_client.request_all_symbols(collect_symbols)

    time.sleep(2)

    # Print all symbols and their kinds for debugging
    print(f"\nFound {len(collected_symbols)} symbols:")
    for sym in collected_symbols:
        print(f"  {sym.name} (kind: {getattr(sym, 'kind', 'unknown')})")

    # The current implementation only collects symbols with kind == 12
    # Let's verify this assumption
    assert len(collected_symbols) > 0, "Should have found some symbols"

    # All collected symbols should be methods according to current filter
    for sym in collected_symbols:
        assert isinstance(sym, DafnySymbol)
        assert sym.name is not None
        assert sym.uri is not None


def test_all_symbol_kinds_investigation(dafny_lsp_client, dafny_example_files):
    """Modified version that captures ALL symbol kinds to investigate what Dafny LSP returns."""
    all_symbols_with_kinds = []

    def collect_all_symbols(symbols):
        """Collect all symbols regardless of kind."""
        all_symbols_with_kinds.extend(symbols)

    # Load multiple files to get diverse symbols
    for file_key, file_path in dafny_example_files.items():
        content = file_path.read_text()
        uri = f"file://{file_path.absolute()}"
        dafny_lsp_client.open_file(uri, content)

    # Give the server time to process the files
    import time

    time.sleep(2)

    # Request symbols using debug method
    dafny_lsp_client.request_all_symbols_debug(collect_all_symbols)

    # Wait for response
    time.sleep(3)

    # Print findings
    print(f"\nInvestigation Results - Found {len(all_symbols_with_kinds)} symbols:")
    print("=" * 60)

    kind_counts = {}
    for sym in all_symbols_with_kinds:
        kind = sym["kind"]
        kind_counts[kind] = kind_counts.get(kind, 0) + 1
        print(
            f"  {sym['name']:<20} | kind: {kind:2d} | {Path(sym['uri']).name if sym['uri'] != 'unknown' else 'unknown'}"
        )

    print("\nSymbol Kind Summary:")
    for kind, count in sorted(kind_counts.items()):
        print(f"  Kind {kind:2d}: {count} symbols")

    # Verify we found symbols
    assert len(all_symbols_with_kinds) > 0, "Should have found symbols to investigate"

    # Check if kind 12 is actually present
    kind_12_symbols = [s for s in all_symbols_with_kinds if s["kind"] == 12]
    kind_6_symbols = [s for s in all_symbols_with_kinds if s["kind"] == 6]

    print(f"\nKind 12 symbols: {len(kind_12_symbols)}")
    for s in kind_12_symbols:
        print(f"  - {s['name']}")

    print(f"\nKind 6 symbols: {len(kind_6_symbols)}")
    for s in kind_6_symbols:
        print(f"  - {s['name']}")
