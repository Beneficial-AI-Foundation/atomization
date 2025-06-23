import pytest
import logging
import asyncio
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
async def dafny_lsp_client():
    """Fixture providing a Dafny LSP client instance."""
    # Use dafny command from the environment (should be available via nix develop)
    transport = JsonRpcTransport(["dafny", "server"])
    await transport.start()
    client = DafnyAtomizer(transport)
    await client.initialize()
    yield client
    # Cleanup: close transport
    await transport.close()


@pytest.mark.asyncio
async def test_symbol_kinds_from_examples(dafny_lsp_client, dafny_example_files):
    """Test symbol discovery and verify what 'kind' values are returned."""
    # Test with sum.dfy - contains a function
    sum_content = dafny_example_files["sum"].read_text()
    sum_uri = f"file://{dafny_example_files['sum'].absolute()}"

    await dafny_lsp_client.open_file(sum_uri, sum_content)
    # Wait for LSP server to process the file
    await asyncio.sleep(2)
    symbols_sum = await dafny_lsp_client.request_all_symbols()

    # Test with class_example.dfy - contains methods and classes
    class_content = dafny_example_files["class_example"].read_text()
    class_uri = f"file://{dafny_example_files['class_example'].absolute()}"

    await dafny_lsp_client.open_file(class_uri, class_content)
    # Wait for LSP server to process the file
    await asyncio.sleep(2)
    symbols_class = await dafny_lsp_client.request_all_symbols()

    # Combine all symbols
    all_symbols = symbols_sum + symbols_class

    # Print all symbols and their kinds for debugging
    print(f"\nFound {len(all_symbols)} symbols:")
    for sym in all_symbols:
        print(f"  {sym.name}")

    # The current implementation only collects symbols with kind == 12
    # Let's verify this assumption
    assert len(all_symbols) > 0, "Should have found some symbols"

    # All collected symbols should be methods according to current filter
    for sym in all_symbols:
        assert isinstance(sym, DafnySymbol)
        assert sym.name is not None
        assert sym.uri is not None


@pytest.mark.asyncio
async def test_all_symbol_kinds_investigation(dafny_lsp_client, dafny_example_files):
    """Modified version that captures ALL symbol kinds to investigate what Dafny LSP returns."""
    # Load multiple files to get diverse symbols
    for file_key, file_path in dafny_example_files.items():
        content = file_path.read_text()
        uri = f"file://{file_path.absolute()}"
        await dafny_lsp_client.open_file(uri, content)

    # Wait for LSP server to process all files
    await asyncio.sleep(3)

    # Request symbols using debug method
    all_symbols_with_kinds = await dafny_lsp_client.request_all_symbols_debug()

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
