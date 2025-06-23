import asyncio
from atomization.dafny.parser import parse_dafny
from atomization.dafny.lsp_client import DafnyAtomizer, DafnySymbol
from atomization.common.lsp.transport import JsonRpcTransport


def atomize_dafny_rgx(content: str) -> list:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:
        parsed_dafny = parse_dafny(content)
        return parsed_dafny

    except Exception as e:
        print(f"Debug - Exception details: {type(e).__name__}: {str(e)}")
        raise Exception(f"Error analyzing {content}: {str(e)}")


async def atomize_dafny_async(
    content: str, timeout: float = 3.0
) -> tuple[list[DafnySymbol], dict[str, list[str]]]:
    """Atomize Dafny code using LSP (async version).

    Args:
        content (str): The Dafny code to atomize.
        timeout (float): Timeout for the LSP processing in seconds.

    Returns:
        tuple: (List of DafnySymbol objects, dependency graph dict)
    """
    # Set up transport and client
    transport = JsonRpcTransport(["dafny", "server"])
    await transport.start()

    try:
        atomizer = DafnyAtomizer(transport)
        await atomizer.initialize()
        await atomizer.open_file("file:///temp.dfy", content)

        # Wait for LSP to process
        await asyncio.sleep(timeout)

        symbols = await atomizer.request_all_symbols()
        dependencies = await atomizer.build_dependency_graph(symbols, content)

        return symbols, dependencies
    finally:
        await transport.close()


def atomize_dafny(
    content: str, timeout: int = 3000
) -> tuple[list[DafnySymbol], dict[str, list[str]]]:
    """Atomize Dafny code using LSP and return symbols with dependencies.

    Args:
        content (str): The Dafny code to atomize.
        timeout (int): Timeout for the LSP request in milliseconds.

    Returns:
        tuple: (List of DafnySymbol objects, dependency graph dict)
    """
    return asyncio.run(atomize_dafny_async(content, timeout / 1000.0))


def jsonify_vlib(
    symbols: list[DafnySymbol],
    source_content: str = "",
    dependencies: dict[str, list[str]] | None = None,
) -> dict:
    """Convert symbols to vlib JSON format matching the schema.

    Args:
        symbols: List of DafnySymbol objects
        source_content: Original source code content
        dependencies: Optional dependency graph mapping symbol names to their dependencies

    Returns:
        Dict matching the vlib schema with data map from names to [dependencies, code] pairs
    """
    data = {}

    for symbol in symbols:
        # Use provided dependencies or empty list
        symbol_dependencies = dependencies.get(symbol.name, []) if dependencies else []

        # Extract the function/method code from source if available
        code = f"// Symbol: {symbol.name} at {symbol.uri}:{symbol.position}"
        if source_content:
            lines = source_content.split("\n")
            start_line = symbol.position.get("line", 0)
            if start_line < len(lines):
                # Find the function/method definition by looking for the full block
                current_line = start_line
                function_lines = []
                brace_count = 0
                in_function = False

                while current_line < len(lines):
                    line = lines[current_line]
                    function_lines.append(line)

                    # Count braces to find the end of the function
                    for char in line:
                        if char == "{":
                            brace_count += 1
                            in_function = True
                        elif char == "}":
                            brace_count -= 1

                    # If we've closed all braces and we were in a function, we're done
                    if in_function and brace_count == 0:
                        break

                    current_line += 1

                if function_lines:
                    code = "\n".join(function_lines).strip()

        data[symbol.name] = [symbol_dependencies, code]

    return {"data": data}
