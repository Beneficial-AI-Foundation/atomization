# %%
import json
from pathlib import Path
from typing import TypedDict, List, Optional, Set, Dict, Any, Collection
from typing import Literal
from dataclasses import dataclass, field
from os import PathLike
import pantograph
import re
import logging
from pantograph.server import Server
import tempfile
import tqdm

#TODO support structures/inductives

type Name = str
# type Kind = Literal["def", "theorem", "lemma", "example", "structure", "class", "abbrev"]
# TODO: Add more kinds
type Kind = Literal["def", "theorem"]
# TODO: Add more builtins
EXCLUDED_NAMESPACES = frozenset(["Init", "Core", "Lean", "Mathlib"])
# to exclude stuff like `Nat`, `List`, `Option`, etc.
COMMON_NAMESPACES = frozenset({"Nat", "List", "Fin","Float","Int","Bool","Int16","Int32","Int64", "Option", "BitVec", "Std","Array","String","IO","UInt16","UInt32","UInt64","_private","_aux","Except","Float32",})

@dataclass
class AtomizedDef:
    """A single atomized definition with its dependencies and source code"""

    name: Name
    type: str
    module_path: str
    # filled in later from `source_start` and `source_end` combined with `file_path`
    source_code: str | None = None
    type_dependencies: Set[Name] = field(default_factory=set)
    value_dependencies: Set[Name] = field(default_factory=set)
    kind: Kind | None = None
    # ref_spec: str | None = None
    file_path: Path | None = None


    def __hash__(self) -> int:
        return hash(self.name)

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, AtomizedDef) and self.name == other.name


@dataclass
class LineColInfo:
    start_line: int
    start_col: int
    end_line: int
    end_col: int


def is_builtin(
    name: Name,
    server: Server,
    exclude_namespaces: Collection[str] = EXCLUDED_NAMESPACES,
) -> bool:
    """Check if a name is a builtin Lean name"""
    info = server.env_inspect(name=name, print_value=True, print_dependency=True)
    module_name: str = info["module"]
    module_parts = module_name.split(".")
    return module_parts[0] in exclude_namespaces


def extract_kind(
    name: Name, server: Server, inspect_cache: Optional[Dict[str, dict]] = None
) -> Optional[Kind]:
    """Extract the kind of definition (def/theorem/etc) from source"""
    if inspect_cache and name in inspect_cache:
        type_info = inspect_cache[name]["type"]["pp"]
    else:
        type_info = server.env_inspect(
            name=name, print_value=True, print_dependency=True
        )["type"]["pp"]

    type = server.expr_type(type_info)
    if type == "Prop":
        return "theorem"
    else:  # TODO: Add more kinds
        return "def"


def module_to_file_path(module_path: str, project_root: Path) -> Path:
    """Convert a module path to a file path

    Example:
    "Atomization.Basic" -> "Atomization/Basic.lean"
    """
    return project_root / Path(module_path.replace(".", "/") + ".lean")


def extract_source_code(
    info: LineColInfo,
    file_path: Path,
) -> str:
    """Extract the source code of a definition."""
    with file_path.open() as f:
        lines = f.readlines()
    # Adjust for 1-based line indexing in json. Column indexing is already 0-based.
    return "".join(lines[info.start_line - 1 : info.end_line])[
        info.start_col : info.end_col
    ]


def atomize_file(
    server: Server, excluded_namespaces: frozenset[str] = EXCLUDED_NAMESPACES, common_namespaces: frozenset[str] = COMMON_NAMESPACES
) -> list[AtomizedDef]:
    """
    Atomize a Lean file into its individual sub definitions using Pantograph's env.inspect
    and extract their dependencies recursively.
    """
    # Get project root from server
    project_root = Path(server.project_path)
    all_excluded_namespaces = excluded_namespaces | common_namespaces
    # First pass: Get all definitions and their basic info. Drop the first character of each symbol, which signifies its type (def/theorem/etc)
    catalog = [sym[1:] for sym in server.run("env.catalog", {})["symbols"]]
    print(f"Catalog length: {len(catalog)}")
    # Filter out builtins in FAST way (just check if the first part of the symbol is in EXCLUDED_NAMESPACES)
    filtered_symbols = [
        sym for sym in catalog if sym.split(".")[0] not in all_excluded_namespaces
    ]
    print(f"Filtered symbols length: {len(filtered_symbols)}")
    # Dump filtered symbols to JSON for inspection/debugging
    with Path("/Users/alokbeniwal/atomization/filtered_symbols.json").open("w") as f:
        json.dump(filtered_symbols, f)
    inspect_cache: Dict[str, dict] = {}  # Cache env.inspect results

    for symbol in tqdm.tqdm(filtered_symbols):
        # print(f"Inspecting {symbol}")
        try:
            # Cache inspect results as we filter
            inspect_cache[symbol] = server.env_inspect(
                name=symbol, print_value=True, print_dependency=True
            )
        except pantograph.ServerError as e:
            print(f"Warning: Failed to inspect {symbol}: {e}")
            continue
    # for debugging
    with Path("/Users/alokbeniwal/atomization/inspect_cache.json").open("w") as f:
        json.dump(inspect_cache, f)

    
    atomized_defs: list[AtomizedDef] = []
    
    # Collect module paths from cached inspect results
    for symbol in tqdm.tqdm(filtered_symbols):
        info = inspect_cache[symbol]

        module_path = info.get("module", "")
        # Extract definition info
        line_col_info = LineColInfo(
            start_line=info.get("sourceStart", {}).get("line", 0),
            start_col=info.get("sourceStart", {}).get("column", 0),
            end_line=info.get("sourceEnd", {}).get("line", 0),
            end_col=info.get("sourceEnd", {}).get("column", 0),
        )
        type_info = info.get("type", {}).get("pp", "")
        file_path = module_to_file_path(module_path, project_root)
        source = extract_source_code(line_col_info, file_path)
        type_deps = list(set(info.get("typeDependency", [])))
        value_deps = list(set(info.get("valueDependency", [])))
        # Still need this call to `server` since it uses `expr_type`.
        kind = extract_kind(
            symbol, server, inspect_cache
        ) 

        atom = AtomizedDef(
            name=symbol,
            type=type_info,
            module_path=module_path,
            source_code=source,
            type_dependencies=set(type_deps),
            value_dependencies=set(value_deps),
            kind=kind,
            file_path=file_path,
        )


        atomized_defs.append(atom)

    return atomized_defs



def find_def(atom: AtomizedDef | Name, all_atoms: list[AtomizedDef]) -> AtomizedDef:
    if isinstance(atom, AtomizedDef):
        return next((d for d in all_atoms if d.name == atom.name))
    else:
        return next((d for d in all_atoms if d.name == atom))


def deserialize_theorem(def_atom: AtomizedDef) -> str:
    """
    Of form
    ```
    theorem $(name) : $(type) := $(proof)
    ```

    """
    return f"theorem {def_atom.name} : {def_atom.type} := {def_atom.source_code}"


def deserialize_def(def_atom: AtomizedDef) -> str:
    """
    Of form
    ```
    def $(name) : $(type) := $(value)
    ```
    """
    return f"def {def_atom.name} : {def_atom.type} := {def_atom.source_code}"


def deserialize_decl(def_atom: AtomizedDef) -> str:
    if def_atom.kind == "theorem":
        return deserialize_theorem(def_atom)
    elif def_atom.kind == "def":
        return deserialize_def(def_atom)
    else:
        raise ValueError(f"Unknown kind: {def_atom.kind}")


def de_atomize(
    def_atom: AtomizedDef,
    all_atoms: list[AtomizedDef],
    server: Server,
    exclude_namespaces: Collection[str] = EXCLUDED_NAMESPACES,
    out: str = "",
) -> str:
    # if a builtin, return `out` (base case of recursion)
    if is_builtin(def_atom.name, server, exclude_namespaces):
        return out

    # Recursively add all dependencies to `out`
    for dep in def_atom.type_dependencies | def_atom.value_dependencies:
        dep_def = find_def(dep, all_atoms)
        if dep_def.module_path:  # not a builtin
            # Pass the current out string, don't use it in concatenation
            out = de_atomize(dep_def, all_atoms, server, exclude_namespaces, out)

    # Add current definition to output (must be after all dependencies are added)
    out += deserialize_decl(def_atom) + "\n"

    return out


def test_atomizer() -> None:
    """Test the atomizer functionality using example definitions
    The code in question is in `Atomization/Basic.lean`:

    ```lean
    def g := 1

    def f := 2
    def fg := g + g
    def f' : 2 = 2 := rfl

    theorem f'' : 2 = 2 := by rfl

    def fib : Nat → Nat := fun n =>
    match n with
    | 0 => 0
    | 1 => 1
    | n + 2 => fib (n + 1) + fib n

    def fibImperative (n: Nat) : Nat := Id.run do
    let mut a : Nat := 0
    let mut b : Nat := 1
    for i in [0:n] do
    let c := a + b
    a := b
    b := c
    return b

    @[csimp]
    theorem fib_spec : @fib = @fibImperative := by
    sorry

    ```
    """

    project_path = "/Users/alokbeniwal/atomization"
    server = Server(imports=["Init", "Atomization"], project_path=project_path)
    # Test atomization
    all_atoms = atomize_file(server)
    print(f"Atomized: {len(all_atoms)} atoms")

    # Test g definition
    g_def = find_def("g", all_atoms)
    print(g_def)

    assert g_def.source_code == "1", f"Expected source code to be '1', got {g_def.source_code}"
    assert g_def.type == "Nat", f"Expected type to be 'Nat', got {g_def.type}"
    assert g_def.kind == "def", f"Expected kind to be 'def', got {g_def.kind}"

    # Test fg definition and its dependencies
    fg_def = find_def("fg", all_atoms)
    print(fg_def)

    assert fg_def.source_code == "g + g", f"Expected source code to be 'g + g', got {fg_def.source_code}"
    assert "g" in fg_def.value_dependencies, f"Expected value dependencies to include 'g', got {fg_def.value_dependencies}"
    assert fg_def.kind == "def", f"Expected kind to be 'def', got {fg_def.kind}"

    # Test theorem f''
    f2_def = find_def("f''", all_atoms)
    print(f2_def)

    assert f2_def.type == "2 = 2", f"Expected type to be '2 = 2', got {f2_def.type}"    
    assert f2_def.kind == "theorem", f"Expected kind to be 'theorem', got {f2_def.kind}"
    assert "f" in f2_def.type_dependencies, f"Expected type dependencies to include 'f', got {f2_def.type_dependencies}"
    assert "f" in f2_def.value_dependencies, f"Expected value dependencies to include 'f', got {f2_def.value_dependencies}"

    # Test ref spec for fib and fibImperative
    fib_def = find_def("fib", all_atoms)
    fib_imp_def = find_def("fibImperative", all_atoms)
    print(f"fib def: {fib_def}")
    print(f"fibImperative def: {fib_imp_def}")

    print("All tests passed!")

if __name__ == "__main__":
    test_atomizer()

# %%
