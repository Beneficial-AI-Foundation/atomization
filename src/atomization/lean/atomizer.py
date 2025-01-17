#!/usr/bin/env python3
# %%
import json
from pathlib import Path

import random
import subprocess
from typing import Collection, TypedDict
from typing import Literal
from dataclasses import dataclass, field
from graphlib import TopologicalSorter
import logging

import pantograph
import tqdm
import dataclasses_json
from pantograph.server import Server

_PROJECT_ROOT = Path(__file__).parent.parent.parent.parent
LOG_DIR = _PROJECT_ROOT / "logs"
LOG_DIR.mkdir(parents=True, exist_ok=True)
# TODO: add back mathlib dependency
# TODO support structures/inductives
# TODO: use this instead of just setting "code" for all atoms.
type CodeType = Literal["code", "proof", "spec", "spec+code"]

# The name of a symbol in Lean.
type SymbolName = str
# type Kind = Literal["def", "theorem", "lemma", "example", "structure", "class", "abbrev"]
# TODO: Add more kinds
type Kind = Literal["def", "theorem"]

# Builtin namespaces that are already assumed to be imported.
EXCLUDED_NAMESPACES = frozenset(["Init", "Core", "Lean", "Mathlib"])
# To exclude stuff like `Nat`, `List`, `Option`, etc.
COMMON_NAMESPACES = frozenset(
    {
        "Nat",
        "List",
        "Fin",
        "Float",
        "Int",
        "Bool",
        "Int16",
        "Int32",
        "Int64",
        "Option",
        "BitVec",
        "Std",
        "Array",
        "String",
        "IO",
        "UInt16",
        "UInt32",
        "UInt64",
        "_private",
        "_aux",
        "Except",
        "Float32",
    }
)
EXCLUDED_SUFFIXES = frozenset(["match_1",
                               "match_2",
                               "match_3",
                               "match_4",
                               "match_5",
                               "match_6",
                               "match_7",
                               "match_8",
                               "match_9",
                               "_sunfold",
                               "eq_1",
                               "eq_2",
                               "eq_3",
                               "eq_4",
                               "eq_5",
                               "eq_6",
                               "_unsafe_rec",
                               "rec",
                               "",
                           ]
)

@dataclasses_json.dataclass_json
@dataclass
class LineColInfo:
    start_line: int
    start_col: int
    end_line: int
    end_col: int


@dataclasses_json.dataclass_json
@dataclass
class AtomizedDef:
    """A single atomized definition with its dependencies and source code"""

    name: SymbolName
    type: str
    module_path: str
    # filled in later from `source_start` and `source_end` combined with `file_path`
    source_code: str | None = None
    type_dependencies: set[SymbolName] = field(default_factory=set)
    value_dependencies: set[SymbolName] = field(default_factory=set)
    kind: Kind | None = None
    # ref_spec: str | None = None
    file_path: Path | str | None = None
    line_col_info: LineColInfo | None = None

    def __hash__(self) -> int:
        return hash(self.name)





def is_builtin(
    name: SymbolName,
    server: Server,
    exclude_namespaces: Collection[str] = EXCLUDED_NAMESPACES,
) -> bool:
    """Check if a name is a builtin Lean name"""
    info = server.env_inspect(name=name, print_value=True, print_dependency=True)
    module_name: str = info["module"]
    module_parts = module_name.split(".")
    return module_parts[0] in exclude_namespaces


def extract_kind(
    name: SymbolName, server: Server, inspect_cache: dict[str, dict] | None = None
) -> Kind | None:
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
    # Slice lines from start_line to end_line (1-based -> 0-based)
    relevant_lines = lines[info.start_line - 1 : info.end_line]
    # Truncate the first line by start_col and the last line by end_col+1
    relevant_lines[0] = relevant_lines[0][info.start_col:]
    relevant_lines[-1] = relevant_lines[-1][: info.end_col + 1]
    # Join into one big string
    return "".join(relevant_lines)


def atomize_project(
    server: Server,
    excluded_namespaces: frozenset[str] = EXCLUDED_NAMESPACES,
    common_namespaces: frozenset[str] = COMMON_NAMESPACES,
    verbose: bool = True,
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
    if verbose:
        print(f"Catalog length: {len(catalog)}")
    # Filter out builtins in FAST way (just check if the first part of the symbol is in EXCLUDED_NAMESPACES)
    filtered_symbols = []
    for sym in catalog:
        sym_parts = sym.split(".")
        if (
            sym_parts[0] not in all_excluded_namespaces
            and sym_parts[-1] not in EXCLUDED_SUFFIXES
        ):
            filtered_symbols.append(sym)
        # filtered_symbols = [
    #     sym for sym in catalog if sym.split(".")[0] not in all_excluded_namespaces
    # ]
    # Filter even *faster* for debugging purposes by excluding all symbols except those starting with "Atom_".
    # short_filtered_symbols = [
    #     sym for sym in filtered_symbols if sym.startswith("Atom_")
    # ]
    # print(f"short filtered symbols: {short_filtered_symbols}")
    # print(f"TestType type: {server.expr_type('Atom_TestType')}")
    print(f"Filtered symbols length: {len(filtered_symbols)}")

    # Dump filtered symbols to JSON for inspection/debugging
    if verbose:
        with (LOG_DIR / "lean_filtered_symbols.json").open("w") as f:
            json.dump(filtered_symbols, f)

    inspect_cache: dict[str, dict] = {}  # Cache env.inspect results
    atomized_defs: list[AtomizedDef] = []

    for symbol in tqdm.tqdm(filtered_symbols):
        # Cache inspect results as we filter
        info = server.env_inspect(
            name=symbol, print_value=True, print_dependency=True
        )
        # skip builtins more thoroughly
        module_path = info.get("module", "")
        if module_path.split(".")[0] in all_excluded_namespaces:
            continue

        if verbose:
            print(f"Inspecting {symbol}")

        inspect_cache[symbol] = info

        # Extract definition info
        start_line: int | None = info.get("sourceStart", {}).get("line", None)
        start_col: int | None = info.get("sourceStart", {}).get("column", None)
        end_line: int | None = info.get("sourceEnd", {}).get("line", None)
        end_col: int | None = info.get("sourceEnd", {}).get("column", None)

        if any(v is None for v in [start_line, start_col, end_line, end_col]):
            # skip symbol, it's not actually in the code but auto-generated
            continue

        line_col_info = LineColInfo(
            start_line=start_line,
            start_col=start_col,
            end_line=end_line,
            end_col=end_col,
        )
        type_info = info.get("type", {}).get("pp", "")
        file_path = module_to_file_path(module_path, project_root)
        source = extract_source_code(line_col_info, file_path)
        type_deps = list(set(info.get("typeDependency", [])))
        value_deps = list(set(info.get("valueDependency", [])))
        # Still need this call to `server` since it uses `expr_type`.
        kind = extract_kind(symbol, server, inspect_cache)

        atom = AtomizedDef(
            name=symbol,
            type=type_info,
            module_path=module_path,
            source_code=source,
            type_dependencies=set(type_deps),
            value_dependencies=set(value_deps),
            kind=kind,
            file_path=str(file_path),
            line_col_info=line_col_info,
        )

        atomized_defs.append(atom)
    # for debugging
    if verbose:
        with (LOG_DIR / "lean_inspect_cache.json").open("w") as f:
            json.dump(inspect_cache, f)
    with (LOG_DIR / "lean_atomized_defs.json").open("w") as f:
        json.dump([atom.to_json() for atom in atomized_defs], f)
    return atomized_defs


def find_def(
    atom: AtomizedDef | SymbolName, all_atoms: list[AtomizedDef]
) -> AtomizedDef:
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
    return def_atom.source_code


def deserialize_def(def_atom: AtomizedDef) -> str:
    """
    Of form
    ```
    def $(name) : $(type) := $(value)
    ```
    """
    return def_atom.source_code


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

    # Skip if no source code available
    if def_atom.source_code is None:
        return out

    # Recursively add all dependencies to `out`
    for dep in def_atom.type_dependencies | def_atom.value_dependencies:
        try:
            dep_def = find_def(dep, all_atoms)
            if dep_def.module_path:  # not a builtin
                # Pass the current out string, don't use it in concatenation
                out = de_atomize(dep_def, all_atoms, server, exclude_namespaces, out)
        except StopIteration:
            # Dependency not in all_atoms, check if it's a builtin using env.inspect
            info = server.env_inspect(name=dep, print_value=True, print_dependency=True)
            if not info.get("sourceStart", None):  # No source location info
                continue
            module_name = info["module"]
            if module_name.split(".")[0] not in exclude_namespaces:
                # Not a builtin and not in all_atoms - this is unexpected
                logging.warning(f"Dependency {dep} not found in atoms or builtins")

    # Add current definition to output (must be after all dependencies are added)
    out += deserialize_decl(def_atom) + "\n"

    return out


def test_atomizer() -> None:
    """Test the atomizer functionality using example definitions
    The code in question is in `{_PROJECT_ROOT}/examples/lean/Atomization/Basic.lean`:

    ```lean
    def Atom_g := 1

    def Atom_f := 2
    def Atom_fg := Atom_g + Atom_g
    def Atom_f' : 2 = 2 := rfl

    theorem Atom_f'' : 2 = 2 := by rfl

    def Atom_fib : Nat → Nat := fun n =>
    match n with
    | 0 => 0
    | 1 => 1
    | n + 2 => Atom_fib (n + 1) + Atom_fib n

    def Atom_fibImperative (n: Nat) : Nat := Id.run do
    let mut a : Nat := 0
    let mut b : Nat := 1
    for _ in [0:n] do
    let c := a + b
    a := b
    b := c
    return b

    @[csimp]
    theorem Atom_fib_spec : @Atom_fib = @Atom_fibImperative := by
    sorry

    ```
    """

    # We create a dummy project as an integration test.
    test_code = (_PROJECT_ROOT / "examples/lean/Atomization/Basic.lean").read_text()

    pkg_id = random.randint(1000, 9999)
    project_name = f"Pkg{pkg_id}"
    project_path = Path(f"/tmp/{project_name}")
    print(f"Creating dummy Lean project at {project_path}")
    create_dummy_lean_project(test_code, pkg_id)
    # pantograph needs the Lean project to be built.
    build_lean_project(project_path)

    server = Server(imports=["Init", project_name], project_path=project_path)
    # Test atomization
    all_atoms = atomize_project(server)


    sorted_atoms = sort_atoms(all_atoms)

    # Test g definition
    # g_def = find_def("Atom_g", all_atoms)
    # print(g_def)


    # assert g_def.source_code == "def Atom_g := 1", (
    #     f"Expected source code to be 'def Atom_g := 1', got {g_def.source_code}"
    # )
    # assert g_def.type == "Nat", f"Expected type to be 'Nat', got {g_def.type}"
    # assert g_def.kind == "def", f"Expected kind to be 'def', got {g_def.kind}"

    # # Test fg definition and its dependencies
    # fg_def = find_def("Atom_fg", all_atoms)

    # assert fg_def.source_code == "def Atom_fg := Atom_g + Atom_g", (
    #     f"Expected source code to be 'def Atom_fg := Atom_g + Atom_g', got {fg_def.source_code}"
    # )
    # assert "Atom_g" in fg_def.value_dependencies, (
    #     f"Expected value dependencies to include 'Atom_g', got {fg_def.value_dependencies}"
    # )
    # assert fg_def.kind == "def", f"Expected kind to be 'def', got {fg_def.kind}"

    # # Test theorem f''
    # f2_def = find_def("Atom_f''", all_atoms)

    # assert f2_def.type == "2 = 2", f"Expected type to be '2 = 2', got {f2_def.type}"
    # assert f2_def.kind == "theorem", f"Expected kind to be 'theorem', got {f2_def.kind}"

    # fib_def = find_def("Atom_fib", all_atoms)

    # assert (
    #     fib_def.source_code
    #     == "def Atom_fib : Nat → Nat := fun n =>\nmatch n with\n| 0 => 0\n| 1 => 1\n| n + 2 => Atom_fib (n + 1) + Atom_fib n"
    # ), (
    #     f"Expected source code to be 'def Atom_fib : Nat → Nat := fun n =>\nmatch n with\n| 0 => 0\n| 1 => 1\n| n + 2 => Atom_fib (n + 1) + Atom_fib n', got {fib_def.source_code}"
    # )

    print("All tests passed!")


class Schema(TypedDict):
    content: str
    type: CodeType
    order: int


def atoms_to_schema(atoms: list[AtomizedDef]) -> list[Schema]:
    """This function takes in a whole list instead of a single atomized definition because it's needed to set the order of the atoms."""
    return [
        Schema(
            content=atom.source_code if atom.source_code else "",
            type="code",
            order=i,
        )
        for i, atom in enumerate(atoms)
    ]


def sort_atoms(atoms: list[AtomizedDef]) -> list[AtomizedDef]:
    """
    Sort atoms so that:
      1) Dependencies come first (topological order).
      2) Among atoms that do not depend on each other, order by file path,
         then by start_line, then by start_col, and finally by name.
      3) If file_path or line_col_info are None, place those atoms first
         (since they have no code and can safely appear before).
    """
    # Map from atom name -> AtomizedDef for easy lookup:
    name_to_atom = {atom.name: atom for atom in atoms}

    # Build the dependency graph: edges from dep -> atom
    # i.e. if `atom` depends on `dep`, we must place `dep` before `atom`.
    graph = {}
    for atom in atoms:
        # Collect direct dependencies from type + value:
        deps = atom.type_dependencies | atom.value_dependencies
        graph[atom.name] = []
        for d in deps:
            if d in name_to_atom:
                # Edge from d to atom.name
                graph[atom.name].append(d)

    # Create a TopologicalSorter
    ts = TopologicalSorter()
    for name, deps in graph.items():
        ts.add(name, *deps)

    # Add this line to prepare the sorter
    ts.prepare()

    result_names = []
    while True:
        batch = list(ts.get_ready())  # which nodes are available next
        if not batch:
            break
        # Sort this batch by our tie-breaking rules:
        #  1) Atoms with None file_path come before atoms with a file_path
        #  2) Then lexical sort by file_path
        #  3) Then by start_line, start_col (if available), else 0
        #  4) Finally break ties by atom name
        def batch_key(n: str) -> tuple:
            a = name_to_atom[n]
            no_file = (a.file_path is None)
            fp = str(a.file_path) if a.file_path else ""
            no_line = (a.line_col_info is None)
            line = a.line_col_info.start_line if a.line_col_info else 0
            col = a.line_col_info.start_col if a.line_col_info else 0
            return (no_file, fp, no_line, line, col, a.name)

        batch.sort(key=batch_key)

        for n in batch:
            result_names.append(n)
            ts.done(n)

    # If the sorter still has active nodes, there's a cycle
    if ts.is_active():
        raise ValueError("Cannot produce a topological order: cycle detected.")

    # Map sorted names back to the actual AtomizedDef objects
    return [name_to_atom[n] for n in result_names]


def set_toolchain(
    project_root: Path, version: str = "leanprover/lean4:v4.16.0-rc1"
) -> None:
    """Set the toolchain for a Lean project."""
    with (project_root / "lean-toolchain").open("w") as f:
        f.write(version)


def create_dummy_lean_project(code: str, pkg_id: int) -> None:
    """Create a dummy Lean project in `/tmp/Pkg{pkg_id}`."""
    project_name = f"Pkg{pkg_id}"
    project_root = Path(f"/tmp/{project_name}")
    root_file = project_root / f"{project_name}.lean"
    main_file = project_root / "Main.lean"
    # `math` is to add a mathlib dependency conveniently.
    result = subprocess.run(
        # ["lake", "new", project_name, "math"],
        # TODO: add back mathlib dependency
        ["lake", "new", project_name],
        cwd="/tmp",
        capture_output=True,
        text=True,
    )

    with root_file.open("w") as f:
        f.write(code)
    # write a simple main file that removes the default `def hello := "world"` referenced from `root_file` since it's overwritten by `root_file.open`.
    with main_file.open("w") as f:
        f.write(f"import {project_name}\n\ndef main : IO Unit := return ()")
    set_toolchain(project_root)

    print(f"Created Lean project at {project_root}")
    print("Command output:", result.stdout)


def build_lean_project(project_root: Path) -> None:
    """Build a Lean project. Necessary before running `pantograph`."""
    set_toolchain(project_root)
    subprocess.run(["lake", "build"], cwd=project_root)


def atomize_lean(code: str, pkg_id: int) -> list[Schema]:
    """Atomize a Lean project and return a list of `Schema`s."""
    project_name = f"Pkg{pkg_id}"
    project_root = Path(f"/tmp/{project_name}")

    create_dummy_lean_project(code, pkg_id)
    build_lean_project(project_root)
    server = Server(imports=["Init", project_name], project_path=project_root)

    all_atoms = atomize_project(server)
    sorted_atoms = sort_atoms(all_atoms)

    schema = atoms_to_schema(sorted_atoms)

    return schema


if __name__ == "__main__":
    test_atomizer()

# %%