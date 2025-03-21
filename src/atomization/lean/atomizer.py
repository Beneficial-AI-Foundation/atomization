#!/usr/bin/env python3
# %%
import json
from pathlib import Path
import subprocess
from typing import Collection, TypedDict
from typing import Literal
from dataclasses import dataclass, field
from graphlib import TopologicalSorter
import logging

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
# TODO fix inductive variants by excluding them if their source code matches r"\W+|.*$" (just a match arm).
# TODO report that structures don't parse to Leni.
# The name of a symbol in Lean.
type SymbolName = str
# type Kind = Literal["def", "theorem", "lemma", "example", "structure", "class", "abbrev","inductive"]
# TODO: Add more kinds
# type ProofKind = Literal["theorem","lemma"]
type Kind = Literal["code", "proof"]

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
EXCLUDED_SUFFIXES = frozenset(
    [
        "match_1",
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
        "brecOn",
        "recOn",
        "casesOn",
        "binductionOn",
        "below",
        "ibelow",
        "noConfusion",
        "inj",
        "injEq",
        "sizeOf_spec",
        "noConfusionType",
        "_sizeOf_inst",
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

    try:
        type = server.expr_type(type_info)
    except Exception as e:  # TODO refine exception type
        error_str = str(e)
        # Error: unknown universe level '`u'. The [1:] is to drop the backtick.
        universe_level = error_str.split("'")[1][1:]
        # probably an inductive, missing universe levels
        try:
            type = server.run(
                "expr.echo", {"expr": type_info, "levels": [universe_level]}
            )["type"]
        except Exception as e:
            print(f"Error 2: {e}")
            raise e

    if type == "Prop":
        return "proof"
    else:
        return "code"


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
    relevant_lines[0] = relevant_lines[0][info.start_col :]
    relevant_lines[-1] = relevant_lines[-1][: info.end_col + 1]
    # Join into one big string
    return "".join(relevant_lines)


def atomize_project(
    server: Server,
    excluded_namespaces: frozenset[str] = EXCLUDED_NAMESPACES,
    common_namespaces: frozenset[str] = COMMON_NAMESPACES,
    verbose: bool = False,
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

    # Dump filtered symbols to JSON for inspection/debugging
    if verbose:
        with (LOG_DIR / "lean_filtered_symbols.json").open("w") as f:
            json.dump(filtered_symbols, f)

    inspect_cache: dict[str, dict] = {}  # Cache env.inspect results
    atomized_defs: list[AtomizedDef] = []

    for symbol in tqdm.tqdm(filtered_symbols):
        # Cache inspect results as we filter
        info = server.env_inspect(name=symbol, print_value=True, print_dependency=True)
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


class Schema(TypedDict):
    """The schema of an atomized definition."""

    identifier: str
    body: str
    type: CodeType
    language: Literal["lean"]
    deps: list["Schema"]


def atoms_to_schema(atoms: Collection[AtomizedDef]) -> list[Schema]:
    """This function takes in a whole list instead of a single atomized definition because it's needed to set the order of the atoms."""
    out: list[Schema] = []
    name_to_atom: dict[str, AtomizedDef] = {atom.name: atom for atom in atoms}
    for atom in atoms:
        deps = []
        deps = [
            Schema(
                identifier=dep,
                # type: ignore
                body=name_to_atom[dep].source_code
                if name_to_atom[dep].source_code is not None
                else "",
                type="code" if name_to_atom[dep].kind == "def" else "proof",
                language="lean",
                deps=[],  # TODO this should be recursive?
            )
            for dep in atom.type_dependencies | atom.value_dependencies
            if dep in name_to_atom
        ]
        out.append(
            Schema(
                identifier=atom.name,
                body=atom.source_code if atom.source_code else "",
                type="code" if atom.kind == "def" else "proof",
                language="lean",
                deps=deps,
            )
        )
    return out


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
            no_file = a.file_path is None
            fp = str(a.file_path) if a.file_path else ""
            no_line = a.line_col_info is None
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
    project_root.mkdir(parents=True, exist_ok=True)

    with (project_root / "lean-toolchain").open("w") as f:
        f.write(version)


def create_dummy_lean_project(code: str, pkg_id: int) -> None:
    """Create a dummy Lean project in `/home/ec2-user/lean_projects/Pkg{pkg_id}`."""
    project_name = f"Pkg{pkg_id}"
    # Create base directory for Lean projects in home directory
    base_dir = Path("/home/ec2-user/lean_projects")
    base_dir.mkdir(parents=True, exist_ok=True)
    
    project_root = base_dir / project_name
    root_file = project_root / f"{project_name}.lean"
    main_file = project_root / "Main.lean"
    
    # First check if the directory already exists, and if not, create it
    if not project_root.exists():
        result = subprocess.run(
            ["lake", "new", project_name],
            cwd=str(base_dir),
            capture_output=True,
            text=True,
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"Failed to create Lean project: {result.stderr}")
            
        print(f"Created Lean project at {project_root}")
        print("Command output:", result.stdout)
    else:
        print(f"Using existing Lean project at {project_root}")
    
    # Create a proper lakefile.lean with mathlib support
    lakefile_content = f"""import Lake
open Lake DSL

package «{project_name}» where
-- Settings applied to both builds and interactive editing
leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
]
-- add any additional package configuration options here

require mathlib from git
"https://github.com/leanprover-community/mathlib4.git"@"f0d4a71"

@[default_target]
lean_lib «{project_name}» where
-- add any library configuration options here
"""
    
    with open(project_root / "lakefile.lean", "w") as f:
        f.write(lakefile_content)
        
    # Set the Lean toolchain version to match your system
    with open(project_root / "lean-toolchain", "w") as f:
        f.write("leanprover/lean4:v4.16.0-rc1\n")
        
    # Write the code to the root file
    with open(root_file, "w") as f:
        f.write(code)
        
    # Write a simple main file
    with open(main_file, "w") as f:
        f.write(f"import {project_name}\n\ndef main : IO Unit := return ()")

def build_lean_project(project_root: Path) -> None:
    """Build a Lean project. Necessary before running `pantograph`."""
    print("Running lake update...")
    update_result = subprocess.run(["lake", "update"], cwd=project_root, capture_output=True, text=True)
    if update_result.returncode != 0:
        print(f"Warning: lake update failed: {update_result.stderr}")
    print("Running lake build...")
    build_result = subprocess.run(["lake", "build"], cwd=project_root, capture_output=True, text=True)
    print(f"Build output: {build_result.stdout}")
    print(f"Build errors: {build_result.stderr}")

def atomize_lean(code: str, pkg_id: int) -> list[Schema]:
    """Atomize a Lean project and return a list of `Schema`s."""
    project_name = f"Pkg{pkg_id}"
    project_root = Path(f"/home/ec2-user/lean_projects/{project_name}")

    create_dummy_lean_project(code, pkg_id)
    build_lean_project(project_root)
    server = Server(imports=["Init", project_name], project_path=project_root)

    all_atoms = atomize_project(server)
    sorted_atoms = sort_atoms(all_atoms)

    schema = atoms_to_schema(sorted_atoms)

    return schema
