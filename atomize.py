#%%
from pathlib import Path
from typing import TypedDict, List, Optional, Set, Dict, Any, Sequence
from typing import Literal
from dataclasses import dataclass, field
from os import PathLike
import pantograph
import re
import logging
from pantograph.server import Server
import tempfile

type Name = str
# type Kind = Literal["def", "theorem", "lemma", "example", "structure", "class", "abbrev"]
# TODO: Add more kinds
type Kind = Literal["def", "theorem"]
EXCLUDED_NAMESPACES = ("Init", "Core", "Lean")
@dataclass
class AtomizedDef:
    """A single atomized definition with its dependencies and source code"""
    name: Name
    source: str
    type: str
    module_path: str
    type_dependencies: Set[Name] = field(default_factory=set)
    value_dependencies: Set[Name] = field(default_factory=set)
    kind: Optional[Kind] = None 
    def __hash__(self) -> int:
        return hash(self.name)
    def __eq__(self, other: Any) -> bool:
        return isinstance(other, AtomizedDef) and self.name == other.name

def is_builtin(name: Name, server: Server, exclude_namespaces: Sequence[str] = EXCLUDED_NAMESPACES) -> bool:
    """Check if a name is a builtin Lean name"""
    info = server.env_inspect(name=name,print_value=True,print_dependency=True)
    module_name:str = info["module"]
    module_parts = module_name.split(".")
    return module_parts[0] in exclude_namespaces

def extract_kind(name: Name, server: Server) -> Optional[Kind]:
    """Extract the kind of definition (def/theorem/etc) from source"""
    type_info: str = server.env_inspect(name=name,print_value=True,print_dependency=True)['type']
    type = server.expr_type(type_info)
    if type == "Prop":
        return "theorem"
    else: # TODO: Add more kinds
        return "def"

    
def atomize_file(server: Server, exclude_namespaces: Sequence[str] = EXCLUDED_NAMESPACES) -> list[AtomizedDef]:
    """
    Atomize a Lean file into its individual sub definitions using Pantograph's env.inspect
    and extract their dependencies recursively.

    Args:
        server: Pantograph server instance
        exclude_namespaces: Namespaces to exclude from dependencies

    Returns:
        List of AtomizedDef containing definition info and dependencies
    
    Raises:
        RuntimeError: If unable to communicate with server or parse file
    """

    # 1) First get the catalog of all definitions in the file
    raw_catalog: dict[str, Any] = server.run("env.catalog", {})
    try:
        catalog: list[Name] = raw_catalog['result']
    except Exception as e:
        raise RuntimeError(f"Failed to extract from {raw_catalog}") from e

        
    # 2) For each definition, get its detailed info and dependencies if its not builtin
    symbols: list[Name] = []
    
    # 3) For each symbol, get its type, value, and dependencies
    atomized_defs: list[AtomizedDef] = []
    for symbol in catalog:
        # Get detailed info including dependencies
        info = server.env_inspect(name=symbol, print_value=True, print_dependency=True)
        
        # Extract type and source code
        type_info = info.get('type', {}).get('pp', '')
        source = info.get('value', {}).get('pp', '')
        module_path = info.get('module', '')
        def is_builtin() -> bool:
            module_parts = module_path.split(".")
            return module_parts[0] in EXCLUDED_NAMESPACES
        # Skip builtins
        if is_builtin():
            continue
        # Extract dependencies
        type_deps = list(set(info.get('typeDependency', [])))
        value_deps = list(set(info.get('valueDependency', [])))
        
        # Determine if it's a theorem by checking if type is Prop
        kind: Optional[Kind] = extract_kind(symbol, server)
        
        atomized_def = AtomizedDef(
            name=symbol,
            source=source,
            type=type_info,
            module_path=module_path,
            type_dependencies=set(type_deps),
            value_dependencies=set(value_deps),
            kind=kind
        )
        atomized_defs.append(atomized_def)

    return atomized_defs


def find_def(atom: AtomizedDef|Name, all_atoms: list[AtomizedDef]) -> AtomizedDef:
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
    return f"theorem {def_atom.name} : {def_atom.type} := {def_atom.source}"

def deserialize_def(def_atom: AtomizedDef) -> str:
    """
    Of form
    ```
    def $(name) : $(type) := $(value)
    ```
    """
    return f"def {def_atom.name} : {def_atom.type} := {def_atom.source}"

def deserialize_decl(def_atom: AtomizedDef) -> str:
    if def_atom.kind == "theorem":
        return deserialize_theorem(def_atom)
    elif def_atom.kind == "def":
        return deserialize_def(def_atom)
    else:
        raise ValueError(f"Unknown kind: {def_atom.kind}")

def de_atomize(def_atom: AtomizedDef, all_atoms: list[AtomizedDef], server: Server, exclude_namespaces: Sequence[str] = EXCLUDED_NAMESPACES, out:str = '') -> str:
    # if a builtin, return `out` (base case of recursion)
    if is_builtin(def_atom.name, server, exclude_namespaces):
        return out
    
    # Recursively add all dependencies to `out`
    for dep in def_atom.type_dependencies | def_atom.value_dependencies:
        dep_def = find_def(dep, all_atoms)
        if dep_def.module_path: # not a builtin
            # Pass the current out string, don't use it in concatenation
            out = de_atomize(dep_def, all_atoms, server, exclude_namespaces, out)
    
    # Add current definition to output (must be after all dependencies are added)
    out += deserialize_decl(def_atom) + "\n"

    return out
    
def test_atomizer():
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
    server = Server(imports=["Atomization", "Init"], project_path=project_path)
    # Test atomization
    all_atoms = atomize_file(server)
    print(f"Atomized: {all_atoms}")
    
    # Test g definition
    g_def = find_def("g", all_atoms)
    print(g_def)

    assert g_def.source == "1"
    assert g_def.type == "Nat"
    assert g_def.kind == "def"

    # Test fg definition and its dependencies
    fg_def = find_def("fg", all_atoms)
    print(fg_def)   
    
    assert fg_def.source == "g + g"
    assert "g" in fg_def.value_dependencies
    assert fg_def.kind == "def"

    # Test theorem f''
    f2_def = find_def("f''", all_atoms)
    print(f2_def)
    
    assert f2_def.type == "2 = 2"
    assert f2_def.kind == "theorem"
    assert "f" in f2_def.type_dependencies
    assert "f" in f2_def.value_dependencies
    
    print("All tests passed!")

if __name__ == "__main__":
    test_atomizer()

    
