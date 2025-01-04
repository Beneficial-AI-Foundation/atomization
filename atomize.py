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
# 
EXCLUDED_NAMESPACES = ("Init", "Core", "Lean", "Mathlib")
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
    ref_spec: Optional[str] = None

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

def extract_kind(name: Name, server: Server, inspect_cache: Optional[Dict[str, dict]] = None) -> Optional[Kind]:
    """Extract the kind of definition (def/theorem/etc) from source"""
    if inspect_cache and name in inspect_cache:
        type_info = inspect_cache[name]['type']['pp']
    else:
        type_info = server.env_inspect(name=name,print_value=True,print_dependency=True)['type']['pp']
    
    type = server.expr_type(type_info)
    if type == "Prop":
        return "theorem"
    else: # TODO: Add more kinds
        return "def"

    
def atomize_file(server: Server, exclude_namespaces: Sequence[str] = EXCLUDED_NAMESPACES) -> list[AtomizedDef]:
    """
    Atomize a Lean file into its individual sub definitions using Pantograph's env.inspect
    and extract their dependencies recursively.
    """
    # Get project root from server
    project_root = Path(server.project_path)

    # First pass: Get all definitions and their basic info
    catalog = server.run("env.catalog", {})['symbols']
    print(f"Catalog length: {len(catalog)}")
    
    # Filter and unmangle symbols first
    filtered_symbols = []
    inspect_cache: Dict[str, dict] = {}  # Cache env.inspect results
    
    for symbol in catalog:
        symbol = symbol[1:]  # TODO: improve unmangling
        try:
            # Cache inspect results as we filter
            info = server.env_inspect(name=symbol, print_value=True, print_dependency=True)
            inspect_cache[symbol] = info
            
            symbol_parts = symbol.split(".")
            if symbol_parts[0] not in EXCLUDED_NAMESPACES:
                filtered_symbols.append(symbol)
        except pantograph.ServerError as e:
            print(f"Warning: Failed to inspect {symbol}: {e}")
            continue
    
    # Second pass: Get source files for all modules
    source_cache: Dict[str, tuple[str, str]] = {}  # module path -> (file name, contents)
    module_paths = set()
    
    # Collect module paths from cached inspect results
    for symbol in filtered_symbols:
        info = inspect_cache[symbol]
        module_path = info.get('module', '')
        if module_path and module_path.split(".")[0] not in exclude_namespaces:
            module_paths.add(module_path)
    
    # Load all source files
    for module_path in module_paths:
        source_file = find_source_file(module_path, project_root)
        if source_file:
            source_cache[module_path] = (source_file.name, source_file.read_text())
        else:
            source_cache[module_path] = ("", "")
            print(f"Warning: Could not find source file for module {module_path}")
    
    # Final pass: Create AtomizedDefs using cached inspect results
    atomized_defs: list[AtomizedDef] = []
    for symbol in filtered_symbols:
        info = inspect_cache[symbol]
        module_path = info.get('module', '')
        if not module_path or module_path not in source_cache:
            continue
            
        # Extract definition info
        type_info = info.get('type', {}).get('pp', '')
        source = info.get('value', {}).get('pp', '')
        type_deps = list(set(info.get('typeDependency', [])))
        value_deps = list(set(info.get('valueDependency', [])))
        kind = extract_kind(symbol, server)  # Still need this call since it uses expr_type
        
        atom = AtomizedDef(
            name=symbol,
            source=source,
            type=type_info,
            module_path=module_path,
            type_dependencies=set(type_deps),
            value_dependencies=set(value_deps),
            kind=kind
        )
        
        # Add ref spec if it exists in the source
        add_ref_spec(atom, source_cache, atomized_defs)
        atomized_defs.append(atom)

    return atomized_defs

def add_ref_spec(atom: AtomizedDef, source_cache: Dict[str, tuple[str, str]], all_atoms: list[AtomizedDef]) -> AtomizedDef:
    """Mutably add a reference specification to an atomized definition."""
    csimp_pattern = r'@\[csimp\]\s*theorem\s+(\w+)\s*:\s*@?(\w+)\s*=\s*@?(\w+)\s*:='
    
    # Find all @[csimp] theorems in the source
    _, source_code = source_cache[atom.module_path]
    for match in re.finditer(csimp_pattern, source_code):
        theorem_name = match.group(1)
        first_name = match.group(2)
        second_name = match.group(3)
        
        # If either side matches our atom's name
        if first_name == atom.name or second_name == atom.name:
            atom.ref_spec = theorem_name
            # Also add ref spec to the other definition if it exists
            other_name = second_name if first_name == atom.name else first_name
            other_atom = next((a for a in all_atoms if a.name == other_name), None)
            if other_atom:
                other_atom.ref_spec = theorem_name
            break  # Take first matching ref spec
            
    return atom

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
    
    # Test ref spec for fib and fibImperative
    fib_def = find_def("fib", all_atoms)
    fib_imp_def = find_def("fibImperative", all_atoms)
    print(f"fib def: {fib_def}")
    print(f"fibImperative def: {fib_imp_def}")
    
    # Both should have fib_spec as their ref spec
    assert fib_def.ref_spec == "fib_spec", f"Expected fib ref_spec to be 'fib_spec', got {fib_def.ref_spec}"
    assert fib_imp_def.ref_spec == "fib_spec", f"Expected fibImperative ref_spec to be 'fib_spec', got {fib_imp_def.ref_spec}"
    
    # Test that non-ref spec functions don't have a ref spec
    g_def = find_def("g", all_atoms)
    assert g_def.ref_spec is None, f"Expected g ref_spec to be None, got {g_def.ref_spec}"
    
    print("All tests passed!")

def find_source_file(module_path: str, project_root: Path) -> Optional[Path]:
    """Find the source file for a given module path in the project.
    
    Args:
        module_path: Module path like "Atomization.Basic"
        project_root: Root directory of the project
        
    Returns:
        Path to the source file or None if not found
    """
    # Convert module path to file path (e.g. "Atomization.Basic" -> "Atomization/Basic.lean")
    relative_path = Path(module_path.replace(".", "/") + ".lean")
    source_path = project_root / relative_path
    
    if source_path.exists():
        return source_path
    return None

if __name__ == "__main__":
    test_atomizer()

    

# %%
