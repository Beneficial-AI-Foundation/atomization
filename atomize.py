#%%
from pathlib import Path
from typing import TypedDict, List, Optional, Set, Dict, Any, Sequence
from typing import Literal
from dataclasses import dataclass, field
from os import PathLike
from pantograph.server import Server
import pantograph
import re
import logging

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
    module_path: Path
    dependencies: Set[Name] = field(default_factory=set)
    kind: Optional[Kind] = None 


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
        file_path: Path to the Lean file
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



    # 3) For each definition, get its detailed info and dependencies if its not builtin
    symbols :list[Name] = [name for name in catalog if not is_builtin(name, server, exclude_namespaces)]
    
    

