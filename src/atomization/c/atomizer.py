from pathlib import Path
import tree_sitter_c as tsc
from tree_sitter import Language, Parser
from typing import List, Dict, Any, Optional
from abc import ABC, abstractmethod
import json

C_LANGUAGE = Language(tsc.language())
parser = Parser(C_LANGUAGE)

class AtomBase(ABC):
    def __init__(
        self,
        atom_type: str,
        identifier: str,
        lineno: int,
        signature: str,
        body: str,
        deps: List[str],
        context: Optional[List[str]] = None,
    ):
        self.atom_type = atom_type
        self.identifier = identifier
        self.lineno = lineno
        self.signature = signature
        self.body = body
        self.deps = deps
        self.context = context or []

    @abstractmethod
    def jsonify(self) -> Dict[str, Any]:
        pass

class FunctionAtom(AtomBase):
    def jsonify(self) -> Dict[str, Any]:
        return {
            "type": self.atom_type,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "body": self.body,
            "deps": self.deps,
            "context": self.context,
        }

class BottomAtom(AtomBase):
    def __init__(self):
        super().__init__(
            atom_type="bottom",
            identifier="",
            lineno=0,
            signature="",
            body="",
            deps=[],
            context=[],
        )

    def jsonify(self) -> Dict[str, Any]:
        return {
            "type": self.atom_type,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "body": self.body,
            "deps": self.deps,
            "context": self.context,
        }

class Atomizer(ABC):
    def __init__(self, filename: str | Path):
        self.filename = Path(filename)

    @abstractmethod
    def atomize(self) -> List[AtomBase]:
        pass

    def jsonify(self) -> str:
        atoms = self.atomize()
        return json.dumps([atom.jsonify() for atom in atoms], indent=2)

def atomize(node, context: Optional[List[str]] = None) -> AtomBase:
    """Convert a tree-sitter node into an atom."""
    if node.type != "function_definition":
        return BottomAtom()

    # Get the function name
    identifier = (
        node.child_by_field_name("declarator")
        .child_by_field_name("declarator")
        .text.decode("utf-8")
    )

    # Get the full signature including return type and parameters
    signature = node.text.decode("utf-8").split("{")[0].strip()
    body = node.text.decode("utf-8")

    # Extract dependencies
    deps = []
    def traverse(n):
        if n.type == "call_expression":
            func_name = n.child_by_field_name("function").text.decode("utf-8")
            if func_name not in deps:
                deps.append(func_name)
        for child in n.children:
            traverse(child)

    body_node = node.child_by_field_name("body")
    if body_node:
        traverse(body_node)

    return FunctionAtom(
        atom_type="function",
        identifier=identifier,
        lineno=node.start_point[0] + 1,
        signature=signature,
        body=body,
        deps=deps,
        context=context or [],
    )

class CAtomizer(Atomizer):
    def atomize(self) -> List[AtomBase]:
        with open(self.filename, "r", encoding="utf-8") as c_file:
            text = c_file.read()
        tree = parser.parse(text.encode("utf-8"))
        return [atomize(node) for node in tree.root_node.children]

def atomize_str(content: str) -> str:
    """Atomize a string containing C code."""
    tree = parser.parse(content.encode("utf-8"))
    atoms = [atomize(node) for node in tree.root_node.children]
    return json.dumps([atom.jsonify() for atom in atoms], indent=2)

if __name__ == "__main__":
    # Example usage
    atomizer = CAtomizer(Path.cwd() / "examples" / "refinedc" / "src" / "example.c")
    print(atomizer.jsonify())
