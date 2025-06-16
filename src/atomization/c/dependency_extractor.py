from pathlib import Path
import json
from typing import List, Dict, Any, Optional
from atomization.c.treesitter_client import parse_file, parse_text

class CAtom:
    def __init__(
        self,
        atom_type: str,
        identifier: str,
        lineno: int,
        signature: str,
        body: str,
        deps: List[str],
        context: Optional[List[str]] = None
    ):
        self.atom_type = atom_type
        self.identifier = identifier
        self.lineno = lineno
        self.signature = signature
        self.body = body
        self.deps = deps
        self.context = context or []

    def jsonify(self) -> Dict[str, Any]:
        return {
            "type": self.atom_type,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "body": self.body,
            "deps": self.deps,
            "context": self.context
        }

class CDependencyExtractor:
    def __init__(self, filename: str | Path):
        self.filename = Path(filename)
        self.atoms: List[CAtom] = []

    def extract_function_signature(self, node) -> tuple[str, str]:
        """Extract function name and signature from a function definition node."""
        # Get the function name
        identifier = node.child_by_field_name("declarator").child_by_field_name("declarator").text.decode("utf-8")
        
        # Get the full signature including return type and parameters
        signature = node.text.decode("utf-8").split("{")[0].strip()
        
        return identifier, signature

    def extract_dependencies(self, node) -> List[str]:
        """Extract function calls and other dependencies from a function body."""
        deps = []
        
        def traverse(n):
            if n.type == "call_expression":
                # Get the function name being called
                func_name = n.child_by_field_name("function").text.decode("utf-8")
                if func_name not in deps:
                    deps.append(func_name)
            
            for child in n.children:
                traverse(child)
        
        # Start traversal from the function body
        body_node = node.child_by_field_name("body")
        if body_node:
            traverse(body_node)
        
        return deps

    def extract_atoms(self) -> List[CAtom]:
        """Extract all function definitions and their dependencies."""
        nodes = parse_file(self.filename)
        
        for node in nodes:
            if node.type == "function_definition":
                identifier, signature = self.extract_function_signature(node)
                body = node.text.decode("utf-8")
                deps = self.extract_dependencies(node)
                
                atom = CAtom(
                    atom_type="function",
                    identifier=identifier,
                    lineno=node.start_point[0] + 1,  # Convert to 1-based line numbers
                    signature=signature,
                    body=body,
                    deps=deps
                )
                self.atoms.append(atom)
        
        return self.atoms

    def jsonify(self) -> str:
        """Convert the extracted atoms to JSON format."""
        atoms = self.extract_atoms()
        return json.dumps([atom.jsonify() for atom in atoms], indent=2)

def extract_dependencies_from_text(content: str) -> str:
    """Extract dependencies from a string containing C code."""
    nodes = parse_text(content)
    extractor = CDependencyExtractor("_temp.c")
    extractor.atoms = []
    
    for node in nodes:
        if node.type == "function_definition":
            identifier, signature = extractor.extract_function_signature(node)
            body = node.text.decode("utf-8")
            deps = extractor.extract_dependencies(node)
            
            atom = CAtom(
                atom_type="function",
                identifier=identifier,
                lineno=node.start_point[0] + 1,
                signature=signature,
                body=body,
                deps=deps
            )
            extractor.atoms.append(atom)
    
    return json.dumps([atom.jsonify() for atom in extractor.atoms], indent=2)

if __name__ == "__main__":
    # Example usage
    extractor = CDependencyExtractor(Path.cwd() / "examples" / "refinedc" / "src" / "example.c")
    print(extractor.jsonify()) 