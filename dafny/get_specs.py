# get_specs.py

import sys
from dataclasses import dataclass
from typing import List
import re
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file,
    extract_verification_annotations
)

@dataclass
class SpecContent:
    requires_clauses: List[str]
    ensures_clauses: List[str]
    ghost_predicates: List[str]
    ghost_functions: List[str]
    spec_functions: List[str]

def parse_dafny_file(filename: str) -> SpecContent:
    content = read_dafny_file(filename)
    
    # Find requires clauses (excluding those in invariants)
    requires_pattern = r'(?<!invariant\s)requires\s+([^{\n]+)'
    requires_clauses = re.findall(requires_pattern, content)
    
    # Find ensures clauses
    ensures_pattern = r'ensures\s+([^{\n]+)'
    ensures_clauses = re.findall(ensures_pattern, content)
    
    # Find ghost predicates
    ghost_predicate_pattern = r'ghost\s+predicate\s+(\w+[^{]*{[^}]*})'
    ghost_predicates = re.findall(ghost_predicate_pattern, content, re.DOTALL)
    
    # Find ghost functions
    ghost_function_pattern = r'ghost\s+function\s+(\w+[^{]*{[^}]*})'
    ghost_functions = re.findall(ghost_function_pattern, content, re.DOTALL)
    
    # Find regular functions and check if they're spec-only
    function_pattern = r'(?<!ghost\s)function\s+(?!method\b)(\w+[^{]*{[^}]*})'
    functions = re.findall(function_pattern, content, re.DOTALL)
    spec_functions = [func.strip() for func in functions if is_spec_only_function(func)]
    
    return SpecContent(
        requires_clauses=[clause.strip() for clause in requires_clauses],
        ensures_clauses=[clause.strip() for clause in ensures_clauses],
        ghost_predicates=[pred.strip() for pred in ghost_predicates],
        ghost_functions=[func.strip() for func in ghost_functions],
        spec_functions=spec_functions
    )

def main():
    if len(sys.argv) != 2:
        print("Usage: python get_specs.py <dafny_file>")
        sys.exit(1)
        
    filename = sys.argv[1]
    
    try:
        spec_content = parse_dafny_file(filename)
        
        print("=== Specification Content Analysis ===")
        print("\nRequires Clauses:")
        for clause in spec_content.requires_clauses:
            print(f"  - {clause}")
            
        print("\nEnsures Clauses:")
        for clause in spec_content.ensures_clauses:
            print(f"  - {clause}")
            
        print("\nGhost Predicates:")
        for pred in spec_content.ghost_predicates:
            print(f"  {pred}\n")
            
        print("\nGhost Functions:")
        for func in spec_content.ghost_functions:
            print(f"  {func}\n")
            
        print("\nNon-ghost Spec Functions (should be empty in modern Dafny):")
        for func in spec_content.spec_functions:
            print(f"  {func}\n")
            
    except FileNotFoundError:
        print(f"Error: Could not find file {filename}")
        sys.exit(1)
    except Exception as e:
        print(f"Error parsing file: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()