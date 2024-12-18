# get_specs.py
from dataclasses import dataclass
from typing import List
import re
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file
)

@dataclass
class SpecContent:
    requires_clauses: List[str]
    ensures_clauses: List[str]
    ghost_predicates: List[str]
    ghost_functions: List[str]
    spec_functions: List[str]

def get_specs(filename: str) -> SpecContent:
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