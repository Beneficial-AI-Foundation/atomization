# get_specs.py
from dataclasses import dataclass
from typing import List
import re
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file,
    SourceLocation,
    find_all_with_positions,
    strip_verification_annotations,
    get_location
)

@dataclass
class SpecContent:
    requires_clauses: List[SourceLocation]
    ensures_clauses: List[SourceLocation]
    ghost_predicates: List[SourceLocation]
    ghost_functions: List[SourceLocation]
    spec_functions: List[SourceLocation]

def get_specs(filename: str) -> SpecContent:
    content = read_dafny_file(filename)
    
    # Find requires clauses (now without the negative lookbehind)
    requires_pattern = r'requires\s+([^{\n]+)'
    requires_clauses = find_all_with_positions(requires_pattern, content, filename)
    
    # Find ensures clauses
    ensures_pattern = r'ensures\s+([^{\n]+)'
    ensures_clauses = find_all_with_positions(ensures_pattern, content, filename)
    
    # Find ghost predicates with annotations stripped
    ghost_predicate_pattern = r'ghost\s+predicate\s+(\w+[^{]*{[^}]*})'
    ghost_predicates = []
    for match in re.finditer(ghost_predicate_pattern, content):
        loc = get_location(content, match.start(), match.end(), filename)
        # Strip verification annotations from the content
        stripped_content = strip_verification_annotations(loc.content)
        loc.content = stripped_content
        ghost_predicates.append(loc)
    
    # Find ghost functions with annotations stripped
    ghost_function_pattern = r'ghost\s+function\s+(\w+[^{]*{[^}]*})'
    ghost_functions = []
    for match in re.finditer(ghost_function_pattern, content):
        loc = get_location(content, match.start(), match.end(), filename)
        # Strip verification annotations from the content
        stripped_content = strip_verification_annotations(loc.content)
        loc.content = stripped_content
        ghost_functions.append(loc)
    
    # Find regular functions and check if they're spec-only
    function_pattern = r'(?<!ghost\s)function\s+(?!method\b)(\w+[^{]*{[^}]*})'
    functions = find_all_with_positions(function_pattern, content, filename)
    
    spec_functions = [
        func for func in functions 
        if is_spec_only_function(func.content)
    ]
    
    return SpecContent(
        requires_clauses=requires_clauses,
        ensures_clauses=ensures_clauses,
        ghost_predicates=ghost_predicates,
        ghost_functions=ghost_functions,
        spec_functions=spec_functions
    )