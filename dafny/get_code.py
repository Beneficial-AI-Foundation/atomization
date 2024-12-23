# get_code.py
from dataclasses import dataclass
import re
from typing import List
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file, 
    strip_verification_annotations,
    SourceLocation,
    find_all_with_positions
)

@dataclass
class CodeContent:
    methods: List[SourceLocation]          # Changed from List[str]
    executable_functions: List[SourceLocation]  # Changed from List[str]

def get_code(filename: str) -> CodeContent:
    content = read_dafny_file(filename)
    
    # Find methods with their bodies (excluding lemmas)
    method_pattern = r'(?<!lemma\s)method\s+\w+[^{]*{(?:[^{}]|{[^{}]*})*}'
    methods = find_all_with_positions(method_pattern, content, filename)
    
    # Find non-ghost functions
    function_pattern = r'(?<!ghost\s)function\s+(?!method\b)(\w+[^{]*{[^}]*})'
    functions = find_all_with_positions(function_pattern, content, filename)
    
    # Filter out functions that use spec-only features
    executable_functions = []
    for func in functions:
        if not is_spec_only_function(func.content):
            # Create new SourceLocation with stripped content
            stripped_content = strip_verification_annotations(func.content)
            executable_functions.append(SourceLocation(
                filename=filename,
                start_line=func.start_line,
                start_col=func.start_col,
                end_line=func.end_line,
                end_col=func.end_col,
                content=stripped_content
            ))
    
    # Strip verification annotations from methods but keep location info
    stripped_methods = []
    for method in methods:
        stripped_content = strip_verification_annotations(method.content)
        stripped_methods.append(SourceLocation(
            filename=filename,
            start_line=method.start_line,
            start_col=method.start_col,
            end_line=method.end_line,
            end_col=method.end_col,
            content=stripped_content
        ))
    
    return CodeContent(
        methods=stripped_methods,
        executable_functions=executable_functions
    )