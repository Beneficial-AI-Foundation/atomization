# get_code.py
from dataclasses import dataclass
import re
from typing import List
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file, 
    strip_verification_annotations
)

@dataclass
class CodeContent:
    methods: List[str]
    executable_functions: List[str]

def get_code(filename: str) -> CodeContent:
    content = read_dafny_file(filename)
    
    # Find methods with their bodies (excluding lemmas)
    method_pattern = r'(?<!lemma\s)method\s+(\w+[^{]*{[^}]*})'
    methods = re.findall(method_pattern, content, re.DOTALL)
    
    # Strip verification annotations from each method
    methods = [strip_verification_annotations(method) for method in methods]
    
    # Find non-ghost functions
    function_pattern = r'(?<!ghost\s)function\s+(?!method\b)(\w+[^{]*{[^}]*})'
    functions = re.findall(function_pattern, content, re.DOTALL)
    
    # Filter out functions that use spec-only features
    executable_functions = [
        strip_verification_annotations(func.strip()) 
        for func in functions 
        if not is_spec_only_function(func)
    ]
    
    return CodeContent(
        methods=[method.strip() for method in methods],
        executable_functions=executable_functions
    )