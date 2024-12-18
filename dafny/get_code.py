# get_code.py

import sys
from dataclasses import dataclass
from typing import List
import re
from dafny_utils import (
    is_spec_only_function, 
    read_dafny_file, 
    strip_verification_annotations
)

@dataclass
class CodeContent:
    methods: List[str]
    executable_functions: List[str]

def parse_dafny_file(filename: str) -> CodeContent:
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

def main():
    if len(sys.argv) != 2:
        print("Usage: python get_code.py <dafny_file>")
        sys.exit(1)
        
    filename = sys.argv[1]
    
    try:
        code_content = parse_dafny_file(filename)
        
        print("=== Executable Code Analysis ===")
        print("\nMethods (without verification annotations):")
        for method in code_content.methods:
            print(f"  {method}\n")
            
        print("\nExecutable Functions:")
        for func in code_content.executable_functions:
            print(f"  {func}\n")
            
    except FileNotFoundError:
        print(f"Error: Could not find file {filename}")
        sys.exit(1)
    except Exception as e:
        print(f"Error parsing file: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()