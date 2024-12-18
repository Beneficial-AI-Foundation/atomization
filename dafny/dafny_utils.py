# dafny_utils.py

import re
from typing import List, Set, Tuple

def is_spec_only_function(function_body: str) -> bool:
    """Check if a function contains spec-only features."""
    spec_features = [
        r'\bold\b',          # old keyword
        r'\bunchanged\b',    # unchanged keyword
        r'\bforall\b',       # quantifiers
        r'\bexists\b',       # quantifiers
        r'\bFresh\b',        # Fresh keyword
        r'\ballocated\b',    # allocated keyword
        r'\breveal_\w+\b',   # reveal statements
    ]
    
    return any(re.search(pattern, function_body, re.MULTILINE | re.DOTALL) is not None 
              for pattern in spec_features)

def remove_comments(content: str) -> str:
    """Remove single-line and multi-line comments from Dafny code."""
    # Remove single-line comments
    content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
    # Remove multi-line comments
    content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
    return content

def read_dafny_file(filename: str) -> str:
    """Read and preprocess a Dafny file."""
    with open(filename, 'r') as f:
        content = f.read()
    return remove_comments(content)

def extract_verification_annotations(code: str) -> Tuple[List[str], List[str], List[str]]:
    """Extract verification annotations (invariants, decreases, assertions) from code.
    Returns tuple of (invariants, decreases, assertions)."""
    
    # Find invariant clauses
    invariant_pattern = r'invariant\s+([^{\n]+)'
    invariants = re.findall(invariant_pattern, code)
    
    # Find decreases clauses
    decreases_pattern = r'decreases\s+([^{\n]+)'
    decreases = re.findall(decreases_pattern, code)
    
    # Find assertions
    assert_pattern = r'assert\s+([^;]+);'
    assertions = re.findall(assert_pattern, code)
    
    return (
        [inv.strip() for inv in invariants],
        [dec.strip() for dec in decreases],
        [asrt.strip() for asrt in assertions]
    )

def strip_verification_annotations(code: str) -> str:
    """Remove verification annotations from code while preserving the core logic."""
    # Remove invariant clauses
    code = re.sub(r'\s*invariant[^{\n]+\n', '\n', code)
    
    # Remove decreases clauses
    code = re.sub(r'\s*decreases[^{\n]+\n', '\n', code)
    
    # Remove assert statements
    code = re.sub(r'\s*assert[^;]+;', '', code)
    
    # Clean up any multiple blank lines that might have been created
    code = re.sub(r'\n\s*\n', '\n\n', code)
    
    return code

def get_loop_invariants(method_body: str) -> List[str]:
    """Extract loop invariants from a method body."""
    # Find while loops and their invariants
    loop_pattern = r'while[^{]*{[^}]*}'
    loops = re.findall(loop_pattern, method_body, re.DOTALL)
    
    all_invariants = []
    for loop in loops:
        invariants, _, _ = extract_verification_annotations(loop)
        all_invariants.extend(invariants)
    
    return all_invariants