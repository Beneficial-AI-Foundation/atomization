# dafny_utils.py

import re
from typing import List, Tuple

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

def find_matching_brace(content: str, start_pos: int) -> int:
    """Find the position of the matching closing brace, handling nested braces."""
    count = 1
    pos = start_pos
    while count > 0 and pos < len(content):
        if content[pos] == '{':
            count += 1
        elif content[pos] == '}':
            count -= 1
        pos += 1
    return pos if count == 0 else -1

def extract_lemmas(content: str) -> List[str]:
    """Extract complete lemma declarations including their entire bodies."""
    lemmas = []
    # Find lemma start positions
    for match in re.finditer(r'lemma\s+\w+', content):
        start = match.start()
        # Find the opening brace
        brace_match = re.search(r'{', content[start:])
        if brace_match:
            brace_pos = start + brace_match.start()
            # Find the matching closing brace
            end_pos = find_matching_brace(content, brace_pos + 1)
            if end_pos != -1:
                # Extract the complete lemma including its body
                lemma = content[start:end_pos].strip()
                lemmas.append(lemma)
    return lemmas

def strip_verification_annotations(code: str) -> str:
    """Remove verification annotations from code while preserving the core logic."""
    # Remove requires clauses
    code = re.sub(r'\s*requires[^{\n]+\n', '\n', code)
    
    # Remove ensures clauses
    code = re.sub(r'\s*ensures[^{\n]+\n', '\n', code)
    
    # Remove invariant clauses
    code = re.sub(r'\s*invariant[^{\n]+\n', '\n', code)
    
    # Remove decreases clauses
    code = re.sub(r'\s*decreases[^{\n]+\n', '\n', code)
    
    # Remove assert statements
    code = re.sub(r'\s*assert[^;]+;', '', code)
    
    # Clean up any multiple blank lines that might have been created
    code = re.sub(r'\n\s*\n', '\n\n', code)
    
    return code.strip()

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