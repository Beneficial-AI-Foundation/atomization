# dafny_utils.py

import re
from dataclasses import dataclass
from typing import List, Tuple

@dataclass
class SourceLocation:
    filename: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    content: str
    parent: str = None
    context: str = None
    context_content: str = None

def is_spec_only_function(function_body: str) -> bool:
    """Check if a function contains specification-only features."""
    spec_features = [
        r'\bforall\b(?!.*==>.*requires)',  # forall but not in requires clause
        r'\bexists\b',       # exists quantifier
        r'\bold\b',          # old keyword
        r'\bunchanged\b',    # unchanged keyword
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
    
    # Remove reads clauses
    code = re.sub(r'\s*reads[^{\n]+\n', '\n', code)  # Add this line
    
    # Remove invariant clauses
    code = re.sub(r'\s*invariant[^{\n]+\n', '\n', code)
    
    # Remove decreases clauses
    code = re.sub(r'\s*decreases[^{\n]+\n', '\n', code)
    
    # Remove assert statements
    code = re.sub(r'\s*assert[^;]+;', '', code)
    
    # Clean up any multiple blank lines
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

def get_parent_name(content: str, start_pos: int, parent_pattern: str) -> str | None:
    """Get the most immediate parent name of a code segment."""
    # Pattern to match any kind of parent declaration
    parent_pattern = r'(ghost\s+)?(function|method|predicate|lemma)\s+\w+'
    
    # Get content up to our position and reverse it for searching backwards
    prefix = content[:start_pos]
    prefix_lines = prefix.split('\n')
    
    # Search through lines in reverse until we find a parent declaration
    for line in reversed(prefix_lines):
        match = re.search(parent_pattern, line)
        if match:
            words = match.group().split()
            return words[-1]
    
    return None

def get_location(content: str, match_start: int, match_end: int, filename: str) -> SourceLocation:
    """
    Convert a string index position into line and column numbers.
    
    Args:
        content: The full file content
        match_start: Starting index of the match
        match_end: Ending index of the match
        filename: Name of the source file
        
    Returns:
        SourceLocation object containing filename, start/end positions, and the content
    """
    # Get content up to start position to count lines and cols
    pre_content = content[:match_start]
    start_line = pre_content.count('\n') + 1
    if start_line == 1:
        start_col = match_start + 1
    else:
        start_col = match_start - pre_content.rindex('\n')

    # Get content up to end position
    pre_end_content = content[:match_end]
    end_line = pre_end_content.count('\n') + 1
    if end_line == 1:
        end_col = match_end + 1
    else:
        end_col = match_end - pre_end_content.rindex('\n')

    # Extract the actual content
    matched_content = content[match_start:match_end]

    parent_pattern = r'(ghost\s+)?(function|method|predicate|lemma)\s+\w+'
    parent = None
    # Get parent method or function name
    if re.search(parent_pattern, matched_content) == None:
        parent = get_parent_name(content, match_start, parent_pattern)
    # parent = get_parent_name(content, match_start, parent_pattern)

    return SourceLocation(
        filename=filename,
        start_line=start_line,
        start_col=start_col,
        end_line=end_line,
        end_col=end_col,
        content=matched_content.strip(),
        parent=parent
    )

def find_all_with_positions(pattern: str, content: str, filename: str) -> List[SourceLocation]:
    """
    Find all matches of a pattern and return their source locations.
    
    Args:
        pattern: Regex pattern to match
        content: Source content to search
        filename: Name of the source file
        
    Returns:
        List of SourceLocation objects for each match
    """
    locations = []
    for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
        locations.append(get_location(content, match.start(), match.end(), filename))
    return locations