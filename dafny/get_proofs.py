# get_proofs.py
import re
from dataclasses import dataclass
from typing import List
from dafny_utils import (
    read_dafny_file,
    extract_verification_annotations,
    find_all_with_positions,
    SourceLocation,
    get_location,
    get_loop_invariants,
    strip_verification_annotations
)

@dataclass
class ProofContent:
    lemmas: List[SourceLocation]
    invariants: List[SourceLocation]
    decreases_clauses: List[SourceLocation]
    assertions: List[SourceLocation]

def get_proofs(filename: str) -> ProofContent:
    content = read_dafny_file(filename)
    
    # Find lemmas with annotations stripped
    lemma_pattern = r'lemma\s+\w+[^{]*{(?:[^{}]|{[^{}]*})*}'
    lemmas = []
    for match in re.finditer(lemma_pattern, content):
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Strip verification annotations from the content
        stripped_content = strip_verification_annotations(loc.content)
        loc.content = stripped_content
        lemmas.append(loc)
    
    # Find invariants (for methods and loops)
    invariant_pattern = r'invariant\s+([^{\n]+)'
    invariants = find_all_with_positions(invariant_pattern, content, filename)
    
    # Find assertions
    assert_pattern = r'assert\s+([^;]+);'
    assertions = find_all_with_positions(assert_pattern, content, filename)
    
    # Find decreases clauses with context
    decreases_pattern = r'decreases\s+([^{\n]+)'
    decreases_clauses = []
    
    for match in re.finditer(decreases_pattern, content):
        # Get the full location
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Determine the context of the decreases clause
        pre_content = content[:match.start()]
        lines = pre_content.split('\n')
        
        # Look back to determine context
        context = None
        for line in reversed(lines):
            if re.search(r'method\s+\w+', line):
                context = 'method'
                break
            elif re.search(r'ghost\s+function\s+\w+', line):
                context = 'ghost_function'
                break
            elif re.search(r'while', line):
                context = 'while_loop'
                break
        
        # Modify the location to include context
        if hasattr(loc, 'context'):
            loc.context = context
        else:
            # Fallback for older SourceLocation implementations
            loc = SourceLocation(
                filename=loc.filename,
                start_line=loc.start_line,
                start_col=loc.start_col,
                end_line=loc.end_line,
                end_col=loc.end_col,
                content=loc.content,
                parent=loc.parent,
                context=context
            )
        
        decreases_clauses.append(loc)
    
    return ProofContent(
        lemmas=lemmas,
        invariants=invariants,
        decreases_clauses=decreases_clauses,
        assertions=assertions
    )