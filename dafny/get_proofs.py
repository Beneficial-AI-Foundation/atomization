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
    
    # Find lemmas
    lemma_pattern = r'lemma\s+\w+[^{]*{(?:[^{}]|{[^{}]*})*}'
    lemmas = []
    for match in re.finditer(lemma_pattern, content, re.DOTALL):
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Strip verification annotations from the content
        stripped_content = strip_verification_annotations(loc.content)
        loc.content = stripped_content
        lemmas.append(loc)
    
    # Find invariants (for methods and loops)
    invariant_pattern = r'invariant\s+([^{\n]+)'
    # invariants = find_all_with_positions(invariant_pattern, content, filename)
    invariants = []

    for match in re.finditer(invariant_pattern, content):
        # Get the full location
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Determine the context of the invariant
        pre_content = content[:match.start()]
        
        # Find the current method
        method_pattern = r'method\s+(\w+)[^{]*{(?:[^{}]|{[^{}]*})*}'
        current_method = None
        for method_match in re.finditer(method_pattern, content, re.DOTALL):
            if match.start() > method_match.start() and match.start() < method_match.end():
                current_method = method_match.group(1)
                break
        
        # Find the specific while loop containing this invariant
        while_condition_pattern = r'while\s+([^{\n]+)'
        context_content = None
        
        for while_match in re.finditer(while_condition_pattern, content):
            if match.start() > while_match.start():
                context_content = f"while {while_match.group(1).strip()}"
                break
        
        # Modify the location to include context
        if hasattr(loc, 'context'):
            loc.context = 'while_loop' if context_content else None
            loc.context_content = context_content
            if current_method:
                loc.parent = current_method
        else:
            # Fallback for older SourceLocation implementations
            loc = SourceLocation(
                filename=loc.filename,
                start_line=loc.start_line,
                start_col=loc.start_col,
                end_line=loc.end_line,
                end_col=loc.end_col,
                content=loc.content,
                parent=current_method,
                context='while_loop' if context_content else None,
                context_content=context_content
            )
        
        invariants.append(loc)
    # Find assertions
    assert_pattern = r'assert\s+([^;]+);'
    assertions = find_all_with_positions(assert_pattern, content, filename)
    
    # Find decreases clauses with context
    decreases_pattern = r'decreases\s+([^{\n]+)'
    decreases_clauses = []
    
    # Find all while loops in the content
    while_condition_pattern = r'while\s+([^{\n]+)'
    
    for match in re.finditer(decreases_pattern, content):
        # Get the full location
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Determine the context of the decreases clause
        pre_content = content[:match.start()]
        lines = pre_content.split('\n')
        
        # Look back to determine context
        context = None
        context_content = None
        current_method = None
        
        # Find the current method
        method_pattern = r'method\s+(\w+)[^{]*{(?:[^{}]|{[^{}]*})*}'
        for method_match in re.finditer(method_pattern, content, re.DOTALL):
            if match.start() > method_match.start() and match.start() < method_match.end():
                current_method = method_match.group(1)
                break
        
        # Find the specific while loop containing this decreases clause
        for while_match in re.finditer(while_condition_pattern, content, re.DOTALL):
            print(f"While match start: {while_match.start()}")
            print(f"While match end: {while_match.end()}")
            print(f"While condition: '{while_match.group(1)}'")
            
            # Print detailed comparison information
            print(f"Comparison details:")
            print(f"match.start() = {match.start()}")
            print(f"while_match.start() = {while_match.start()}")
            print(f"while_match.end() = {while_match.end()}")
            print(f"Condition 1 (match.start() > while_match.start()): {match.start() > while_match.start()}")
            print(f"Condition 2 (match.start() < while_match.end()): {match.start() < while_match.end()}")
        
            if match.start() > while_match.start(): # and match.start() < while_match.end():
                context = 'while_loop'
                context_content = f"while {while_match.group(1).strip()}"
                print(f"Captured condition: '{context_content}'")
                break
        # If no while loop found, check for method or ghost function
        if context is None:
            for line in reversed(lines):
                if re.search(r'method\s+\w+', line):
                    context = 'method'
                    break
                elif re.search(r'ghost\s+function\s+\w+', line):
                    context = 'ghost_function'
                    break
        
        # Modify the location to include context
        if hasattr(loc, 'context'):
            loc.context = context
            if context_content:
                # Store the entire while loop content
                print(f"Setting context content: '{context_content}'")
                loc.context_content = context_content
            if current_method:
                loc.parent = current_method
        else:
            # Fallback for older SourceLocation implementations
            loc = SourceLocation(
                filename=loc.filename,
                start_line=loc.start_line,
                start_col=loc.start_col,
                end_line=loc.end_line,
                end_col=loc.end_col,
                content=loc.content,
                parent=current_method,
                context=context,
                context_content=context_content
            )
        
        decreases_clauses.append(loc)
    
    return ProofContent(
        lemmas=lemmas,
        invariants=invariants,
        decreases_clauses=decreases_clauses,
        assertions=assertions
    )