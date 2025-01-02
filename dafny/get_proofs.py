# get_proofs.py
import re
from dataclasses import dataclass
from typing import List, Tuple
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

@dataclass
class InvariantGroup:
    method_name: str
    while_condition: str
    location: dict  # Location of the first invariant
    invariants: List[Tuple[int, str]]  # List of (offset, content)


def get_invariants_group(content: str, method_start: int, method_end: int) -> List[Tuple[int, str]]:
   """Get all invariants for a method with their offsets from method start."""
   invariant_pattern = r'invariant\s+([^{\n]+)'
   invariants = []
   
   for match in re.finditer(invariant_pattern, content):
       if method_start < match.start() < method_end:
           offset = match.start() - method_start
           invariants.append((offset, match.group(1).strip()))
           
   return sorted(invariants, key=lambda x: x[0])


def get_proofs(filename: str) -> ProofContent:
    content = read_dafny_file(filename)
    method_invariants = {}
    # Find lemmas
    lemma_pattern = r'lemma\s+\w+[^{]*{(?:[^{}]|{[^{}]*})*}'
    lemmas = []
    for match in re.finditer(lemma_pattern, content, re.DOTALL):
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Strip verification annotations from the content
        stripped_content = strip_verification_annotations(loc.content)
        loc.content = stripped_content
        lemmas.append(loc)
    
    # Find method pattern and process invariants separately
    method_pattern = r'method\s+(\w+)[^{]*{(?:[^{}]|{[^{}]*})*}'
    for method_match in re.finditer(method_pattern, content, re.DOTALL):
        method_name = method_match.group(1)
        method_content = method_match.group(0)
        
        # Find while condition before invariants
        while_pattern = r'while\s+([^{\n]+)'
        while_match = re.search(while_pattern, method_content)
        while_condition = while_match.group(1) if while_match else None
        
        # Get invariants for this method
        invs = get_invariants_group(content, method_match.start(), method_match.end())
        if invs:
            first_inv_loc = get_location(content, method_match.start(), method_match.end(), filename)
            method_invariants[method_name] = InvariantGroup(
                method_name=method_name,
                while_condition=while_condition,
                location=first_inv_loc.__dict__,
                invariants=invs
            )

    # Process individual invariant locations
    invariant_pattern = r'invariant\s+([^{\n]+)'
    invariants = []
    current_method = None

    for match in re.finditer(invariant_pattern, content):
        # Get the full location
        loc = get_location(content, match.start(), match.end(), filename)
        
        # Find the current method
        for method_match in re.finditer(method_pattern, content, re.DOTALL):
            if match.start() > method_match.start() and match.start() < method_match.end():
                current_method = method_match.group(1)
                break
        
        # Find the specific while loop containing this invariant
        context_content = None
        while_condition_pattern = r'while\s+([^{\n]+)'
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
            if match.start() > while_match.start(): # and match.start() < while_match.end():
                context = 'while_loop'
                context_content = f"while {while_match.group(1).strip()}"
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
        invariants=list(method_invariants.values()),
        decreases_clauses=decreases_clauses,
        assertions=assertions
    )