# get_proofs.py
import re
from dataclasses import dataclass
from typing import List
from dafny_utils import (
    read_dafny_file,
    extract_verification_annotations,
    find_all_with_positions,
    SourceLocation,
    get_loop_invariants
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
    lemmas = find_all_with_positions(lemma_pattern, content, filename)
    
    # Find invariants
    invariant_pattern = r'invariant\s+([^{\n]+)'
    invariants = find_all_with_positions(invariant_pattern, content, filename)
    
    # Find decreases clauses
    decreases_pattern = r'decreases\s+([^{\n]+)'
    decreases = find_all_with_positions(decreases_pattern, content, filename)
    
    # Find assertions
    assert_pattern = r'assert\s+([^;]+);'
    assertions = find_all_with_positions(assert_pattern, content, filename)
    
    return ProofContent(
        lemmas=lemmas,
        invariants=invariants,
        decreases_clauses=decreases,
        assertions=assertions
    )