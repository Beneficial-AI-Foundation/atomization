# get_proofs.py
import re
from dataclasses import dataclass
from typing import List
from dafny_utils import (
    read_dafny_file,
    extract_verification_annotations,
    get_loop_invariants,
    extract_lemmas
)

@dataclass
class ProofContent:
    lemmas: List[str]
    invariants: List[str]
    decreases_clauses: List[str]
    assertions: List[str]

def get_proofs(filename: str) -> ProofContent:
    content = read_dafny_file(filename)
    
    # Get complete lemmas using the utility function
    lemmas = extract_lemmas(content)
    
    # Find methods with their bodies
    method_pattern = r'method\s+(\w+[^{]*{[^}]*})'
    methods = re.findall(method_pattern, content, re.DOTALL)
    
    # Collect all loop invariants using the utility function
    all_invariants = []
    for method in methods:
        all_invariants.extend(get_loop_invariants(method))
    
    # Get decreases clauses and assertions using the utility function
    _, decreases_clauses, assertions = extract_verification_annotations(content)
    
    return ProofContent(
        lemmas=lemmas,
        invariants=[inv.strip() for inv in all_invariants],
        decreases_clauses=[dec.strip() for dec in decreases_clauses],
        assertions=[asrt.strip() for asrt in assertions]
    )