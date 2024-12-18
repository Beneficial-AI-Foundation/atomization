# get_proofs.py

import sys
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
    lemmas: List[str]          # Complete lemma declarations and bodies
    invariants: List[str]      # Loop invariants
    decreases_clauses: List[str]  # Decreases clauses
    assertions: List[str]      # Assert statements

def parse_dafny_file(filename: str) -> ProofContent:
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

def main():
    if len(sys.argv) != 2:
        print("Usage: python get_proofs.py <dafny_file>")
        sys.exit(1)
        
    filename = sys.argv[1]
    
    try:
        proof_content = parse_dafny_file(filename)
        
        print("=== Proof Content Analysis ===")
        print("\nLemmas:")
        for lemma in proof_content.lemmas:
            print(f"  {lemma}\n")
            
        print("\nLoop Invariants:")
        for inv in proof_content.invariants:
            print(f"  - {inv}")
            
        print("\nDecreases Clauses:")
        for dec in proof_content.decreases_clauses:
            print(f"  - {dec}")
            
        print("\nAssertions:")
        for asrt in proof_content.assertions:
            print(f"  - {asrt}")
            
    except FileNotFoundError:
        print(f"Error: Could not find file {filename}")
        sys.exit(1)
    except Exception as e:
        print(f"Error parsing file: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()