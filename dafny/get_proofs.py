# get_proofs.py

import sys
from dataclasses import dataclass
from typing import List
import re
from dafny_utils import (
    read_dafny_file,
    extract_verification_annotations,
    get_loop_invariants
)

@dataclass
class ProofContent:
    lemmas: List[str]          # Lemma methods
    invariants: List[str]      # Loop invariants
    decreases_clauses: List[str]  # Decreases clauses
    assertions: List[str]      # Assert statements
    calc_statements: List[str] # Calc blocks for proofs

def parse_dafny_file(filename: str) -> ProofContent:
    content = read_dafny_file(filename)
    
    # Find all lemmas (including their bodies)
    lemma_pattern = r'lemma\s+(\w+[^{]*{[^}]*})'
    lemmas = re.findall(lemma_pattern, content, re.DOTALL)
    
    # Find methods to extract their loop invariants
    method_pattern = r'method\s+(\w+[^{]*{[^}]*})'
    methods = re.findall(method_pattern, content, re.DOTALL)
    
    # Collect all loop invariants
    all_invariants = []
    for method in methods:
        all_invariants.extend(get_loop_invariants(method))
    
    # Get decreases clauses and assertions
    _, decreases_clauses, assertions = extract_verification_annotations(content)
    
    # Find calc statements (used in proofs)
    calc_pattern = r'calc\s*{[^}]*}'
    calc_statements = re.findall(calc_pattern, content, re.DOTALL)
    
    return ProofContent(
        lemmas=[lemma.strip() for lemma in lemmas],
        invariants=[inv.strip() for inv in all_invariants],
        decreases_clauses=[dec.strip() for dec in decreases_clauses],
        assertions=[asrt.strip() for asrt in assertions],
        calc_statements=[calc.strip() for calc in calc_statements]
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
            
        print("\nCalc Statements:")
        for calc in proof_content.calc_statements:
            print(f"  {calc}\n")
            
    except FileNotFoundError:
        print(f"Error: Could not find file {filename}")
        sys.exit(1)
    except Exception as e:
        print(f"Error parsing file: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()