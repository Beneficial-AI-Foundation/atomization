# dafny_atomize.py
import sys
import json
from dataclasses import asdict
from get_code import get_code
from get_specs import get_specs
from get_proofs import get_proofs
from dafny_utils import SourceLocation

def format_code_segment(source_loc: SourceLocation) -> dict:
    """Format a source location into a dictionary with location and content."""
    return {
        'location': {
            'filename': source_loc.filename,
            'start_line': source_loc.start_line,
            'start_col': source_loc.start_col,
            'end_line': source_loc.end_line,
            'end_col': source_loc.end_col
        },
        'content': source_loc.content
    }

def atomize_dafny(filename: str) -> dict:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:
        code_content = get_code(filename)
        spec_content = get_specs(filename)
        proof_content = get_proofs(filename)
        
        
        return {
            "code": {
                "methods": [
                    format_code_segment(method) for method in code_content.methods
                ],
                "executable_functions": [
                    format_code_segment(func) for func in code_content.executable_functions
                ]
            },
            "spec": {
                "requires_clauses": [
                    format_code_segment(req) for req in spec_content.requires_clauses
                ],
                "ensures_clauses": [
                    format_code_segment(ens) for ens in spec_content.ensures_clauses
                ],
                "ghost_predicates": [
                    format_code_segment(pred) for pred in spec_content.ghost_predicates
                ],
                "ghost_functions": [
                    format_code_segment(func) for func in spec_content.ghost_functions
                ],
                "spec_functions": [
                    format_code_segment(func) for func in spec_content.spec_functions
                ]
            },
            "proof": {
                "lemmas": [
                    format_code_segment(lemma) for lemma in proof_content.lemmas
                ],
                "invariants": [
                    format_code_segment(inv) for inv in proof_content.invariants
                ],
                "decreases_clauses": [
                    format_code_segment(dec) for dec in proof_content.decreases_clauses
                ],
                "assertions": [
                    format_code_segment(asrt) for asrt in proof_content.assertions
                ]
            }
        }
    except Exception as e:
        print(f"Debug - Exception details: {type(e).__name__}: {str(e)}")
        raise Exception(f"Error analyzing {filename}: {str(e)}")

def main():
    if len(sys.argv) != 2:
        print("Usage: python dafny_atomize.py <dafny_file>")
        sys.exit(1)
        
    filename = sys.argv[1]
    try:
        result = atomize_dafny(filename)
        # Print to stdout
        print(json.dumps(result, indent=2))
        
        # Write to JSON file
        output_filename = filename.rsplit('.', 1)[0] + '_analysis.json'
        with open(output_filename, 'w') as f:
            json.dump(result, f, indent=2)
            
        print(f"\nAnalysis saved to {output_filename}")
    except Exception as e:
        print(f"Error: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()