# dafny_atomize.py
import sys
import json
from dataclasses import asdict
from get_code import get_code
from get_specs import get_specs
from get_proofs import get_proofs

def atomize_dafny(filename: str) -> dict:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:
        code_content = get_code(filename)
        spec_content = get_specs(filename)
        proof_content = get_proofs(filename)
        
        # Convert dataclass objects to dictionaries
        return {
            "code": asdict(code_content),
            "spec": asdict(spec_content),
            "proof": asdict(proof_content)
        }
    except Exception as e:
        raise Exception(f"Error analyzing {filename}: {str(e)}")

def main():
    if len(sys.argv) != 2:
        print("Usage: python dafny_atomize.py <dafny_file>")
        sys.exit(1)
        
    filename = sys.argv[1]
    try:
        result = atomize_dafny(filename)
        
        # Print formatted output
        print("=== Dafny File Analysis ===")
        print(json.dumps(result, indent=2))
        
        # Save to JSON file
        output_filename = filename.rsplit('.', 1)[0] + '_analysis.json'
        with open(output_filename, 'w') as f:
            json.dump(result, f, indent=2)
            
        print(f"\nAnalysis saved to {output_filename}")
        
    except Exception as e:
        print(f"Error: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()