import subprocess
import sys

def run_isabelle_scala(theory_file):
    command = ['isabelle', 'scala', '-explain', 'split_isa_specs_proofs.scala', theory_file]
    result = subprocess.run(command, capture_output=True, text=True)
    print(result.stdout)
    print(result.stderr, file=sys.stderr)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python run_split_isa_spec_proofs.py <theory_file.thy>")
        sys.exit(1)
    
    theory_file = sys.argv[1]
    run_isabelle_scala(theory_file)