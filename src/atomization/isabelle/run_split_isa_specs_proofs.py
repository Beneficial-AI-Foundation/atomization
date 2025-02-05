import subprocess
import sys
import os

def run_isabelle_scala(theory_file):
    script_dir = os.path.dirname(os.path.abspath(__file__))
    scala_file = os.path.join(script_dir, 'split_isa_specs_proofs.scala')
    command = ['isabelle', 'scala', '-explain', scala_file, theory_file]
    result = subprocess.run(command, capture_output=True, text=True)
    print(result.stdout)
    print(result.stderr, file=sys.stderr)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python run_split_isa_spec_proofs.py <theory_file.thy>")
        sys.exit(1)
    
    theory_file = sys.argv[1]
    run_isabelle_scala(theory_file)