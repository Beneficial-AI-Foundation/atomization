import subprocess
import sys
from pathlib import Path


def atomize_isa(theory_path: str, output_dir: Path) -> str:
    """
    Run atomizer on a theory file and return its JSON output as a string.

    Args:
        theory_path: Path to the .thy file
        output_dir: Path to the directory for output files

    Returns:
        The JSON content as a string

    Raises:
        subprocess.CalledProcessError: If isabelle command fails
        FileNotFoundError: If theory file or JSON output not found
    """
    # Ensure theory file exists and has .thy extension
    thy_path = Path(theory_path)
    if not thy_path.exists():
        raise FileNotFoundError(f"Theory file not found: {theory_path}")
    if thy_path.suffix != ".thy":
        raise ValueError(f"Expected .thy file, got: {theory_path}")

    # Expected JSON output path
    json_path = output_dir / thy_path.with_suffix(".json").name

    script_dir = Path(__file__).parent
    scala_file = script_dir / "atomizer_2.scala"

    # Run atomizer
    try:
        cmd = [
            "isabelle",
            "scala",
            "-explain",
            str(scala_file),
            str(thy_path),
            str(output_dir),
        ]
        result = subprocess.run(cmd, check=True, capture_output=True, text=True)

        # Check if JSON file was created
        if not json_path.exists():
            raise FileNotFoundError(
                f"JSON output not found at: {json_path}\n"
                + f"Atomizer output: {result.stdout}\n"
                + f"Atomizer errors: {result.stderr}"
            )

        # Read and return JSON content
        with open(json_path) as f:
            return f.read()

    except subprocess.CalledProcessError as e:
        print(f"Atomizer failed with return code {e.returncode}")
        print(f"stdout: {e.stdout}")
        print(f"stderr: {e.stderr}")
        raise


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python atomizer.py <theory_file.thy>")
        sys.exit(1)

    try:
        # Provide a default output directory if running as main
        json_content = atomize_isa(sys.argv[1], Path("."))
        print(json_content)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
