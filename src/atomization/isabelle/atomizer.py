import subprocess
import json
import tempfile
import re
from pathlib import Path


class TheoryParseError(Exception):
    """Raised when unable to parse theory name from content."""

    pass


def extract_theory_name(theory_content: str) -> str:
    """Extract theory name from content using regex.

    Args:
        theory_content: The content of the theory file

    Returns:
        The theory name

    Raises:
        TheoryParseError: If no theory name can be found in the content

    Example:
        >>> extract_theory_name('theory MyTheory\\nimports Main\\nbegin')
        'MyTheory'
    """
    match = re.search(r"theory\s+(\w+)", theory_content)
    if not match:
        raise TheoryParseError(
            "Could not find theory name in content. Expected 'theory <name>'"
        )
    return match.group(1)


def atomize_isa(theory_content: str) -> dict:
    """
    Run atomizer on a theory file and return its JSON output as a Python dictionary.

    Args:
        theory_content: Content of a theory file

    Returns:
        A dictionary containing the parsed JSON content with atoms and their dependencies

    Raises:
        subprocess.CalledProcessError: If isabelle command fails
        FileNotFoundError: If theory file not found
    """
    # Create temporary directory for both theory file and output
    with tempfile.TemporaryDirectory() as temp_dir:
        output_dir = Path(temp_dir)

        try:
            # Extract theory name and create theory file
            theory_name = extract_theory_name(theory_content)
        except TheoryParseError as e:
            raise ValueError(str(e))

        theory_path = output_dir / f"{theory_name}.thy"

        # Write theory content to temporary file
        with open(theory_path, "w", encoding="utf-8") as theory_file:
            theory_file.write(theory_content)

        script_dir = Path(__file__).parent
        latex_mapping = script_dir / "latex_unicode_map.json"
        scala_file = script_dir / "atomizer_2.scala"

        # Run atomizer
        try:
            cmd = [
                "isabelle",
                "scala",
                "-explain",
                str(scala_file),
                str(theory_path),
                str(output_dir),
                str(latex_mapping),
            ]
            result = subprocess.run(cmd, check=True, capture_output=True, text=True)

            # Check if JSON file was created
            json_path = output_dir / theory_path.with_suffix(".json").name
            if not json_path.exists():
                raise FileNotFoundError(
                    f"JSON output not found at: {json_path}\n"
                    + f"Atomizer output: {result.stdout}\n"
                    + f"Atomizer errors: {result.stderr}"
                )

            # Read and parse JSON content
            with open(json_path, encoding="utf-8") as f:
                atoms_dict = json.load(f)

            return atoms_dict

        except subprocess.CalledProcessError as e:
            print(f"Atomizer failed with return code {e.returncode}")
            print(f"stdout: {e.stdout}")
            print(f"stderr: {e.stderr}")
            raise
