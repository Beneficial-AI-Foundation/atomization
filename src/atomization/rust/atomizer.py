import subprocess
import json
from pathlib import Path

def atomize_rust(folder: str) -> dict:
    """
    Run atomizer on a folder and return its JSON output as a Python dictionary.

    Args:
        folder: the folder with Rust files

    Returns:
        A dictionary containing the parsed JSON content with atoms and their dependencies

    Raises:
        subprocess.CalledProcessError: If cargo command fails
        FileNotFoundError: If folder not found
    """
    folder_path = Path(folder).resolve()  # Ensure absolute path

    if not folder_path.is_dir():
        raise ValueError(f"Provided path {folder_path} is not a directory.")

    rust_file = "call_graph_with_syn_v2"
    rust_project_dir = Path(__file__).parent  # Ensure `Cargo.toml` is found

    # Run atomizer
    try:
        cmd = [
            "cargo",
            "run",
            "--bin",
            str(rust_file),
            str(folder_path),
        ]
        result = subprocess.run(cmd, check=True, capture_output=True, text=True, cwd=rust_project_dir)

        # Check if JSON file was created
        json_path = rust_project_dir / "call_graph.json"
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

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Atomize Rust code in a folder")
    parser.add_argument("folder", type=str, help="Path to the folder containing Rust files")
    args = parser.parse_args()

    try:
        result = atomize_rust(args.folder)
        print(json.dumps(result, indent=2))
    except Exception as e:
        print(f"Error: {e}")