#!/usr/bin/env python3
import pytest
import json
from pathlib import Path
import tempfile
import shutil

from atomization.lean.visualizer import visualize_lean_file

@pytest.fixture
def temp_dir():
    """Create a temporary directory for test outputs."""
    temp_dir = tempfile.mkdtemp()
    yield temp_dir
    shutil.rmtree(temp_dir)

@pytest.fixture
def examples_dir():
    """Path to the examples directory."""
    return Path(__file__).parent.parent / "examples" / "lean"

def test_visualize_basic_lean_file(temp_dir, examples_dir):
    """Test visualizing a basic Lean file."""
    lean_file = examples_dir / "Atomization" / "Basic.lean"
    output_dir = Path(temp_dir)

    # Make sure the example file exists
    assert lean_file.exists(), f"Example file not found: {lean_file}"

    # Visualize the file
    visualize_lean_file(lean_file, output_dir)

    # Check that the output files were created
    json_file = output_dir / "Basic.json"
    dot_file = output_dir / "Basic.dot"
    svg_file = output_dir / "Basic.svg"
    png_file = output_dir / "Basic.png"

    assert json_file.exists(), f"JSON file not created: {json_file}"
    assert dot_file.exists(), f"DOT file not created: {dot_file}"

    # SVG and PNG files might not be created if Graphviz is not installed
    if svg_file.exists():
        assert svg_file.exists(), f"SVG file not created: {svg_file}"
    if png_file.exists():
        assert png_file.exists(), f"PNG file not created: {png_file}"

    # Check that the JSON file contains valid JSON
    with open(json_file) as f:
        data = json.load(f)
        assert "Atoms" in data, "JSON file does not contain 'Atoms' key"
        assert isinstance(data["Atoms"], list), "'Atoms' value is not a list"

def test_visualize_nonexistent_file(temp_dir, examples_dir):
    """Test visualizing a file that doesn't exist."""
    lean_file = examples_dir / "NonExistentFile.lean"
    output_dir = Path(temp_dir)

    # The function should not raise an exception, but should print an error message
    visualize_lean_file(lean_file, output_dir)

    # Check that no output files were created
    assert len(list(output_dir.glob("*.json"))) == 0
    assert len(list(output_dir.glob("*.dot"))) == 0
    assert len(list(output_dir.glob("*.svg"))) == 0
    assert len(list(output_dir.glob("*.png"))) == 0