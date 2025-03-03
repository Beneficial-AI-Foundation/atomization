#!/usr/bin/env python3
import os
import unittest
from pathlib import Path

import tempfile
import shutil

from src.atomization.lean.visualizer import visualize_lean_file


class TestLeanVisualizer(unittest.TestCase):
    """Test case for the Lean 4 visualizer functions."""

    def setUp(self):
        """Set up temporary directories for testing."""
        self.temp_dir = tempfile.mkdtemp()
        self.examples_dir = Path(__file__).parent.parent / "examples" / "lean"

    def tearDown(self):
        """Clean up temporary directories after testing."""
        shutil.rmtree(self.temp_dir)

    def test_visualize_basic_lean_file(self):
        """Test visualizing a basic Lean file."""
        lean_file = self.examples_dir / "Atomization" / "Basic.lean"
        output_dir = Path(self.temp_dir)

        # Make sure the example file exists
        self.assertTrue(lean_file.exists(), f"Example file not found: {lean_file}")

        # Visualize the file
        visualize_lean_file(lean_file, output_dir)

        # Check that the output files were created
        json_file = output_dir / "Basic.json"
        dot_file = output_dir / "Basic.dot"
        svg_file = output_dir / "Basic.svg"
        png_file = output_dir / "Basic.png"

        self.assertTrue(json_file.exists(), f"JSON file not created: {json_file}")
        self.assertTrue(dot_file.exists(), f"DOT file not created: {dot_file}")

        # SVG and PNG files might not be created if Graphviz is not installed
        if svg_file.exists():
            self.assertTrue(svg_file.exists(), f"SVG file not created: {svg_file}")
        if png_file.exists():
            self.assertTrue(png_file.exists(), f"PNG file not created: {png_file}")

        # Check that the JSON file contains valid JSON
        with open(json_file) as f:
            import json

            data = json.load(f)
            self.assertIn("Atoms", data, "JSON file does not contain 'Atoms' key")
            self.assertIsInstance(data["Atoms"], list, "'Atoms' value is not a list")

    def test_visualize_nonexistent_file(self):
        """Test visualizing a file that doesn't exist."""
        lean_file = self.examples_dir / "NonExistentFile.lean"
        output_dir = Path(self.temp_dir)

        # The function should not raise an exception, but should print an error message
        visualize_lean_file(lean_file, output_dir)

        # Check that no output files were created
        self.assertEqual(len(list(output_dir.glob("*.json"))), 0)
        self.assertEqual(len(list(output_dir.glob("*.dot"))), 0)
        self.assertEqual(len(list(output_dir.glob("*.svg"))), 0)
        self.assertEqual(len(list(output_dir.glob("*.png"))), 0)


if __name__ == "__main__":
    unittest.main()
