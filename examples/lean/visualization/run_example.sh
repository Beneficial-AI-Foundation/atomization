#!/bin/bash

# Script to run the Lean visualization example

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../" && pwd)"

# Check if Python is available
if ! command -v python3 &>/dev/null; then
    echo "Python 3 is required but not found. Please install Python 3."
    exit 1
fi

# Check if Graphviz is available
if ! command -v dot &>/dev/null; then
    echo "Graphviz 'dot' command not found. Please install Graphviz."
    echo "Continuing anyway but SVG conversion will fail..."
fi

echo "=== Lean Visualization Example ==="
echo "Project root: $PROJECT_ROOT"
echo "Working directory: $SCRIPT_DIR"

# Run the Python script
cd "$SCRIPT_DIR"
echo -e "\nRunning visualization script..."
python3 run_visualization.py

# Check if the SVG file exists
if [ -f "$SCRIPT_DIR/Basic.svg" ]; then
    echo -e "\nVisualization completed successfully!"
    echo "Generated files:"
    echo "- JSON: $SCRIPT_DIR/Basic.json"
    echo "- DOT: $SCRIPT_DIR/Basic.dot"
    echo "- SVG: $SCRIPT_DIR/Basic.svg"

    # Open the SVG file if on macOS
    if [[ "$OSTYPE" == "darwin"* ]]; then
        echo -e "\nOpening SVG file..."
        open "$SCRIPT_DIR/Basic.svg"
    else
        echo -e "\nTo view the SVG file, open: $SCRIPT_DIR/Basic.svg"
    fi
else
    echo -e "\nVisualization failed to create SVG file."
    echo "Please check the script output for errors."
fi
