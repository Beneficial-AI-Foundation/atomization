#!/usr/bin/env bash
# Script to visualize a Lean 4 file and generate dependency graph visualizations

set -e

# Check if a file was provided
if [ $# -ne 1 ]; then
    echo "Usage: $0 <lean_file.lean>"
    exit 1
fi

LEAN_FILE="$1"

# Check if the file exists and has a .lean extension
if [ ! -f "$LEAN_FILE" ]; then
    echo "Error: File not found - $LEAN_FILE"
    exit 1
fi

if [[ ! "$LEAN_FILE" =~ \.lean$ ]]; then
    echo "Error: Not a Lean file - $LEAN_FILE"
    exit 1
fi

# Check for Graphviz
if ! command -v dot &>/dev/null; then
    echo "Warning: Graphviz 'dot' command not found. SVG/PNG visualization will be skipped."
    echo "Please install Graphviz to enable visualization."
fi

# Run the visualizer
echo "Visualizing Lean file: $LEAN_FILE"
python -m src.atomization.lean.visualizer "$LEAN_FILE"

# Get the base name without extension
BASE_NAME=$(basename "$LEAN_FILE" .lean)
DIR_NAME=$(dirname "$LEAN_FILE")

# Check if the output files were created
if [ -f "$DIR_NAME/$BASE_NAME.json" ]; then
    echo "JSON file created: $DIR_NAME/$BASE_NAME.json"
fi

if [ -f "$DIR_NAME/$BASE_NAME.dot" ]; then
    echo "DOT file created: $DIR_NAME/$BASE_NAME.dot"
fi

if [ -f "$DIR_NAME/$BASE_NAME.svg" ]; then
    echo "SVG file created: $DIR_NAME/$BASE_NAME.svg"
fi

if [ -f "$DIR_NAME/$BASE_NAME.png" ]; then
    echo "PNG file created: $DIR_NAME/$BASE_NAME.png"
fi

echo "Visualization complete!"
