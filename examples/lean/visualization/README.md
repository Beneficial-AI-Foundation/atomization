# Lean Visualization Example

This directory contains examples of using the atomization visualization features with Lean code.

## Files

- `Basic.lean`: A Lean source file containing various definitions, theorems, and proofs
- `Basic.json`: JSON representation of the atomized Lean code
- `Basic.dot`: Graph representation in DOT format 
- `Basic.svg`: Visual graph rendered as SVG

## How to Run

You can run the example visualization script with:

```bash
# From the project root
cd examples/lean/visualization
python run_visualization.py
```

This will process `Basic.lean` and generate all the visualization files.

## What's Happening

The visualization process consists of several steps:

1. **Lean code atomization**: The Lean code is parsed and atomized into individual definitions, theorems, etc.
2. **JSON generation**: The atomized code is converted to a JSON representation 
3. **DOT graph generation**: The JSON is converted to a DOT graph format
4. **SVG rendering**: The DOT graph is rendered as an SVG image using Graphviz

## Visualization Features

The visualization represents different types of Lean code elements as follows:

- **Regular definitions** (green boxes): Functions, constants, and other definitions
- **Theorems and proofs** (blue ellipses): Mathematical statements and their proofs
- **Arrows**: Dependencies between definitions, showing how elements build on each other

This visualization helps to understand the structure and dependencies in Lean code, making it easier to navigate complex mathematical proofs and definitions.

## Requirements

To use the visualization features, you need:

- Lean 4
- Python 3.10+
- Graphviz (for DOT to SVG/PNG conversion)

## Integration with Atomizer

This visualization feature is integrated into the main atomizer command line tool:

```bash
# From the project root
uv run src/atomization/atomizer.py visualize examples/lean/Basic.lean --output-dir output
``` 