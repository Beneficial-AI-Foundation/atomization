#!/usr/bin/env python3
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union

from pantograph.server import Server

from atomization.lean.atomizer import (
    AtomizedDef,
    atomize_lean,
    atomize_project,
    build_lean_project,
    create_dummy_lean_project,
    dataclasses_json,
    set_toolchain,
)


def get_atom_color(kind: str) -> str:
    """Return a color for the atom based on its kind."""
    if kind == "code":
        return "#4CAF50"  # Green for regular code
    elif kind == "proof":
        return "#2196F3"  # Blue for proofs
    else:
        return "#9E9E9E"  # Gray for unknown kinds


def get_atom_shape(atom: AtomizedDef) -> str:
    """Return a shape for the atom based on its type."""
    # Check if it's a function/definition or a theorem/lemma/proof
    if atom.kind == "code":
        if "theorem" in atom.name.lower() or "lemma" in atom.name.lower():
            return "ellipse"  # Theorems/lemmas as ellipses
        else:
            return "box"  # Regular definitions as boxes
    elif atom.kind == "proof":
        return "ellipse"  # Proofs as ellipses
    else:
        return "diamond"  # Unknown as diamonds


def atoms_to_dot(atoms: List[AtomizedDef], output_path: Path) -> None:
    """
    Convert a list of AtomizedDef objects to a DOT graph and write it to a file.

    Args:
        atoms: List of atomized definitions
        output_path: Path to write the DOT file to
    """
    # Create a set of all nodes and edges
    nodes = []
    edges = []

    # Create a mapping of node names to ensure they're unique in the graph
    node_names = {}

    for i, atom in enumerate(atoms):
        # Create a sanitized name for the node (DOT requires unique IDs)
        node_name = f"node_{i}"
        node_names[atom.name] = node_name

        # Prepare the node attributes
        attrs = {
            "label": atom.name,
            "shape": get_atom_shape(atom),
            "fillcolor": get_atom_color(atom.kind if atom.kind else ""),
            "style": "filled",
            "tooltip": atom.source_code if atom.source_code else atom.name,
        }

        # Format attributes as a DOT-compatible string
        attr_str = ", ".join(f'{k}="{v}"' for k, v in attrs.items())
        nodes.append(f"    {node_name} [{attr_str}];")

        # Add edges for dependencies
        all_deps = set()
        if atom.type_dependencies:
            all_deps.update(atom.type_dependencies)
        if atom.value_dependencies:
            all_deps.update(atom.value_dependencies)

        for dep in all_deps:
            # Only add edges for dependencies that are in our list of atoms
            if dep in node_names:
                edges.append(f"    {node_name} -> {node_names[dep]};")

    # Assemble the DOT file content
    dot_content = "digraph G {\n"
    dot_content += "    rankdir=BT;\n"  # Bottom to Top layout
    dot_content += '    node [fontname="Arial", fontsize=10];\n'
    dot_content += "\n".join(nodes) + "\n"
    dot_content += "\n".join(edges) + "\n"
    dot_content += "}\n"

    # Write the DOT file
    with open(output_path, "w") as f:
        f.write(dot_content)

    print(f"DOT file written to: {output_path}")


def atoms_to_json(atoms: List[AtomizedDef], output_path: Path) -> None:
    """
    Convert a list of AtomizedDef objects to JSON and write it to a file.

    Args:
        atoms: List of atomized definitions
        output_path: Path to write the JSON file to
    """
    # Create the JSON structure
    json_atoms = []

    for atom in atoms:
        # Get all dependencies
        all_deps = set()
        if atom.type_dependencies:
            all_deps.update(atom.type_dependencies)
        if atom.value_dependencies:
            all_deps.update(atom.value_dependencies)

        # Filter out dependencies that aren't in our list of atoms
        valid_deps = [dep for dep in all_deps if any(a.name == dep for a in atoms)]

        json_atom = {
            "identifier": atom.name,
            "body": atom.source_code if atom.source_code else "",
            "statement_type": atom.kind if atom.kind else "unknown",
            "language": "Lean",
            "deps": valid_deps,
        }

        json_atoms.append({f"{atom.name}_atom": json_atom})

    # Write the JSON file
    with open(output_path, "w") as f:
        json.dump({"Atoms": json_atoms}, f, indent=2)

    print(f"JSON file written to: {output_path}")


def generate_svg(dot_path: Path, svg_path: Path) -> None:
    """
    Generate an SVG file from a DOT file using Graphviz.

    Args:
        dot_path: Path to the DOT file
        svg_path: Path to write the SVG file to
    """
    cmd = ["dot", "-Tsvg", str(dot_path), "-o", str(svg_path)]

    try:
        subprocess.run(cmd, check=True)
        print(f"SVG file generated: {svg_path}")
    except subprocess.CalledProcessError as e:
        print(f"Error generating SVG file: {e}")
    except FileNotFoundError:
        print("Error: Graphviz 'dot' command not found. Please install Graphviz.")


def generate_png(dot_path: Path, png_path: Path) -> None:
    """
    Generate a PNG file from a DOT file using Graphviz.

    Args:
        dot_path: Path to the DOT file
        png_path: Path to write the PNG file to
    """
    cmd = ["dot", "-Tpng", str(dot_path), "-o", str(png_path)]

    try:
        subprocess.run(cmd, check=True)
        print(f"PNG file generated: {png_path}")
    except subprocess.CalledProcessError as e:
        print(f"Error generating PNG file: {e}")
    except FileNotFoundError:
        print("Error: Graphviz 'dot' command not found. Please install Graphviz.")


def visualize_lean_file(
    file_path: Union[str, Path], output_dir: Optional[Path] = None
) -> None:
    """
    Visualize a Lean source file by generating JSON, DOT, SVG, and PNG files.

    Args:
        file_path: Path to the Lean source file
        output_dir: Optional output directory (defaults to the same directory as the source file)
    """
    file_path = Path(file_path)

    if not file_path.exists():
        print(f"Error: File not found - {file_path}")
        return

    if file_path.suffix != ".lean":
        print(f"Error: Not a Lean file - {file_path}")
        return

    # Determine output directory
    if output_dir is None:
        output_dir = file_path.parent

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Get the base name for output files
    base_name = file_path.stem

    # Set up paths for output files
    json_path = output_dir / f"{base_name}.json"
    dot_path = output_dir / f"{base_name}.dot"
    svg_path = output_dir / f"{base_name}.svg"
    png_path = output_dir / f"{base_name}.png"

    # Create a temporary Lean project
    pkg_id = hash(str(file_path)) % 1000000
    project_name = f"Pkg{pkg_id}"  # Match the project name used in create_dummy_lean_project
    create_dummy_lean_project(file_path.read_text(), pkg_id)

    try:
        # Set toolchain and build the project
        project_root = Path(f"/tmp/{project_name}")  # Match the path pattern in create_dummy_lean_project
        set_toolchain(project_root)
        build_lean_project(project_root)

        # Start a Pantograph server to interact with the Lean project
        # Correctly initialize the Server with imports and project_path
        server = Server(
            imports=["Init", project_name],  # List of imports
            project_path=str(project_root)   # Project path as a string
        )

        # Atomize the project
        atoms = atomize_project(server)

        # Filter atoms to only those with source code
        atoms = [atom for atom in atoms if atom.source_code is not None]

        # Generate visualization files
        atoms_to_json(atoms, json_path)
        atoms_to_dot(atoms, dot_path)
        generate_svg(dot_path, svg_path)
        generate_png(dot_path, png_path)

    finally:
        # Clean up the temporary project
        if (project_root := Path(f"/tmp/{project_name}")).exists():
            import shutil
            shutil.rmtree(project_root)


def main() -> None:
    if len(sys.argv) != 2:
        print("Usage: python visualizer.py <lean_file.lean>")
        sys.exit(1)

    file_path = sys.argv[1]
    visualize_lean_file(file_path)


if __name__ == "__main__":
    main()
