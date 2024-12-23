# dafny_deatomize.py

import json
import sys
from dataclasses import dataclass
from typing import List, Dict, Any

@dataclass
class Location:
    filename: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    content: str
    parent: str

def parse_location(item: Dict[str, Any]) -> Location:
    """Convert a JSON location object into a Location instance."""
    loc = item['location']
    return Location(
        filename=loc['filename'],
        start_line=loc['start_line'],
        start_col=loc['start_col'],
        end_line=loc['end_line'],
        end_col=loc['end_col'],
        content=item['content'],
        parent=item.get('parent', None)
    )

def collect_elements_by_parent(data: Dict[str, Any]) -> Dict[str | None, List[Location]]:
    """Group all elements by their parent."""
    elements_by_parent = {}
    
    # First collect all potential parents (things without parents themselves)
    for method in data['code']['methods']:
        loc = parse_location(method)
        if loc.parent is None:
            elements_by_parent[loc.content.split()[1]] = [loc]  # Use method name as key
            
    for gf in data['spec']['ghost_functions']:
        loc = parse_location(gf)
        if loc.parent is None:
            elements_by_parent[loc.content.split()[-2]] = [loc]  # Use function name as key
            
    # Similar for ghost_predicates and lemmas...
    
    # Then collect all child elements
    for requires in data['spec']['requires_clauses']:
        loc = parse_location(requires)
        if loc.parent:
            if loc.parent not in elements_by_parent:
                elements_by_parent[loc.parent] = []
            elements_by_parent[loc.parent].append(loc)
    
    # Similar for ensures, invariants, and decreases clauses...
    
    return elements_by_parent

def reconstruct_file(elements_by_parent: Dict[str | None, List[Location]]) -> str:
    """Reconstruct the Dafny file content maintaining parent-child relationships."""
    # Sort all elements within each parent group by line number
    for parent, elements in elements_by_parent.items():
        elements.sort(key=lambda x: (x.start_line, x.start_col))
    
    # Now reconstruct in order
    reconstructed = []
    current_line = 1
    
    # Process each parent group
    for parent, elements in elements_by_parent.items():
        parent_element = next((e for e in elements if 'method' in e.content 
                             or 'function' in e.content 
                             or 'predicate' in e.content
                             or 'lemma' in e.content), None)
        
        if parent_element:
            # Add blank lines if needed
            while current_line < parent_element.start_line:
                reconstructed.append('')
                current_line += 1
            
            # Add parent declaration
            lines = parent_element.content.split('\n')
            reconstructed.extend(lines)
            current_line += len(lines)
            
            # Add its children in correct position
            child_elements = [e for e in elements if e != parent_element]
            for elem in child_elements:
                # Add with proper indentation
                indent = ' ' * (elem.start_col - 1)
                reconstructed.append(indent + elem.content)
                current_line += 1
        
        # Add blank line after each group
        reconstructed.append('')
        current_line += 1
    
    return '\n'.join(reconstructed)

def main():
    if len(sys.argv) != 2:
        print("Usage: python dafny_deatomize.py <analysis_json>")
        sys.exit(1)
        
    json_file = sys.argv[1]
    try:
        # Read JSON file
        with open(json_file, 'r') as f:
            data = json.load(f)
            
        # Collect and sort elements
        elements = collect_elements_by_parent(data)
        
        # Reconstruct file
        reconstructed = reconstruct_file(elements)
        
        # Write output
        output_file = json_file.replace('_analysis.json', '_reconstructed.dfy')
        with open(output_file, 'w') as f:
            f.write(reconstructed)
            
        print(f"Reconstructed Dafny file saved to {output_file}")
        
    except Exception as e:
        print(f"Error: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()