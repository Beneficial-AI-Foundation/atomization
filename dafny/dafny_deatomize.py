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

def parse_location(item: Dict[str, Any]) -> Location:
    """Convert a JSON location object into a Location instance."""
    loc = item['location']
    return Location(
        filename=loc['filename'],
        start_line=loc['start_line'],
        start_col=loc['start_col'],
        end_line=loc['end_line'],
        end_col=loc['end_col'],
        content=item['content']
    )

def collect_all_elements(data: Dict[str, Any]) -> List[Location]:
    """Collect all elements from the JSON into a single list."""
    elements = []
    
    # Collect from code section
    for method in data['code']['methods']:
        elements.append(parse_location(method))
    for func in data['code']['executable_functions']:
        elements.append(parse_location(func))
        
    # Collect from spec section
    for req in data['spec']['requires_clauses']:
        elements.append(parse_location(req))
    for ens in data['spec']['ensures_clauses']:
        elements.append(parse_location(ens))
    for pred in data['spec']['ghost_predicates']:
        elements.append(parse_location(pred))
    for func in data['spec']['ghost_functions']:
        elements.append(parse_location(func))
    for func in data['spec']['spec_functions']:
        elements.append(parse_location(func))
        
    # Collect from proof section
    for lemma in data['proof']['lemmas']:
        elements.append(parse_location(lemma))
    for inv in data['proof']['invariants']:
        elements.append(parse_location(inv))
    for dec in data['proof']['decreases_clauses']:
        elements.append(parse_location(dec))
    for asrt in data['proof']['assertions']:
        elements.append(parse_location(asrt))
    
    return elements

def reconstruct_file(elements: List[Location]) -> str:
    """Reconstruct the Dafny file content from sorted elements."""
    # Sort elements by line number and then column
    sorted_elements = sorted(
        elements, 
        key=lambda x: (x.start_line, x.start_col)
    )
    
    # Initialize output
    current_line = 1
    reconstructed = []
    
    # Process each element
    for elem in sorted_elements:
        # Add blank lines if needed
        while current_line < elem.start_line:
            reconstructed.append('')
            current_line += 1
            
        # Add content with proper indentation
        lines = elem.content.split('\n')
        for i, line in enumerate(lines):
            if i == 0:
                # First line: add proper leading spaces
                padding = ' ' * (elem.start_col - 1)
                reconstructed.append(padding + line)
            else:
                # Preserve original indentation for subsequent lines
                reconstructed.append(line)
        
        current_line = elem.end_line + 1
    
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
        elements = collect_all_elements(data)
        
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