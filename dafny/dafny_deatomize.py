# dafny_deatomize.py

import json
import sys
from dataclasses import dataclass
from typing import List, Dict, Any, Optional

@dataclass
class Location:
    filename: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    content: str
    parent: str
    context: Optional[str] = None

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
        parent=item.get('parent', None),
        context=item.get('context', None)
    )

def collect_elements_by_parent(data: Dict[str, Any]) -> Dict[str | None, List[Location]]:
    """Group all elements by their parent, maintaining proper ordering."""
    elements_by_parent = {}
    
    # First collect all potential parents in original order
    parent_order = []
    
    for gf in data['spec']['ghost_functions']:
        loc = parse_location(gf)
        name = loc.content.split('(')[0].split()[2]  # 'ghost function name'
        parent_order.append(name)
        elements_by_parent[name] = [loc]
            
    for method in data['code']['methods']:
        loc = parse_location(method)
        name = loc.content.split('(')[0].split()[1]  # 'method name'
        parent_order.append(name)
        elements_by_parent[name] = [loc]
    
    for pred in data['spec']['ghost_predicates']:
        loc = parse_location(pred)
        name = loc.content.split('(')[0].split()[2]  # 'ghost predicate name'
        parent_order.append(name)
        elements_by_parent[name] = [loc]
    
    for lemma in data['proof']['lemmas']:
        loc = parse_location(lemma)
        name = loc.content.split('(')[0].split()[1]  # 'lemma name'
        parent_order.append(name)
        elements_by_parent[name] = [loc]
    
    # Then collect all child elements
    for requires in data['spec']['requires_clauses']:
        loc = parse_location(requires)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
    
    for ensures in data['spec']['ensures_clauses']:
        loc = parse_location(ensures)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
    
    for inv in data['proof']['invariants']:
        loc = parse_location(inv)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
            
    for dec in data['proof']['decreases_clauses']:
        loc = parse_location(dec)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
            
    return elements_by_parent, parent_order

def reconstruct_file(elements_by_parent: Dict[str, List[Location]], parent_order: List[str]) -> str:
    reconstructed = []
    current_line = 1

    for parent_name in parent_order:
        elements = elements_by_parent[parent_name]
        
        # Group elements by type
        parent_elem = next(e for e in elements if e.parent is None)
        requires = sorted([e for e in elements if "requires" in e.content], 
                        key=lambda x: (x.start_line, x.start_col))
        ensures = sorted([e for e in elements if "ensures" in e.content],
                        key=lambda x: (x.start_line, x.start_col))
        invariants = sorted([e for e in elements if "invariant" in e.content],
                          key=lambda x: (x.start_line, x.start_col))
        decreases = sorted([e for e in elements if "decreases" in e.content],
                         key=lambda x: (x.start_line, x.start_col))
        
        # Add blank lines if needed
        while current_line < parent_elem.start_line:
            reconstructed.append('')
            current_line += 1

        # Split parent content into lines and process
        parent_lines = parent_elem.content.split('\n')
        body_indent = ' ' * (parent_elem.start_col - 1)
        
        # Add first line (signature)
        reconstructed.append(body_indent + parent_lines[0])
        
        # Add requires/ensures/decreases if any
        indent = ' ' * (parent_elem.start_col + 2)
        for req in requires:
            if req.parent == parent_name:  # Only add if it belongs to this parent
                reconstructed.append(indent + req.content)
        
        for ens in ensures:
            if ens.parent == parent_name:
                reconstructed.append(indent + ens.content)
        
        # Add top-level function/method decreases clauses
        for dec in decreases:
            if (dec.parent == parent_name and 
                (dec.context == 'ghost_function' or dec.context == 'method')):
                reconstructed.append(indent + dec.content)
            
        # Process remaining lines, adding invariants where needed
        in_while = False
        for line in parent_lines[1:]:
            if "while" in line and "{" not in line:
                in_while = True
                reconstructed.append(body_indent + line)
                # Add invariants
                for inv in invariants:
                    if inv.parent == parent_name:
                        reconstructed.append(indent + inv.content)
                
                # Add while loop decreases 
                for dec in decreases:
                    if (dec.parent == parent_name and 
                        dec.context == 'while_loop'):
                        reconstructed.append(indent + dec.content)
            else:
                reconstructed.append(body_indent + line if line.strip() else '')
        
        # Add blank line after
        reconstructed.append('')
        current_line = len(reconstructed)
    
    return '\n'.join(filter(lambda x: not '<userStyle>' in x, reconstructed))

def main():
    if len(sys.argv) != 2:
        print("Usage: python dafny_deatomize.py <analysis_json>")
        sys.exit(1)
        
    json_file = sys.argv[1]
    try:
        # Read JSON file
        with open(json_file, 'r') as f:
            data = json.load(f)
            
        # Collect elements and their ordering
        elements_by_parent, parent_order = collect_elements_by_parent(data)
        
        # Reconstruct file
        reconstructed = reconstruct_file(elements_by_parent, parent_order)
        
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