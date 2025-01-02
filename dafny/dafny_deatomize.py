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
    context_content: Optional[str] = None

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
        context=item.get('context', None),
        context_content=item.get('context_content', None)
    )

def collect_elements_by_parent(data: Dict[str, Any]) -> Dict[str | None, List[Location]]:
    """Group all elements by their parent, maintaining proper ordering."""
    elements_by_parent = {}
   
    # First collect all potential parents with their line numbers
    parent_order = []
    all_parents = []
    
    # Collect all parent elements with their line numbers
    for gf in data['spec']['ghost_functions']:
        loc = parse_location(gf)
        name = loc.content.split('(')[0].split()[2]  # 'ghost function name'
        all_parents.append((name, loc.start_line))
        elements_by_parent[name] = [loc]
            
    for func in data['code']['executable_functions']:
        loc = parse_location(func)
        name = loc.content.split('(')[0].split()[1]  # 'function name'
        all_parents.append((name, loc.start_line))
        elements_by_parent[name] = [loc]

    for method in data['code']['methods']:
        loc = parse_location(method)
        name = loc.content.split('(')[0].split()[1]  # 'method name'
        all_parents.append((name, loc.start_line))
        elements_by_parent[name] = [loc]
    
    for pred in data['spec']['ghost_predicates']:
        loc = parse_location(pred)
        name = loc.content.split('(')[0].split()[2]  # 'ghost predicate name'
        all_parents.append((name, loc.start_line))
        elements_by_parent[name] = [loc]
    
    for lemma in data['proof']['lemmas']:
        loc = parse_location(lemma)
        name = loc.content.split('(')[0].split()[1]  # 'lemma name'
        all_parents.append((name, loc.start_line))
        elements_by_parent[name] = [loc]
    
    # Handle invariant groups
    for group in data['proof']['invariant_groups']:
        method_name = group['method']
        if method_name in elements_by_parent:
            for inv in group['invariants']:
                loc = Location(
                    filename=group['location']['filename'],
                    start_line=group['location']['start_line'] + inv['offset'],
                    start_col=group['location']['start_col'],
                    end_line=group['location']['end_line'],
                    end_col=group['location']['end_col'],
                    content=f"invariant {inv['content']}",
                    parent=method_name,
                    context='while_loop',
                    context_content=f"while {group['while_condition']}"
                )
                elements_by_parent[method_name].append(loc)
    
    # Sort parents by line number to maintain original file order
    all_parents.sort(key=lambda x: x[1])
    parent_order = [name for name, _ in all_parents]
    
    # Then collect all child elements
    for requires in data['spec']['requires_clauses']:
        loc = parse_location(requires)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
    
    for ensures in data['spec']['ensures_clauses']:
        loc = parse_location(ensures)
        if loc.parent and loc.parent in elements_by_parent:
            elements_by_parent[loc.parent].append(loc)
        
    for reads in data['spec']['reads_clauses']:
            loc = parse_location(reads)
            if loc.parent and loc.parent in elements_by_parent:
                elements_by_parent[loc.parent].append(loc)
    
    # for inv in data['proof']['invariants']:
    #     loc = parse_location(inv)
    #     if loc.parent and loc.parent in elements_by_parent:
    #         elements_by_parent[loc.parent].append(loc)
            
    # Modify the collection of child elements to use both parent and context
    for dec in data['proof']['decreases_clauses']:
        loc = parse_location(dec)
        # Check if parent exists and matches a known parent
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
        reads = sorted([e for e in elements if "reads" in e.content],
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
        
        # Add requires/ensures if any
        indent = ' ' * (parent_elem.start_col + 2)
        
        # Track added requires/ensures to avoid duplicates
        added_requires = set()
        added_ensures = set()
        added_reads = set()
        
        for req in requires:
            if req.parent == parent_name and req.content not in added_requires:
                reconstructed.append(indent + req.content)
                added_requires.add(req.content)
        
        for ens in ensures:
            if ens.parent == parent_name and ens.content not in added_ensures:
                reconstructed.append(indent + ens.content)
                added_ensures.add(ens.content)

        for read in reads:
            if read.parent == parent_name and read.content not in added_reads:
                reconstructed.append(indent + read.content)
                added_reads.add(read.content)
        
        # for dec in decreases:
        #     if dec.parent == parent_name:  # Remove the context check
        #         reconstructed.append(indent + dec.content)
        # # Add decreases clauses only for ghost functions or methods at the top level
        # for dec in decreases:
        #     if (dec.parent == parent_name and 
        #         (dec.context == 'ghost_function' or 
        #          dec.context == 'method')):
        #         reconstructed.append(indent + dec.content)

        # Add decreases clause based on offset from parent line and column
        # Add global/parent-level decreases clauses with precise line offset
        for dec in decreases:
            if dec.parent == parent_name and dec.context != 'while_loop':
                reconstructed.append(indent + dec.content)

        # Process remaining lines, adding invariants where needed
        in_while = False
        
        for line in parent_lines[1:]:
            if "while" in line and "{" not in line:
                in_while = True
                reconstructed.append(body_indent + line)
                
                # Find matching invariant group
                for group in data['proof']['invariant_groups']:
                    if (group['method'] == parent_name and 
                        group['while_condition'] == line.strip().replace('while ', '')):
                        for inv in group['invariants']:
                            reconstructed.append(indent + f"invariant {inv['content']}")
            
                # Add while loop decreases 
                for dec in decreases:
                    if (dec.parent == parent_name and 
                        dec.context == 'while_loop'):
                        reconstructed.append(indent + dec.content)
            
            else:
                reconstructed.append(body_indent + line)
        
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