# Dafny Atomizer

Dafny Atomizer takes a Dafny file and breaks it down into its atomic parts, specifically:

1. Code
1. Spec
1. Proof

## Components

### Code
In Dafny, `code` consists of executable elements:
- Methods (without verification annotations)
- Non-ghost functions
- Implementation details (e.g., variable declarations, assignments, loops)

### Spec
Specification elements include:
- `requires` clauses (preconditions)
- `ensures` clauses (postconditions)
- `ghost functions` (specification-only functions)
- `ghost predicates` (specification-only predicates)

### Proof
Proof elements demonstrate program correctness:
- `invariant` clauses (loop invariants) 
- `decreases` clauses (termination metrics)
- `assert` statements
- `lemma` declarations and their bodies

## Features
- Maintains source location information (line, column) for all elements
- Tracks parent-child relationships (e.g., requirements belonging to methods)
- Preserves code structure and indentation
- Handles nested structures (e.g., invariants within loops)

## Usage

### Atomize
```base
python dafny_atomize.py /path/to/dafny/file.dfy
```

Produces a JSON file containing all elements with their locations and relationships.


### Deatomize
```base
python dafny_deatomize.py /path/to/atomized/analysis.json
```

Recreates a valid Dafny file maintaining all code, spec, and proof relationships.

## JSON Structure

```json
{
  "code": {
    "methods": [...],
    "executable_functions": [...]
  },
  "spec": {
    "requires_clauses": [...],
    "ensures_clauses": [...],
    "ghost_predicates": [...],
    "ghost_functions": [...]
  },
  "proof": {
    "lemmas": [...],
    "invariants": [...],
    "decreases_clauses": [...],
    "assertions": [...]
  }
}
```

Each element includes its source location and parent information, enabling accurate reconstruction.