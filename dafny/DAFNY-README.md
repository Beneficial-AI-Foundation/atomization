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
python atomize.py <code_id>
```

Creates a package corresponding to the code and atomizes it into snippets.

### Clean up DB
```base
python atomize.py delete <package_id>
```

Deletes the package with `package_id`, finds the code it belongs to and nullifies that code's `package_id` value, and deletes the atomized snippets with that `package_id`

