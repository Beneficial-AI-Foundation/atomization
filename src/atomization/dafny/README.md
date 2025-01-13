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
- Classes

### Spec

Specification elements include:

- `requires` clauses (preconditions)
- `ensures` clauses (postconditions)
- `reads` clauses (state sensitivity conditions)
- `modifies` clauses (state effect conditions)
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
