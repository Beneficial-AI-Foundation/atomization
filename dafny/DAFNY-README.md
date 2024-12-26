# Dafny Atomizer

Dafny Atomizer takes a Dafny file and breaks it down into its atomic parts, specifically:

1. Code
1. Spec
1. Proof

## Code

In Dafny, `code` is considered to be the executable functions and methods, without the verification annotations.

## Spec
Dafny Atomizer treats the `ensures` and `requires` clauses as `spec`, as well as `ghost functions` and `ghost predicates`.

## Proof
The `invariant`, `decreases`, `assert`, and `lemma` clauses and objects are collected as `proof` atoms.

## Usage

### Atomize
```python
python dafny_atomize.py /path/to/dafny/file.dfy
```

### Deatomize
```python
python dafny_deatomize.py /path/to/atomized/analysis.json
```