# Isabelle/HOL Atomizer

Isabelle/HOL Atomizer takes an Isabelle/HOL theory file, call it `My_thy.thy` and breaks it down into its atomic parts, specifically:

- Spec (in `My_thy_definitions.thy`)
- Proofs (in `My_thy_proofs.thy`)

In case the theory file contains the command `export_code`, the atomizer creates a folder `export` for the generated code.

## Components

### Spec

The generated specification file contains all (data)type definitions and functions.

### Proof

The generated proof file contains all the lemmas, theorems with their proofs.

### Code

In an Isabelle/HOL theory, with the command `export_code` one generates code for the functions specified as input to the command. The generated code is in the specified language (one of Haskell, Scala, OCaml, or SML).

## Features

- reuses Isabelle/HOL scala code

## How to run

- `python run_split_isa_specs_proofs.py <theory_file>`



