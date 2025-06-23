# Isabelle/HOL Atomizer 2

Isabelle/HOL Atomizer 2 takes an Isabelle/HOL theory file and generates a json corresponding to the dependency graph of the theory.

## Features

- Reuses Isabelle/HOL scala code
- Converts LaTeX-style symbols to Unicode using a configurable mapping file: Isabelle theory files contain symbols such as <Rightarrow>; we want to render them and for this we use `latex_unicode_map.json`.
