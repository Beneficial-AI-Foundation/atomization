# atomization

## Lean 4 Atomizer

Goal: Extract all the transitive imports of a Lean definition.

Extract line/column information for each definition.

Then, split into spec (type signatures) and code (definition body). If the spec is `Prop`-valued, then the code is a proof.

### Ideas

- [ ] Try `fileMap`
- [ ] Try `nameMap`

