# atomization

## Usage

### Dependencies

You'll have to have installed nix and [enabled flakes](https://nixos.wiki/wiki/flakes)

```base
nix develop
uv sync
```

To install python version and dependencies

### Atomize

```base
uv run main <code_id>
```

Creates a package corresponding to the code and atomizes it into snippets.

### Clean up DB

```base
uv run main delete <package_id>
```

Deletes the package with `package_id`, finds the code it belongs to and nullifies that code's `package_id` value, and deletes the atomized snippets with that `package_id`
