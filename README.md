# atomization
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
