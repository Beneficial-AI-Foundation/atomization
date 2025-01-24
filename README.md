# atomization

## Usage: local development, no docker

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

## Usage: on servers with docker

Due to the jank (non LTS server), we are using the old `docker-compose` executable instead of the current `docker compose` subcommand.

Test that mysql connection, environment variables, etc are working

```base
docker-compose run atomization test
```

The `main` script is bound to the `atomization` service entrypoint

```base
docker-compose run atomization <code_id>
docker-compose run atomization delete <package_id>
```
