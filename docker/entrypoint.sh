#!/usr/bin/env sh

set -euo pipefail

# Enter nix shell and execute the command
exec uv run main "$@"
