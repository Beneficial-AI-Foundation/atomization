#!/usr/bin/env sh

set -euo pipefail

exec nix develop --command uv run atomize "$@"
