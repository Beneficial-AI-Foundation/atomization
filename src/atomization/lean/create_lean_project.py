#!/usr/bin/env python3

import sys
import re
from pathlib import Path
import subprocess


def create_lakefile(filename: str):
    camel_case = "".join(
        word.capitalize() for word in filename.replace("-", "_").split("_")
    )

    template = f"""import Lake
open Lake DSL

package «{filename}» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.13.0"

@[default_target]
lean_lib «{camel_case}» where
  -- add any library configuration options here"""

    with open("lakefile.lean", "w") as f:
        f.write(template)


def run_lean(file_path):
    filename = Path(file_path).stem
    create_lakefile(filename)

    try:
        s = subprocess.run(
            f"lake build --verbose",
            shell=True,
            capture_output=True,
            timeout=60,
            text=True,
            cwd=str(Path(file_path).parent),
        )
    except Exception as e:
        return "", str(e)
    return s.stdout, s.stderr


def check_build_output(stdout, stderr):
    build_success = True
    has_sorries = False
    error_messages = []
    sorry_locations = []

    full_output = f"{stdout}\n{stderr}"

    if "build failed" in full_output.lower():
        build_success = False

    # Extract error messages
    seen_errors = set()
    collecting_goals = False
    current_error = []

    for line in full_output.splitlines():
        line = line.strip()
        if line.startswith("error:"):
            if current_error:
                seen_errors.add("\n".join(current_error))
                current_error = []
            if "unsolved goals" in line:
                collecting_goals = True
            current_error.append(line)
        elif (
            collecting_goals
            and line
            and not line.startswith("✔")
            and not line.startswith("Build")
        ):
            current_error.append(line)
        elif collecting_goals and (not line or line.startswith("✔")):
            collecting_goals = False
            if current_error:
                seen_errors.add("\n".join(current_error))
                current_error = []
        elif line.startswith("error:"):
            seen_errors.add(line)

    # if current_error:
    #     seen_errors.add("\n".join(current_error))

    error_messages.extend(list(seen_errors))

    # Check for sorries
    sorry_matches = re.finditer(
        r"warning: .*?:(\d+):(\d+): declaration uses \'sorry\'", full_output
    )

    for match in sorry_matches:
        has_sorries = True
        line_num = match.group(1)
        col_num = match.group(2)
        sorry_locations.append(f"Line {line_num}, Column {col_num}")

    final_message = ""
    if error_messages:
        final_message = "\n".join(error_messages)
    if sorry_locations:
        if final_message:
            final_message += "\n"
        final_message += f"Found 'sorry' in the following locations:\n" + "\n".join(
            sorry_locations
        )

    return build_success, has_sorries, final_message, sorry_locations


def verify_lean_proof(file_path):
    stdout, stderr = run_lean(file_path)
    build_success, has_sorries, error_msg, sorry_locations = check_build_output(
        stdout, stderr
    )

    if not build_success:
        return False, error_msg
    elif has_sorries:
        return False, error_msg

    return True, "Proof verification successful"


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python run_lean.py <filepath>")
        sys.exit(1)

    success, message = verify_lean_proof(sys.argv[1])
    print(message)
    sys.exit(0 if success else 1)
