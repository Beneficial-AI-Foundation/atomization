def get_indentation(line: str) -> int:
    return len(line) - len(line.lstrip())


def join_lines_with_indentation(lines: list[tuple[str, int]]) -> str:
    result = []
    for line, indent in lines:
        if not line.strip():
            result.append("")  # Preserve empty lines
        else:
            result.append(" " * indent + line.strip())
    return "\n".join(result) + "\n"  # Add final newline


def collect_until_closing_brace(lines: list[str], start_idx: int) -> tuple[str, int]:
    brace_count = 0
    chunk = []
    i = start_idx
    empty_lines_after = 0

    while i < len(lines):
        line = lines[i]
        if not line.strip():
            if brace_count == 0 and "{" in "".join(l[0] for l in chunk):
                empty_lines_after += 1
                if empty_lines_after > 1:  # Found two consecutive empty lines
                    break
            else:
                chunk.append(("", get_indentation(line)))
            i += 1
            continue

        empty_lines_after = 0
        indentation = get_indentation(line)
        chunk.append((line.strip(), indentation))
        brace_count += line.strip().count("{")
        brace_count -= line.strip().count("}")

        if brace_count == 0 and "{" in "".join(l[0] for l in chunk):
            i += 1
            break
        i += 1
    return join_lines_with_indentation(chunk), i


def parse_dafny(content: str) -> list[dict[str, str]]:
    lines = content.split("\n")
    chunks = []
    chunk_order = 0
    i = 0

    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue

        if line.strip().startswith(("ghost", "lemma")):
            chunk, i = collect_until_closing_brace(lines, i)
            chunks.append(
                {
                    "content": chunk,
                    "type": "proof" if line.strip().startswith("lemma") else "spec",
                    "order": chunk_order,
                }
            )
            chunk_order += 1
            continue

        if line.strip().startswith(
            ("method", "function")
        ) and not line.strip().startswith("ghost"):
            # Get the method/function signature
            signature = [(line.strip(), get_indentation(line))]
            i += 1

            chunks.append(
                {
                    "content": join_lines_with_indentation(signature),
                    "type": "spec+code",
                    "order": chunk_order,
                }
            )
            chunk_order += 1

            # Collect specs (requires/ensures/decreases)
            spec = []
            while i < len(lines):
                line = lines[i]
                if not line.strip():
                    i += 1
                    continue
                if "{" in line:
                    break
                if any(x in line for x in ["requires", "ensures", "decreases"]):
                    spec.append((line.strip(), get_indentation(line)))
                    i += 1
                    continue
                i += 1

            if spec:
                chunks.append(
                    {
                        "content": join_lines_with_indentation(spec),
                        "type": "spec",
                        "order": chunk_order,
                    }
                )
                chunk_order += 1

            # Process method/function body
            current_chunk = [(line.strip(), get_indentation(line))]
            brace_count = line.count("{")
            code_chunks = []

            while i < len(lines) and brace_count > 0:
                i += 1
                if i >= len(lines):
                    break

                line = lines[i]
                if not line.strip():
                    continue

                current_indent = get_indentation(line)
                if "invariant" in line.strip() or "decreases" in line.strip():
                    if current_chunk:
                        code_chunks.append(
                            ("code", join_lines_with_indentation(current_chunk))
                        )

                    proof_lines = [(line.strip(), current_indent)]
                    while i + 1 < len(lines):
                        next_line = lines[i + 1]
                        if not next_line.strip():
                            i += 1
                            continue
                        if not (
                            "invariant" in next_line.strip()
                            or "decreases" in next_line.strip()
                        ):
                            break
                        proof_lines.append(
                            (next_line.strip(), get_indentation(next_line))
                        )
                        i += 1

                    code_chunks.append(
                        ("proof", join_lines_with_indentation(proof_lines))
                    )
                    current_chunk = []
                    continue

                current_chunk.append((line.strip(), current_indent))
                brace_count += line.count("{")
                brace_count -= line.count("}")

                if brace_count == 0:
                    if current_chunk:
                        code_chunks.append(
                            ("code", join_lines_with_indentation(current_chunk))
                        )

            for chunk_type, chunk_content in code_chunks:
                chunks.append(
                    {"content": chunk_content, "type": chunk_type, "order": chunk_order}
                )
                chunk_order += 1
            continue

        i += 1

    return chunks
