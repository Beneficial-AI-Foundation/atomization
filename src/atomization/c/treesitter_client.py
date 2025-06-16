from pathlib import Path
import tree_sitter_c as tsc
from tree_sitter import Language, Parser

C_LANGUAGE = Language(tsc.language())
parser = Parser(C_LANGUAGE)


def parse_file(filename: str | Path) -> list:
    with open(filename, "r", encoding="utf-8") as c_file:
        text = c_file.read()
    tree = parser.parse(text.encode("utf-8"))
    return tree.root_node.children


def parse_text(text: str) -> list:
    tree = parser.parse(text.encode("utf-8"))
    return tree.root_node.children


if __name__ == "__main__":
    # Example usage
    nodes = parse_file(Path.cwd() / "examples" / "refinedc" / "src" / "example.c")
    print(nodes)
