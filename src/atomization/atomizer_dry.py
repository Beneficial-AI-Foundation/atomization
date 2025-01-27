from pathlib import Path
from argparse import ArgumentParser
from atomization.coq.atomizer import CoqAtomizer

EXAMPLES = Path("examples")
COQ_FIXTURES = EXAMPLES / "coq"


def parser() -> ArgumentParser:
    parser = ArgumentParser()
    parser.add_argument("name", type=str)
    return parser


def main():
    args = parser().parse_args()
    the_file = COQ_FIXTURES / f"{args.name}.v"
    atomizer = CoqAtomizer(the_file)
    jsn = atomizer.jsonify_vlib()
    print(jsn)
