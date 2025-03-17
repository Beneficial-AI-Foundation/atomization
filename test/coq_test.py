from pathlib import Path
import pytest
from atomization.coq.atomizer import CoqAtomizer

EXAMPLES = Path("examples")
COQ_FIXTURES = EXAMPLES / "coq"


@pytest.mark.parametrize("name", ["minimal", "trivial", "days", "sumupto"])
def test_coq_file_structure(name):
    the_file = COQ_FIXTURES / f"{name}.v"
    atomizer = CoqAtomizer(the_file)
    jsn = atomizer.jsonify_vlib()
    for item in jsn:
        assert "content" in item.keys()
        assert "type" in item.keys()
