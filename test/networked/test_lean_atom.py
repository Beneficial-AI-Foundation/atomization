import pytest
from atomization.lean.atomizer import atomize_lean, create_dummy_lean_project


@pytest.fixture
def good_lean_file():
    """Fixture to provide content of Basic.lean which has no imports."""
    content = """/-!
# Atomization

All the identifiers start with `Atom_` to make them easy to filter so I can test the atomization fast.
-/


def Atom_g := 1

def Atom_f := 2
def Atom_fg := Atom_g + Atom_g
def Atom_f' : 2 = 2 := rfl

theorem Atom_f'' : 2 = 2 := by rfl
theorem Atom_f''' : 2 = 2 := by omega

def Atom_fib : Nat → Nat := fun n =>
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Atom_fib (n + 1) + Atom_fib n

def Atom_fibImperative (n: Nat) : Nat := Id.run do
  let mut a : Nat := 0
  let mut b : Nat := 1
  for _ in [0:n] do
    let c := a + b
    a := b
    b := c
  return b

@[csimp]
theorem Atom_fib_spec : @Atom_fib = @Atom_fibImperative := by
  sorry
"""
    return content


@pytest.fixture
def bad_lean_file():
    """Fixture to provide content of Main.lean which has imports."""
    content = """import Atomization
def main : IO Unit := do
  return ()
"""
    return content


def test_create_dummy_project_good_case(good_lean_file):
    """Test that create_dummy_lean_project works with a file with no imports."""
    result = create_dummy_lean_project(good_lean_file, 1000)
    assert result is True, "Should return True for files without imports"


def test_create_dummy_project_bad_case(bad_lean_file):
    """Test that create_dummy_lean_project fails gracefully with a file with imports."""
    result = create_dummy_lean_project(bad_lean_file, 2000)
    assert result is False, "Should return False for files with imports"


@pytest.mark.skip(
    reason="pantograph.server.ServerError: Cannot decode Json object. A server error may have occurred."
)
def test_atomize_good_case(good_lean_file):
    """Test successful atomization of Basic.lean (no imports)."""
    schema = atomize_lean(good_lean_file, 3000)

    # Basic checks to confirm success
    assert isinstance(schema, list)
    assert len(schema) > 0

    # Check schema structure of at least one atom
    assert any(atom for atom in schema)
    sample_atom = schema[0]
    assert "identifier" in sample_atom
    assert "body" in sample_atom
    assert "type" in sample_atom
    assert "language" in sample_atom
    assert "deps" in sample_atom
    assert sample_atom["language"] == "lean"

    # Check we found the expected atoms from Basic.lean
    identifiers = [atom["identifier"] for atom in schema]
    expected_identifiers = [
        "Atom_g",
        "Atom_f",
        "Atom_fg",
        "Atom_f'",
        "Atom_f''",
        "Atom_f'''",
        "Atom_fib",
        "Atom_fibImperative",
    ]

    for expected in expected_identifiers:
        assert any(expected in identifier for identifier in identifiers), (
            f"Missing expected identifier: {expected}"
        )


def test_atomize_bad_case_with_imports(bad_lean_file):
    """Test graceful failure when atomizing Main.lean with imports."""
    # Verify that the bad file actually has imports
    assert "import" in bad_lean_file, "Test file should contain imports"

    # Attempt atomization (should return empty list for files with imports)
    schema = atomize_lean(bad_lean_file, 4000)

    # Success criteria is an empty list, not an exception
    assert schema == [], "Should return empty list for files with imports"
