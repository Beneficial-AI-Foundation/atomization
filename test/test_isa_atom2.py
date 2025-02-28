import pytest
import json
from pathlib import Path
from atomization.isabelle.atomizer import atomize_isa

# Test fixtures
@pytest.fixture(params=[f for f in Path("examples/isabelle").glob("*.thy")])
def sample_theory_file(request, tmp_path):
    """Fixture to provide paths to .thy files in examples/isabelle and a temporary output directory."""
    thy_file = request.param
    if not thy_file.exists():
        pytest.skip(f"Theory file not found: {thy_file}")

    # Create a temporary directory for output files
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return thy_file, output_dir


@pytest.fixture
def latex_symbols_file():
    """Provide the path to the latex symbols file."""
    return Path("src/atomization/isabelle/latex_unicode_map.json")

@pytest.fixture
def simple_theory_file(tmp_path):
    """Create a simple theory file with known content for testing."""
    theory_content = """
theory Simple
imports Main
begin

definition const_def: "const ≡ 5"

lemma const_lemma:
  shows "const = 5"
  using const_def by simp

theorem main_theorem:
  shows "const ≡ 5 ⇒ const = 5"
  using const_lemma by auto

end
"""
    theory_file = tmp_path / "Simple.thy"
    theory_file.write_text(theory_content)
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return theory_file, output_dir


def test_get_atoms_basic(sample_theory_file, latex_symbols_file):
    """Test basic atom extraction from a simple theory file"""
    thy_file, output_dir = sample_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    assert json_str != ""


def test_json_structure(simple_theory_file, latex_symbols_file):
    """Test the basic structure of the generated JSON."""
    thy_file, output_dir = simple_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    data = json.loads(json_str)
    
    # Check overall structure
    assert isinstance(data, dict)
    assert "Atoms" in data
    assert isinstance(data["Atoms"], list)
    
    # Should have exactly 3 atoms
    atoms = data["Atoms"]
    assert len(atoms) == 3


def test_atom_content(simple_theory_file, latex_symbols_file):
    """Test the content of individual atoms."""
    thy_file, output_dir = simple_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    data = json.loads(json_str)
    atoms = {atom["identifier"]: atom for atom in data["Atoms"]}
    
    # Check const_def atom
    assert "const_def" in atoms
    const_def = atoms["const_def"]
    assert const_def["statement_type"] == "definition"
    assert "const" in const_def["body"]
    assert const_def["language"] == "Isabelle"
    
    # Check const_lemma atom
    assert "const_lemma" in atoms
    const_lemma = atoms["const_lemma"]
    assert const_lemma["statement_type"] == "lemma"
    assert "const = 5" in const_lemma["body"]


def test_dependencies(simple_theory_file, latex_symbols_file):
    """Test that dependencies between atoms are correctly captured."""
    thy_file, output_dir = simple_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    data = json.loads(json_str)
    atoms = {atom["identifier"]: atom for atom in data["Atoms"]}
    
    # const_lemma should depend on const_def
    const_lemma_deps = atoms["const_lemma"]["deps"]
    assert "const_def" in const_lemma_deps
    
    # main_theorem should depend on const_lemma
    main_theorem_deps = atoms["main_theorem"]["deps"]
    assert "const_lemma" in main_theorem_deps


@pytest.fixture
def complex_theory_file(tmp_path):
    """Create a more complex theory file with different types of statements."""
    theory_content = """
theory Complex
imports Main
begin

fun factorial :: "nat ⇒ nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = Suc n * factorial n"

definition is_even :: "nat ⇒ bool" where
  "is_even n ≡ n mod 2 = 0"

lemma factorial_pos:
  shows "factorial n > 0"
  by (induct n) auto

theorem even_factorial:
  shows "n > 0 ⟹ ¬(is_even (factorial n))"
  using factorial_pos is_even by auto

end
"""
    theory_file = tmp_path / "Complex.thy"
    theory_file.write_text(theory_content)
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return theory_file, output_dir


def test_statement_types(complex_theory_file, latex_symbols_file):
    """Test handling of different statement types."""
    thy_file, output_dir = complex_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    data = json.loads(json_str)
    atoms = {atom["identifier"]: atom for atom in data["Atoms"]}
    
    # Check for function definition
    assert "factorial" in atoms
    assert atoms["factorial"]["statement_type"] == "fun"
    
    # Check for regular definition
    assert "is_even" in atoms
    assert atoms["is_even"]["statement_type"] == "definition"
    
    # Check for lemma
    assert "factorial_pos" in atoms
    assert atoms["factorial_pos"]["statement_type"] == "lemma"
    
    # Check theorem dependencies
    assert "even_factorial" in atoms
    even_factorial_deps = atoms["even_factorial"]["deps"]
    assert "factorial_pos" in even_factorial_deps
    assert "is_even" in even_factorial_deps


def test_get_atoms_nonexistent_file(latex_symbols_file):
    """Test handling of non-existent theory file"""
    with pytest.raises(FileNotFoundError):
        atomize_isa("nonexistent.thy", Path("."), latex_symbols_file)


def test_generated_files(sample_theory_file, latex_symbols_file):
    """Test that all expected output files are generated"""
    thy_file, output_dir = sample_theory_file
    
    # Generate JSON with atomizer
    atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    json_file = output_dir / Path(thy_file).with_suffix(".json").name
    
    # Clean up
    json_file.unlink()

def test_json_schema_validation(simple_theory_file, latex_symbols_file):
    """Test that the JSON structure adheres to the expected schema."""
    thy_file, output_dir = simple_theory_file
    json_str = atomize_isa(str(thy_file), output_dir, latex_symbols_file)
    data = json.loads(json_str)
    
    # Validate top-level structure
    assert isinstance(data, dict), "Top level should be a dictionary"
    assert "Atoms" in data, "Missing 'Atoms' key in top level"
    assert isinstance(data["Atoms"], list), "'Atoms' should be a list"
    
    # Validate each atom's structure
    required_fields = {"identifier", "body", "statement_type", "language", "deps"}
    field_types = {
        "identifier": str,
        "body": str,
        "statement_type": str,
        "language": str,
        "deps": list
    }
    
    for atom in data["Atoms"]:
        # Check all required fields are present
        assert isinstance(atom, dict), "Each atom should be a dictionary"
        assert set(atom.keys()) == required_fields, f"Atom missing required fields: {required_fields - set(atom.keys())}"
        
        # Validate field types
        for field, expected_type in field_types.items():
            assert isinstance(atom[field], expected_type), f"Field '{field}' should be of type {expected_type}"
        
        # Additional specific validations
        assert atom["language"] == "Isabelle", "Language should be 'Isabelle'"
        assert atom["statement_type"] in {"fun", "definition", "theorem", "lemma", "corollary", "proposition"}, \
            f"Invalid statement_type: {atom['statement_type']}"
        assert all(isinstance(dep, str) for dep in atom["deps"]), "All dependencies should be strings"

if __name__ == "__main__":
    pytest.main([__file__])
