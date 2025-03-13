import pytest
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


def test_get_atoms_basic(sample_theory_file):
    """Test basic atom extraction from a simple theory file"""
    thy_file, output_dir = sample_theory_file
    json_str = atomize_isa(str(thy_file), output_dir)
    assert json_str != ""


def test_get_atoms_nonexistent_file():
    """Test handling of non-existent theory file"""
    with pytest.raises(FileNotFoundError):
        atomize_isa("nonexistent.thy", Path("."))


def test_generated_files(sample_theory_file):
    """Test that all expected output files are generated"""
    thy_file, output_dir = sample_theory_file
    atomize_isa(str(thy_file), output_dir)

    base_path = Path(thy_file)

    # Construct the full output path
    json_path = output_dir / base_path.with_suffix(".json").name
    dot_path = output_dir / base_path.with_suffix(".dot").name
    png_path = output_dir / base_path.with_suffix(".png").name
    svg_path = output_dir / base_path.with_suffix(".svg").name

    assert json_path.exists()
    assert dot_path.exists()
    assert png_path.exists()
    assert svg_path.exists()

    # Clean up generated files
    json_path.unlink()
    dot_path.unlink()
    png_path.unlink()
    svg_path.unlink()


if __name__ == "__main__":
    pytest.main([__file__])
