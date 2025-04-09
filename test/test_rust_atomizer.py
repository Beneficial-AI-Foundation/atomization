import os
import pytest
from atomization.rust.atomizer import atomize_rust

def load_rust_files(folder_path):
    """Load all Rust files from a folder and concatenate their content."""
    rust_code = ""
    for file_name in os.listdir(folder_path):
        if file_name.endswith(".rs"):
            with open(os.path.join(folder_path, file_name), "r", encoding="utf-8") as f:
                rust_code += f.read() + "\n"
    return rust_code

@pytest.fixture
def rust_folder(tmp_path):
    """Create a temporary folder with Rust files for testing."""
    folder = tmp_path / "rust_code"
    folder.mkdir()

    # Create example Rust files
    (folder / "file1.rs").write_text("""
    pub fn add(a: i32, b: i32) -> i32 {
        a + b
    }
    """, encoding="utf-8")

    (folder / "file2.rs").write_text("""
    pub fn multiply(a: i32, b: i32) -> i32 {
        a * b
    }
                                     /// A function that calculates the factorial of a number
    pub fn factorial(n: u64) -> u64 {
        if n == 0 {
            1
        } else {
            n * factorial(n - 1)
        }
    }

    /// Returns true if the number is even
    pub fn is_even(n: u64) -> bool {
        n % 2 == 0
    }

    /// Calculates the sum of even numbers up to n
    pub fn sum_even(n: u64) -> u64 {
        let mut sum = 0;
        for i in 0..=n {
            if is_even(i) {
                sum += i;
            }
        }
        sum
    }
    """, encoding="utf-8")

    return folder


def test_atomize_rust_folder(rust_folder):
    """Test atomizing a folder of Rust code."""
    # Pass the folder path directly to atomize_rust
    atoms = atomize_rust(rust_folder)

    assert isinstance(atoms, dict)
    assert "atoms" in atoms
    assert len(atoms["atoms"]) > 0

        # Should have exactly 3 atoms
    atoms = atoms["atoms"]
    assert len(atoms) == 5

    # Check individual atoms
    atom_identifiers = {atom["identifier"] for atom in atoms}
    assert "factorial" in atom_identifiers
    assert "is_even" in atom_identifiers
    assert "sum_even" in atom_identifiers

    # Check dependencies
    factorial_atom = next(atom for atom in atoms if atom["identifier"] == "factorial")
    assert factorial_atom["deps"] == []

    is_even_atom = next(atom for atom in atoms if atom["identifier"] == "is_even")
    assert is_even_atom["deps"] == []

    sum_even_atom = next(atom for atom in atoms if atom["identifier"] == "sum_even")
    assert "is_even" in sum_even_atom["deps"]
