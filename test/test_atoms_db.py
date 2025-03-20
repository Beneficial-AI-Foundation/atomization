import pytest
from atomization.atomizer import save_atoms_to_db
from mysql.connector import Error as MysqlConnectorError

# Add pytest-mock fixture
pytest_plugins = ["pytest_mock"]


@pytest.fixture
def mock_db_connection(mocker):
    """Mock database connection and cursor"""
    mock_cursor = mocker.MagicMock()
    mock_conn = mocker.MagicMock()
    mock_conn.__enter__.return_value = mock_conn
    mock_conn.cursor.return_value = mock_cursor
    mocker.patch("atomization.atomizer.DBConnection", return_value=mock_conn)
    return mock_cursor


@pytest.fixture
def isabelle_atoms():
    """Sample Isabelle atoms with string identifiers as dependencies"""
    return {
        "Atoms": [
            {
                "identifier": "const_def",
                "body": "const ≡ 5",
                "statement_type": "definition",
                "deps": [],
            },
            {
                "identifier": "const_lemma",
                "body": "shows const = 5",
                "statement_type": "lemma",
                "deps": ["const_def"],
            },
            {
                "identifier": "main_theorem",
                "body": "shows const ≡ 5 ⇒ const = 5",
                "statement_type": "theorem",
                "deps": ["const_lemma"],
            },
        ]
    }


@pytest.fixture
def lean_atoms():
    """Sample Lean atoms with full atom objects as dependencies"""
    return [
        {"identifier": "const_def", "body": "const := 5", "type": "code", "deps": []},
        {
            "identifier": "const_lemma",
            "body": "theorem const_eq : const = 5",
            "type": "proof",
            "deps": [
                {
                    "identifier": "const_def",
                    "body": "const := 5",
                    "type": "code",
                    "deps": [],
                }
            ],
        },
    ]


@pytest.fixture
def mock_existing_atoms(mock_db_connection):
    """Mock cursor to simulate existing atoms in DB"""
    # Setup mock to return existing atoms for const_def
    mock_db_connection.fetchall.return_value = [{"identifier": "const_def", "id": 42}]
    return mock_db_connection


def test_save_isabelle_atoms(mock_db_connection, isabelle_atoms):
    """Test saving Isabelle atoms with string dependencies"""
    code_id = 123
    save_atoms_to_db(isabelle_atoms, code_id)

    # Check atoms were inserted correctly
    atom_inserts = [
        c
        for c in mock_db_connection.execute.call_args_list
        if "INSERT INTO atoms" in c[0][0]
    ]
    assert len(atom_inserts) == 3

    # Check dependencies were inserted using executemany
    dep_inserts = [
        c
        for c in mock_db_connection.executemany.call_args_list
        if "INSERT INTO atomsdependencies" in c[0][0]
    ]
    assert len(dep_inserts) == 2  # Two batches of dependency insertions

    # Verify the content of dependency insertions
    first_dep = dep_inserts[0]
    second_dep = dep_inserts[1]
    # const_lemma depends on const_def
    assert len(first_dep[0][1]) == 1  # One dependency in first batch
    # main_theorem depends on const_lemma
    assert len(second_dep[0][1]) == 1  # One dependency in second batch


def test_save_lean_atoms(mock_db_connection, lean_atoms):
    """Test saving Lean atoms with full atom dependencies"""
    code_id = 123
    save_atoms_to_db(lean_atoms, code_id)

    # Check atoms were inserted correctly
    atom_inserts = [
        c
        for c in mock_db_connection.execute.call_args_list
        if "INSERT INTO atoms" in c[0][0]
    ]
    assert len(atom_inserts) == 2

    # Check dependencies were inserted using executemany
    dep_inserts = [
        c
        for c in mock_db_connection.executemany.call_args_list
        if "INSERT INTO atomsdependencies" in c[0][0]
    ]
    assert len(dep_inserts) == 1  # One batch of dependency insertions

    # Verify the content of dependency insertion
    first_dep = dep_inserts[0]
    # const_lemma depends on const_def
    assert len(first_dep[0][1]) == 1  # One dependency in the batch


def test_save_atoms_error_handling(mock_db_connection, isabelle_atoms):
    """Test error handling during atom saving"""
    # Mock a MySQL specific error instead of generic Exception
    mock_db_connection.execute.side_effect = MysqlConnectorError("DB Error")

    code_id = 123
    result = save_atoms_to_db(isabelle_atoms, code_id)
    assert result is False

    # Verify error was logged (optional)
    mock_db_connection.execute.assert_called_once()


def test_atoms_ordering(mock_db_connection, isabelle_atoms):
    """Test that atoms are saved in correct order for dependencies"""
    code_id = 123
    save_atoms_to_db(isabelle_atoms, code_id)

    # Get all atom insertions
    atom_inserts = [
        c
        for c in mock_db_connection.execute.call_args_list
        if "INSERT INTO atoms" in c[0][0]
    ]

    # First atom should be const_def
    first_insert = atom_inserts[0][0][1]  # get first insert's values
    assert "const_def" in first_insert

    # Last atom should be main_theorem
    last_insert = atom_inserts[-1][0][1]  # get last insert's values
    assert "main_theorem" in last_insert


def test_batch_dependency_insertion(mock_db_connection, isabelle_atoms):
    """Test that dependencies are inserted in batches"""
    code_id = 123
    save_atoms_to_db(isabelle_atoms, code_id)

    # Check for executemany calls for dependencies
    executemany_calls = mock_db_connection.executemany.call_args_list
    assert len(executemany_calls) > 0
    assert "INSERT INTO atomsdependencies" in executemany_calls[0][0][0]


def test_skip_existing_atoms(mock_existing_atoms, isabelle_atoms):
    """Test that existing atoms are skipped but used for dependencies"""
    code_id = 123

    # Setup mock to return different results for different queries
    def mock_fetchall_side_effect():
        if not hasattr(mock_fetchall_side_effect, "call_count"):
            mock_fetchall_side_effect.call_count = 0
        mock_fetchall_side_effect.call_count += 1

        # First call: for existing atoms
        if mock_fetchall_side_effect.call_count == 1:
            return [{"identifier": "const_def", "id": 42}]
        # All subsequent calls: for existing dependencies (none)
        return [{"childatom_id": None}]  # Empty result but with correct column name

    mock_existing_atoms.fetchall.side_effect = mock_fetchall_side_effect

    save_atoms_to_db(isabelle_atoms, code_id)

    # Get all atom insertions
    atom_inserts = [
        c
        for c in mock_existing_atoms.execute.call_args_list
        if "INSERT INTO atoms" in c[0][0]
    ]

    # Should only insert 2 atoms (const_lemma and main_theorem)
    # const_def should be skipped as it already exists
    assert len(atom_inserts) == 2
    assert all("const_def" not in str(c) for c in atom_inserts)

    # But const_def's ID should still be used in dependencies
    dep_inserts = [
        c
        for c in mock_existing_atoms.executemany.call_args_list
        if "INSERT INTO atomsdependencies" in c[0][0]
    ]
    assert len(dep_inserts) == 2

    # Verify const_lemma still depends on const_def using its existing ID
    first_dep = dep_inserts[0]
    dep_values = first_dep[0][1]  # Get the values being inserted
    assert len(dep_values) == 1  # One dependency
    assert 42 in dep_values[0]  # Should use existing ID 42


def test_skip_existing_dependencies(mock_existing_atoms, isabelle_atoms):
    """Test that dependency insertions occur when no duplicates exist"""
    code_id = 123

    # Setup fetchall to return different values based on call count.
    def mock_fetchall_side_effect():
        if not hasattr(mock_fetchall_side_effect, "call_count"):
            mock_fetchall_side_effect.call_count = 0
        mock_fetchall_side_effect.call_count += 1
        if mock_fetchall_side_effect.call_count == 1:
            # First call: for existing atoms query; return valid row.
            return [{"identifier": "const_def", "id": 42}]
        else:
            # For dependency queries, return empty list.
            return []

    mock_existing_atoms.fetchall.side_effect = mock_fetchall_side_effect

    save_atoms_to_db(isabelle_atoms, code_id)

    # Collect all dependency insertions (each call's second argument is a list of tuples)
    dep_inserts = [
        call[0][1]
        for call in mock_existing_atoms.executemany.call_args_list
        if "INSERT INTO atomsdependencies" in call[0][0]
    ]
    # Sum the lengths of dependency lists (for both const_lemma and main_theorem)
    total_deps_inserted = sum(len(deps) for deps in dep_inserts)

    # For isabelle_atoms, we have two dependencies:
    #  - const_lemma depends on const_def
    #  - main_theorem depends on const_lemma.
    # So we expect 2 total dependency insertions.
    assert total_deps_inserted == 2


if __name__ == "__main__":
    pytest.main([__file__])
