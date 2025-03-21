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


def test_raise_error_existing_atoms(mock_existing_atoms, isabelle_atoms):
    """Test that attempting to save atoms for a code_id that already has atoms
    raises a ValueError."""
    code_id = 123
    # Simulate that an atom exists by returning a non-empty result in the initial query.
    mock_existing_atoms.fetchall.return_value = [{"identifier": "const_def", "id": 42}]
    with pytest.raises(ValueError, match=f"Atoms already exist for code ID {code_id}"):
        save_atoms_to_db(isabelle_atoms, code_id)
