import pytest
from mysql.connector import Error as MysqlConnectorError
from atomization.atomizer import delete_code_atoms


# Updated fixture: return the connection mock instead of the cursor.
@pytest.fixture
def mock_db_connection(mocker):
    """Mock database connection and cursor for deletion tests."""
    mock_cursor = mocker.MagicMock()
    mock_conn = mocker.MagicMock()
    mock_conn.__enter__.return_value = mock_conn
    mock_conn.cursor.return_value = mock_cursor
    mocker.patch("atomization.atomizer.DBConnection", return_value=mock_conn)
    return mock_conn


def test_delete_code_atoms_success_when_atoms_exist(mock_db_connection):
    """Test that delete_code_atoms returns (True, True) when atoms exist and are deleted."""
    # Simulate that atoms exist:
    mock_cursor = mock_db_connection.cursor.return_value
    mock_cursor.fetchone.return_value = {"1": 1}  # any non-None value
    # And simulate a list of atom ids:
    mock_cursor.fetchall.side_effect = [
        [{"id": 10}, {"id": 20}],  # for SELECT id FROM atoms
        []  # for SELECT DISTINCT childatom_id (if needed afterwards)
    ]
    result = delete_code_atoms(1)
    # Check that DELETE queries were issued:
    calls = [call[0][0] for call in mock_cursor.execute.call_args_list]
    assert any("DELETE FROM atomsdependencies" in query for query in calls)
    assert any("DELETE FROM atoms WHERE code_id = %s" in query for query in calls)
    mock_db_connection.commit.assert_called_once()
    assert result == (True, True)


def test_delete_code_atoms_no_atoms(mock_db_connection):
    """Test that delete_code_atoms returns (True, False) when no atoms exist."""
    # Simulate no atoms: cursor.fetchone returns None
    mock_db_connection.cursor.return_value.execute.side_effect = None
    mock_db_connection.cursor.return_value.fetchone.return_value = None
    result = delete_code_atoms(1)
    # Ensure proper logging would have happened and no DELETE is attempted:
    assert result == (True, False)


def test_delete_code_atoms_failure(mock_db_connection):
    """Test that delete_code_atoms returns (False, False) when a database error occurs."""
    mock_db_connection.cursor.return_value.execute.side_effect = MysqlConnectorError("DB error")
    result = delete_code_atoms(1)
    assert result == (False, False)