import pytest
from mysql.connector import Error as MysqlConnectorError
from atomization.atomizer import delete_all_atoms


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


def test_delete_all_atoms_success(mock_db_connection):
    """Test that delete_all_atoms returns True and executes the correct queries."""
    result = delete_all_atoms()
    calls = [
        call[0][0]
        for call in mock_db_connection.cursor.return_value.execute.call_args_list
    ]
    # Both DELETE queries should be issued.
    assert any("DELETE FROM atomsdependencies" in query for query in calls)
    assert any("DELETE FROM atoms" in query for query in calls)
    mock_db_connection.commit.assert_called_once()
    assert result is True


def test_delete_all_atoms_failure(mock_db_connection):
    """Test that delete_all_atoms returns False when a database error occurs."""
    mock_db_connection.cursor.return_value.execute.side_effect = MysqlConnectorError(
        "DB error"
    )
    result = delete_all_atoms()
    assert result is False