import pytest
from unittest.mock import patch, MagicMock
import os
from atomization.atomizer import (
    DBConnection,
    get_code_entry,
    create_package_entry,
    create_snippets,
    delete_package_and_cleanup,
)


@pytest.fixture
def mock_db_config():
    """Set up environment variables for testing."""
    os.environ["DB_PASSWORD"] = "test_password"
    os.environ["DB_HOST"] = "test_host"


@pytest.fixture
def mock_code_entry():
    """Common mock data for tests."""
    return {
        "id": 1,
        "package_id": None,
        "text": b"test code content",
        "language_id": 1,
        "summary": "Test summary",
        "description": "Test description",
        "filename": "test.dfy",
        "url": "http://test.com",
    }


@pytest.fixture
def mock_cursor():
    """Create a mock cursor."""
    return MagicMock()


@pytest.fixture
def mock_conn(mock_cursor):
    """Create a mock connection with the mock cursor."""
    conn = MagicMock()
    conn.cursor.return_value = mock_cursor
    return conn


@patch("mysql.connector.connect")
def test_db_connection(mock_connect, mock_db_config):
    """Test database connection context manager."""
    mock_conn = MagicMock()
    mock_connect.return_value = mock_conn

    with DBConnection() as conn:
        assert conn == mock_conn

    mock_conn.close.assert_called_once()


@patch("mysql.connector.connect")
def test_get_code_entry(
    mock_connect, mock_db_config, mock_code_entry, mock_cursor, mock_conn
):
    """Test code entry retrieval."""
    mock_connect.return_value = mock_conn
    mock_cursor.fetchone.return_value = mock_code_entry

    # Test successful code retrieval
    content, package_id = get_code_entry(1)
    assert content == b"test code content"
    assert package_id is None

    # Test code with package_id
    mock_cursor.fetchone.return_value = {**mock_code_entry, "package_id": 42}
    content, package_id = get_code_entry(1)
    assert content is None
    assert package_id == 42


@patch("mysql.connector.connect")
def test_create_package_entry(
    mock_connect, mock_db_config, mock_code_entry, mock_cursor, mock_conn
):
    """Test package creation."""
    mock_connect.return_value = mock_conn
    mock_cursor.fetchone.return_value = mock_code_entry
    mock_cursor.lastrowid = 42

    package_id = create_package_entry(1, 1)
    assert package_id == 42

    # Verify all three database calls were made
    assert mock_cursor.execute.call_count == 3

    # Get all the calls made to execute
    calls = mock_cursor.execute.call_args_list

    # Verify SELECT query
    select_call = calls[0]
    assert "SELECT * FROM codes WHERE id = %s" in select_call[0][0]
    assert select_call[0][1] == (1,)

    # Verify INSERT query
    insert_call = calls[1]
    assert "INSERT INTO packages" in insert_call[0][0]
    assert "VALUES" in insert_call[0][0]
    assert insert_call[0][1][0] == 1  # code_id
    assert insert_call[0][1][1] == 1  # language_id
    assert "Test summary: Test description" in insert_call[0][1][2]  # description

    # Verify UPDATE query
    update_call = calls[2]
    assert "UPDATE codes SET package_id = %s WHERE id = %s" in update_call[0][0]
    assert update_call[0][1] == (42, 1)  # package_id and code_id

    mock_conn.commit.assert_called_once()


@patch("mysql.connector.connect")
def test_create_snippets(mock_connect, mock_db_config, mock_cursor, mock_conn):
    """Test snippet creation."""
    mock_connect.return_value = mock_conn

    test_chunks = [
        {"type": "spec", "content": "test spec", "order": 1},
        {"type": "code", "content": "test code", "order": 2},
        {"type": "proof", "content": "test proof", "order": 3},
    ]

    result = create_snippets(42, 1, test_chunks)
    assert result is True

    assert mock_cursor.execute.call_count == len(test_chunks)
    mock_conn.commit.assert_called_once()


@patch("mysql.connector.connect")
def test_delete_package_and_cleanup(
    mock_connect, mock_db_config, mock_cursor, mock_conn
):
    """Test package deletion and cleanup."""
    mock_connect.return_value = mock_conn
    mock_cursor.fetchone.return_value = {"code_id": 1}

    result = delete_package_and_cleanup(42)
    assert result is True

    assert mock_cursor.execute.call_count == 4
    mock_conn.commit.assert_called_once()


def test_db_connection_error(mock_db_config):
    """Test database connection error handling."""
    with patch("mysql.connector.connect", side_effect=Exception("Connection failed")):
        with pytest.raises(Exception):
            with DBConnection():
                pass


@pytest.mark.parametrize(
    "code_id,expected",
    [(1, (b"test code content", None)), (2, (None, 42)), (3, (None, None))],
)
def test_get_code_entry_parametrized(code_id, expected, mock_db_config):
    """Test code entry retrieval with different scenarios."""
    mock_results = {
        1: {"id": 1, "package_id": None, "text": b"test code content"},
        2: {"id": 2, "package_id": 42, "text": b"content"},
        3: None,
    }

    with patch("mysql.connector.connect") as mock_connect:
        mock_cursor = MagicMock()
        mock_cursor.fetchone.return_value = mock_results[code_id]
        mock_conn = MagicMock()
        mock_conn.cursor.return_value = mock_cursor
        mock_connect.return_value = mock_conn

        result = get_code_entry(code_id)
        assert result == expected
