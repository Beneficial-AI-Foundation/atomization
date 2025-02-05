from atomization.atomizer import (
    get_code_entry, 
    get_code_language_id, 
    create_package_entry,
    create_snippets,
    delete_package_and_cleanup
)

def test_get_code_entry(mocker):
    # Create a mock result that matches SQLAlchemy's mappings result
    mock_result = {
        "text": b'test content',
        "package_id": None
    }
    
    mock_session = mocker.Mock()
    mock_execute = mocker.Mock()
    mock_mappings = mocker.Mock()
    mock_first = mocker.Mock(return_value=mock_result)
    
    # Set up the chain
    mock_mappings.first = mock_first
    mock_execute.mappings = mocker.Mock(return_value=mock_mappings)
    mock_session.execute = mocker.Mock(return_value=mock_execute)
    
    mock_db_context = mocker.patch('atomization.atomizer.DBConnection')
    mock_db_context().__enter__.return_value = mock_session

    content, package_id = get_code_entry(1)
    assert content == b'test content'
    assert package_id is None

def test_get_code_language_id(mocker):
    mock_result = {"language_id": 3}  # 3 for Coq
    
    mock_session = mocker.Mock()
    mock_execute = mocker.Mock()
    mock_fetchone = mocker.Mock(return_value=mock_result)
    
    mock_execute.fetchone = mock_fetchone
    mock_session.execute = mocker.Mock(return_value=mock_execute)
    
    mock_db_context = mocker.patch('atomization.atomizer.DBConnection')
    mock_db_context().__enter__.return_value = mock_session

    language_id = get_code_language_id(1)
    assert language_id == 3

def test_create_package_entry(mocker):
    mock_code_result = {
        "summary": "Test summary",
        "description": "Test description",
        "url": "http://test.com",
        "filename": "test.v"
    }
    
    mock_session = mocker.Mock()
    mock_execute = mocker.Mock()
    mock_mappings = mocker.Mock()
    mock_first = mocker.Mock(return_value=mock_code_result)
    
    # Mock the insert result
    mock_insert_result = mocker.Mock()
    mock_insert_result.lastrowid = 42
    
    # Set up the chain for the first query
    mock_mappings.first = mock_first
    mock_execute.mappings = mocker.Mock(return_value=mock_mappings)
    
    # Mock session to handle both select and insert
    mock_session.execute = mocker.Mock(side_effect=[
        mock_execute,  # First call returns select result
        mock_insert_result,  # Second call returns insert result
        mocker.Mock(),  # Third call for update
    ])
    mock_session.commit = mocker.Mock()
    
    mock_db_context = mocker.patch('atomization.atomizer.DBConnection')
    mock_db_context().__enter__.return_value = mock_session

    package_id = create_package_entry(1, 3)  # code_id=1, language_id=3
    assert package_id == 42

def test_create_snippets(mocker):
    parsed_chunks = [
        {"content": "test spec", "type": "spec", "order": 1},
        {"content": "test code", "type": "code", "order": 2},
    ]
    
    mock_session = mocker.Mock()
    mock_execute = mocker.Mock()
    mock_fetchall = mocker.Mock(return_value=[])  # No existing snippets
    
    mock_execute.fetchall = mock_fetchall
    mock_session.execute = mocker.Mock(return_value=mock_execute)
    mock_session.commit = mocker.Mock()
    
    mock_db_context = mocker.patch('atomization.atomizer.DBConnection')
    mock_db_context().__enter__.return_value = mock_session

    result = create_snippets(42, 3, parsed_chunks)  # package_id=42, language_id=3
    assert result is True

def test_delete_package_and_cleanup(mocker):
    mock_package = {"code_id": 1}
    
    mock_session = mocker.Mock()
    mock_execute = mocker.Mock()
    mock_fetchone = mocker.Mock(return_value=mock_package)
    
    mock_execute.fetchone = mock_fetchone
    mock_session.execute = mocker.Mock(return_value=mock_execute)
    mock_session.commit = mocker.Mock()
    
    mock_db_context = mocker.patch('atomization.atomizer.DBConnection')
    mock_db_context().__enter__.return_value = mock_session

    result = delete_package_and_cleanup(42)  # package_id=42
    assert result is True
    
    # Verify all necessary deletes/updates were called
    assert mock_session.execute.call_count == 4  # select + update codes + delete snippets + delete package 