import logging
import os
import sys
from pprint import pprint
from mysql import connector
from mysql.connector import Error as MysqlConnectorError
from dotenv import load_dotenv
from atomization.dafny.atomizer import atomize_dafny
from atomization.coq.atomizer import atomize_str_vlib as atomize_coq

load_dotenv()
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# read environment variable DB_PASS in
DB_PASSWORD = os.environ.get("DB_PASSWORD", None)
DB_HOST = os.environ.get("DB_HOST", "localhost")

languages = {1: "dafny", 2: "lean", 3: "coq", 4: "isabelle", 5: "metamath"}


class DBConnection:
    def __init__(
        self, host=DB_HOST, user="root", password=DB_PASSWORD, database="verilib"
    ):
        self.config = {
            "host": host,
            "user": user,
            "password": password,
            "database": database,
        }
        self.conn = None

    def __enter__(self):
        try:
            self.conn = connector.connect(**self.config)
            return self.conn
        except MysqlConnectorError as e:
            logger.error(f"Error connecting to MySQL: {e}")
            raise

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.conn and self.conn.is_connected():
            self.conn.close()


def test_connection():
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)

            # Get all table names
            cursor.execute("SHOW TABLES")
            tables = cursor.fetchall()
            print("Database tables:")
            for table in tables:
                print(f"- {list(table.values())[0]}")

            # Sample some data from codes table
            cursor.execute("SELECT id, package_id FROM codes LIMIT 5")
            codes = cursor.fetchall()
            print("\nSample codes entries:")
            for code in codes:
                print(f"ID: {code['id']}, Package ID: {code['package_id']}")

            return True

    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return False


def get_code_entry(code_id: int):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT * FROM codes WHERE id = %s", (code_id,))
            code = cursor.fetchone()
            if code:
                if code["package_id"] is not None:
                    print(f"Note: This code is package {code['package_id']}")
                    return None, code["package_id"]
                if code["text"] is None:
                    print(f"No content found for code ID {code_id}")
                    return None, None
                print(f"Note: This is the content: {code['text']}")
                return code["text"], None
            else:
                print(f"No code found with ID {code_id}")
                return None, None

    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return None, None


def get_code_language_id(code_id: int):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT language_id FROM codes WHERE id = %s", (code_id,))
            code = cursor.fetchone()
            if code:
                return code["language_id"]
            else:
                logger.error(f"No code found with ID {code_id}")
                return None
    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return None


def create_package_entry(code_id: int, code_language_id: int):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT * FROM codes WHERE id = %s", (code_id,))
            original_code = cursor.fetchone()

            if not original_code:
                logger.error(f"No code found with ID {code_id}")
                return None

            description = None
            if original_code.get("summary") and original_code.get("description"):
                description = (
                    f"{original_code['summary']}: {original_code['description']}"
                )
            elif original_code.get("summary"):
                description = original_code["summary"]
            elif original_code.get("description"):
                description = original_code["description"]

            insert_query = """
            INSERT INTO packages 
            (code_id, language_id, description, url, timestamp, name)
            VALUES (%s, %s, %s, %s, NOW(), %s)
            """

            cursor.execute(
                insert_query,
                (
                    code_id,
                    code_language_id,
                    description,
                    original_code.get("url"),
                    original_code.get("filename"),
                ),
            )

            package_id = cursor.lastrowid

            # Update codes table with new package_id
            cursor.execute(
                "UPDATE codes SET package_id = %s WHERE id = %s", (package_id, code_id)
            )

            conn.commit()
            logger.info(f"Created package with ID {package_id}")
            return package_id
    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return None


def create_snippets(package_id: int, code_language_id: int, parsed_chunks: list):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)

            # Map chunk types to type_ids
            type_map = {
                "spec": 1,  # Assuming spec entries with type_id 1
                "code": 2,  # Assuming code entries with type_id 2
                "proof": 3,  # Assuming proofs use type_id 3
                "spec+code": 4,  # For method/function headers use type_id 4
            }

            insert_query = """
            INSERT INTO snippets 
            (package_id, language_id, type_id, text, sortorder, timestamp)
            VALUES (%s, %s, %s, %s, %s, NOW())
            """

            for chunk in parsed_chunks:
                cursor.execute(
                    insert_query,
                    (
                        package_id,
                        code_language_id,
                        type_map[chunk["type"]],
                        chunk["content"],
                        chunk["order"],
                    ),
                )

            conn.commit()
            logger.info(f"Created snippets for package {package_id}")
            return True

    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return False


def delete_package_and_cleanup(package_id: int):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)

            # Get code_id for the package
            cursor.execute("SELECT code_id FROM packages WHERE id = %s", (package_id,))
            package = cursor.fetchone()
            if not package:
                logger.error(f"No package found with ID {package_id}")
                return False

            # Update code.package_id to NULL
            cursor.execute(
                "UPDATE codes SET package_id = NULL WHERE id = %s",
                (package["code_id"],),
            )

            # Delete snippets
            cursor.execute("DELETE FROM snippets WHERE package_id = %s", (package_id,))

            # Delete package
            cursor.execute("DELETE FROM packages WHERE id = %s", (package_id,))

            conn.commit()
            logger.info(
                f"Successfully deleted package {package_id} and related entries"
            )
            return True

    except MysqlConnectorError as e:
        logger.error(f"Database error: {e}")
        return False

def sort_dafny_chunks(result: dict) -> list[dict]:
    """
    Takes a dictionary of categorized chunks and returns a flat list sorted by order
    
    Args:
        result: Dictionary with keys 'code', 'proof', 'spec', 'spec+code', 
               where each value is a list of dicts with 'content' and 'order' keys
    
    Returns:
        List of dictionaries with 'content', 'order', and 'type' keys, sorted by order
    """
    # Create a flat list of all chunks with their types
    all_chunks = []
    
    for chunk_type in ['code', 'proof', 'spec', 'spec+code']:
        for chunk in result.get(chunk_type, []):
            all_chunks.append({
                'content': chunk['content'],
                'order': chunk['order'],
                'type': chunk_type
            })
    
    # Sort by order
    return sorted(all_chunks, key=lambda x: x['order'])

def jsonify_vlib(parsed_chunks: list[dict]) -> dict:
    def jsonify_content(typ: str) -> list:
        return [
            {"content": chunk["content"], "order": chunk["order"]}
            for chunk in parsed_chunks
            if chunk["type"] == typ
        ]

    return {typ: jsonify_content(typ) for typ in ["spec", "code", "proof", "spec+code"]}


def main():
    if len(sys.argv) == 1:
        print(f'Usage: python atomizer.py <code id>')
        print(f'Usage: python atomizer.py delete <package_id>')
        print(f'Usage: python atomizer.py test <filename>')
    elif sys.argv[1] == "test" and len(sys.argv) == 3:
        with open(sys.argv[2], 'r') as f:
            content = f.read()
            parsed_chunks = atomize_dafny(content)
            result = {
                'spec': [{'content': chunk['content'], 'order': chunk['order']} 
                        for chunk in parsed_chunks if chunk['type'] == 'spec'],
                'code': [{'content': chunk['content'], 'order': chunk['order']}
                        for chunk in parsed_chunks if chunk['type'] == 'code'],
                'proof': [{'content': chunk['content'], 'order': chunk['order']}
                        for chunk in parsed_chunks if chunk['type'] == 'proof'],
                'spec+code': [{'content': chunk['content'], 'order': chunk['order']}
                        for chunk in parsed_chunks if chunk['type'] == 'spec+code']
            }
            pprint(result)
            sorted_chunks = sort_dafny_chunks(result)
            for chunk in sorted_chunks:
                print(f"Order {chunk['order']} ({chunk['type']}):")
                print(chunk['content'])
    elif sys.argv[1] == "delete" and len(sys.argv) == 3:
        print(f"Deleting package {sys.argv[2]}")
        # run delete_package_and_cleanup
        package_id = int(sys.argv[2])
        if delete_package_and_cleanup(package_id):
            logger.info(f"Successfully deleted package {package_id}")
    else:
        try:
            code_id = int(sys.argv[1])
            content, package_id = get_code_entry(code_id)

            if content is not None:
                decoded_content = content.decode("utf-8")
                code_language_id = get_code_language_id(code_id)
                if code_language_id == 1:
                    parsed_chunks = atomize_dafny(decoded_content)
                    print(f"Atomizing Dafny code with ID {code_id}")
                    result = jsonify_vlib(parsed_chunks)
                elif code_language_id == 3:
                    parsed_chunks = atomize_coq(decoded_content)
                    print(f"Atomizing Coq code with ID {code_id}")
                    result = jsonify_vlib(parsed_chunks)
                else:
                    print(f"Language not supported yet")
                    sys.exit(1)

                pprint(result)

                # Create package entry
                package_id = create_package_entry(code_id, code_language_id)
                if package_id:
                    logger.info(f"Successfully created package with ID {package_id}")
                    # Create snippets entries
                    if create_snippets(package_id, code_language_id, parsed_chunks):
                        logger.info("Successfully created snippets")
                    else:
                        logger.error("Failed to create snippets")
                else:
                    logger.error("Failed to create package entry")
            else:
                print(f"Package already exists: {package_id}")

        except ValueError:
            print("Please provide either 'test' or a valid integer ID")
