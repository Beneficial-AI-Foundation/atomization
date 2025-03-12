import logging
import os
import sys
import argparse
from pprint import pprint
from mysql import connector
from mysql.connector import Error as MysqlConnectorError
from dotenv import load_dotenv
from atomization.dafny.atomizer import atomize_dafny
from atomization.coq.atomizer import atomize_str_vlib as atomize_coq
from bidict import bidict
from atomization.lean.atomizer import atomize_lean
from pathlib import Path
from atomization.coq.atomizer import CoqAtomizer
from atomization.lean.visualizer import visualize_lean_file


load_dotenv()
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# read environment variable DB_PASS in
DB_PASSWORD = os.environ.get("DB_PASSWORD", None)
DB_HOST = os.environ.get("DB_HOST", "localhost")

# This is a bidirectional map between language names and their IDs in the database because they're supposed to be unique.
LANG_MAP: bidict[str, int] = bidict({
    "dafny": 1,
    "lean": 2,
    "coq": 3,
    "isabelle": 4,
    "metamath": 5,
})


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

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        if self.conn and self.conn.is_connected():
            self.conn.close()


def test_connection() -> bool:
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

    for chunk_type in ["code", "proof", "spec", "spec+code"]:
        for chunk in result.get(chunk_type, []):
            all_chunks.append({
                "content": chunk["content"],
                "order": chunk["order"],
                "type": chunk_type,
            })

    # Sort by order
    return sorted(all_chunks, key=lambda x: x["order"])


def jsonify_vlib(parsed_chunks: list[dict]) -> dict:
    def jsonify_content(typ: str) -> list:
        return [
            {"content": chunk["content"], "order": chunk["order"]}
            for chunk in parsed_chunks
            if chunk["type"] == typ
        ]

    return {typ: jsonify_content(typ) for typ in ["spec", "code", "proof", "spec+code"]}


def parse_cli_arguments(
    args: list[str] | None = None,
) -> tuple[argparse.Namespace, argparse.ArgumentParser]:
    """Set up and parse CLI arguments, returning both the parsed args and the parser."""
    parser = argparse.ArgumentParser(
        description="Atomize code from the database into snippets"
    )
    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Test command
    subparsers.add_parser("test", help="Test database connection")

    # Delete command
    delete_parser = subparsers.add_parser("delete", help="Delete a package and cleanup")
    delete_parser.add_argument("package_id", type=int, help="Package ID to delete")

    # Atomize command
    atomize_parser = subparsers.add_parser("atomize", help="Atomize code with given ID")
    atomize_parser.add_argument("code_id", type=int, help="Code ID to atomize")

    # Visualize command
    visualize_parser = subparsers.add_parser(
        "visualize", help="Visualize Lean code and generate dependency graphs"
    )
    visualize_parser.add_argument("file_path", type=str, help="Path to Lean file")
    visualize_parser.add_argument(
        "--output-dir",
        type=str,
        help="Output directory for visualization files",
        default=None,
    )

    return parser.parse_args(args), parser


def execute_test_command() -> int:
    """Execute the test command by verifying the database connection."""
    return 0 if test_connection() else 1


def execute_delete_command(package_id: int) -> int:
    """Execute the delete command by handling related DB cleanup."""
    print(f"Deleting package {package_id}")
    if delete_package_and_cleanup(package_id):
        logger.info(f"Successfully deleted package {package_id}")
        return 0
    return 1


def save_lean_atoms_to_db(parsed_chunks, code_id):
    """
    Save atomized Lean code chunks to the database (atoms and atomsdependencies tables).
    
    Args:
        parsed_chunks: List of Schema objects representing atomized Lean code
        code_id: Code ID from the codes table
    
    Returns:
        bool: True if successful, False otherwise
    """
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)
            
            # Dictionary to track atom ids by identifier
            atom_id_map = {}
            
            # Function to recursively process atoms and their dependencies
            def process_atom(atom, parent_id=None):
                # Skip if we've already processed this atom
                if atom['identifier'] in atom_id_map:
                    # If we have a parent, add the dependency relationship
                    if parent_id is not None:
                        cursor.execute(
                            "INSERT INTO atomsdependencies (parentatom_id, childatom_id) VALUES (%s, %s)",
                            (parent_id, atom_id_map[atom['identifier']])
                        )
                    return atom_id_map[atom['identifier']]
                
                # Insert the atom into the atoms table
                # Convert the body to bytes if it's not already
                body_blob = atom['body'].encode('utf-8') if isinstance(atom['body'], str) else atom['body']
                cursor.execute(
                    "INSERT INTO atoms (text, identifier, statement_type, code_id) VALUES (%s, %s, %s, %s)",
                    (body_blob, atom['identifier'], atom['type'], code_id)
                )
                atom_id = cursor.lastrowid
                atom_id_map[atom['identifier']] = atom_id
                
                # If there's a parent, add the dependency relationship
                if parent_id is not None:
                    cursor.execute(
                        "INSERT INTO atomsdependencies (parentatom_id, childatom_id) VALUES (%s, %s)",
                        (parent_id, atom_id)
                    )
                
                # Process dependencies recursively
                for dep in atom.get('deps', []):
                    process_atom(dep, atom_id)
                
                return atom_id
            
            # Process all top-level atoms
            for atom in parsed_chunks:
                process_atom(atom)
            
            conn.commit()
            logger.info(f"Successfully saved {len(atom_id_map)} atoms to database")
            return True
            
    except MysqlConnectorError as e:
        logger.error(f"Database error while saving atoms: {e}")
        return False


def execute_atomize_command(code_id: int, parser: argparse.ArgumentParser) -> int:
    """
    Execute the atomize command:
     - Isolate DB operations (fetching and creating entries),
     - Handle CLI I/O (printing and error reporting),
     - Run the core business logic for atomization.
    """
    try:
        # DB Operation: Retrieve code entry from database
        content, existing_pkg = get_code_entry(code_id)
        if content is None:
            print(f"Package already exists: {existing_pkg}")
            return 1

        # CLI I/O: Decode the retrieved content
        decoded_content: str = content.decode("utf-8")

        # Business Logic: Determine atomization method based on language
        code_language_id: int = get_code_language_id(code_id)
        if code_language_id == LANG_MAP["dafny"]:
            parsed_chunks = atomize_dafny(decoded_content)
            print(f"Atomizing Dafny code with ID {code_id}")
        elif code_language_id == LANG_MAP["lean"]:
            # For Lean, we need a different approach
            print(f"Atomizing Lean code with ID {code_id}")
            parsed_chunks = atomize_lean(decoded_content, code_id)
            
            # Save Lean atoms to database (atoms and atomsdependencies tables)
            if parsed_chunks:
                if save_lean_atoms_to_db(parsed_chunks, code_id):
                    logger.info(f"Successfully saved Lean atoms for code {code_id}")
                else:
                    logger.error(f"Failed to save Lean atoms for code {code_id}")
                    return 1
            
            # Convert Lean atoms to snippets format for consistency with other languages
            # Note: This is a simplified conversion for display and snippet creation
            snippet_chunks = []
            for atom in parsed_chunks:
                snippet_chunks.append({
                    "content": atom["body"],
                    "order": len(snippet_chunks) + 1,  # Simple sequential ordering
                    "type": atom["type"]
                })
            parsed_chunks = snippet_chunks
            
        elif code_language_id == LANG_MAP["coq"]:
            parsed_chunks = atomize_coq(decoded_content)
            print(f"Atomizing Coq code with ID {code_id}")
        else:
            print("Language not supported yet")
            return 1
            
        if parsed_chunks:
            print(f"Parsed chunks: {parsed_chunks}")
            
        # Business Logic: Format and display the atomized result
        result = jsonify_vlib(parsed_chunks)
        pprint(result)

        # DB Operation: Create package and snippet records
        new_pkg_id = create_package_entry(code_id, code_language_id)
        if new_pkg_id:
            logger.info(f"Successfully created package with ID {new_pkg_id}")
            if create_snippets(new_pkg_id, code_language_id, parsed_chunks):
                logger.info("Successfully created snippets")
            else:
                logger.error("Failed to create snippets")
                return 1
        else:
            logger.error("Failed to create package entry")
            return 1

        return 0

    except ValueError as e:
        parser.error(
            f"Invalid input: {e}. Please provide one of: `test`, `delete <package_id>`, or `atomize <code_id>`"
        )


def execute_visualize_command(file_path: str, output_dir: str | None = None) -> int:
    """
    Execute the visualize command:
     - Takes a Lean file and generates visualization files (JSON, DOT, SVG, PNG)
     - Handle CLI I/O (printing and error reporting)
    """
    try:
        file_path = Path(file_path)
        output_dir = Path(output_dir) if output_dir else None

        if not file_path.exists():
            print(f"Error: File not found - {file_path}")
            return 1

        if file_path.suffix != ".lean":
            print(
                f"Error: Not a Lean file - {file_path}. Only Lean files are supported."
            )
            return 1

        print(f"Visualizing Lean file: {file_path}")
        visualize_lean_file(file_path, output_dir)
        return 0

    except Exception as e:
        print(f"Error visualizing file: {e}")
        return 1


def run_atomizer(args: list[str] | None = None) -> int:
    """Parse CLI arguments and dispatch to the appropriate command handler; returns exit code."""
    parsed_args, parser = parse_cli_arguments(args)

    if parsed_args.command == "test" or not parsed_args.command:
        return execute_test_command()
    elif parsed_args.command == "delete":
        return execute_delete_command(parsed_args.package_id)
    elif parsed_args.command == "atomize":
        return execute_atomize_command(parsed_args.code_id, parser)
    elif parsed_args.command == "visualize":
        return execute_visualize_command(parsed_args.file_path, parsed_args.output_dir)
    else:
        parser.print_help()
        return 1


def main() -> None:
    exit_code = run_atomizer()
    sys.exit(exit_code)


def dry_run() -> None:
    """Dry run the atomizer on a given Coq file."""

    def parser() -> argparse.ArgumentParser:
        parser = argparse.ArgumentParser()
        parser.add_argument("name", type=str)
        return parser

    coq_fixtures = Path("examples/coq")
    args = parser().parse_args()
    file = coq_fixtures / f"{args.name}.v"
    atomizer = CoqAtomizer(file)
    json_content = atomizer.jsonify_vlib()
    print(json_content)


if __name__ == "__main__":
    main()
