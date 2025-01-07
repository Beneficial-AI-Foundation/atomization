import mysql.connector
from mysql.connector import Error
import logging
import os
import sys
from pprint import pprint

from dafny.dafny_parser import parse_dafny


logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# read environment variable DB_PASS in
db_pass = os.environ.get("DB_PASS", None)

class DBConnection:
    def __init__(self, host="localhost", user="root", password=db_pass, database="verilib"):
        self.config = {
            "host": host,
            "user": user,
            "password": password,
            "database": database
        }
        self.conn = None
        
    def __enter__(self):
        try:
            self.conn = mysql.connector.connect(**self.config)
            return self.conn
        except Error as e:
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
            
    except Error as e:
        logger.error(f"Database error: {e}")
        return False

def get_code_entry(code_id: int):
    try:
        with DBConnection() as conn:
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT * FROM codes WHERE id = %s", (code_id,))
            code = cursor.fetchone()
            if code:
                if code['package_id'] is not None:
                    print(f"Note: This code is package {code['package_id']}")
                if code['text'] is None:
                    print(f"No content found for code ID {code_id}")
                    return None
                print(f"Note: This is the content: {code['text']}")
                return code['text']
            else:
                print(f"No code found with ID {code_id}")
                return None
            
    except Error as e:
        logger.error(f"Database error: {e}")
        return None

def atomize_dafny(content: str) -> dict:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:

        parsed_dafny = parse_dafny(content)
        return parsed_dafny
        
       
    except Exception as e:
        print(f"Debug - Exception details: {type(e).__name__}: {str(e)}")
        raise Exception(f"Error analyzing {content}: {str(e)}")

if __name__ == "__main__":
    if len(sys.argv) == 1:
        get_code_entry(1)
    elif sys.argv[1] == "test":
        test_connection()
    else:
        try:
            code_id = int(sys.argv[1])
            content = get_code_entry(code_id)

            if content is not None:
                decoded_content = content.decode('utf-8')
                parsed_chunks = atomize_dafny(decoded_content)
        
                result = {
                    'spec': [{'content': chunk['content'], 'order': chunk['order']} 
                            for chunk in parsed_chunks if chunk['type'] == 'spec'],
                    'code': [{'content': chunk['content'], 'order': chunk['order']}
                            for chunk in parsed_chunks if chunk['type'] == 'code'],
                    'proof': [{'content': chunk['content'], 'order': chunk['order']}
                            for chunk in parsed_chunks if chunk['type'] == 'proof']
                }
                pprint(result)
        except ValueError:
            print("Please provide either 'test' or a valid integer ID")