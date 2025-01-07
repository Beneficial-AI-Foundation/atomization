# dafny_atomize.py
import sys
import json
from dataclasses import asdict
from get_code import get_code
from get_specs import get_specs
from get_proofs import get_proofs, InvariantGroup
from dafny_parser import parse_dafny
from dafny_utils import SourceLocation

# def format_code_segment(source_loc: SourceLocation) -> dict:
#     """Format a source location into a dictionary with location and content."""
#     formatted = {
#         'location': {
#             'filename': source_loc.filename,
#             'start_line': source_loc.start_line,
#             'start_col': source_loc.start_col,
#             'end_line': source_loc.end_line,
#             'end_col': source_loc.end_col
#         },
#         'content': source_loc.content,
#         'parent': source_loc.parent,
#         'context_content': source_loc.context_content
#     }
    
#     # Add context if it exists
#     if hasattr(source_loc, 'context') and source_loc.context is not None:
#         formatted['context'] = source_loc.context

#     # Add context_content if it exists
#     if hasattr(source_loc, 'context_content') and source_loc.context_content is not None:
#         formatted['context_content'] = source_loc.context_content
    
#     return formatted

def atomize_dafny(content: str) -> dict:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:

        parsed_dafny = parse_dafny(content)
        return parsed_dafny
        
       
    except Exception as e:
        print(f"Debug - Exception details: {type(e).__name__}: {str(e)}")
        raise Exception(f"Error analyzing {content}: {str(e)}")

def main():
    try:
        content = """
ghost function fibonacci(n: int): int
   requires n >= 0
   decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fibonacci(n-1) + fibonacci(n-2)
}



method fib_method(n: int) returns (result: int)
   requires n >= 0
   ensures result == fibonacci(n)
{
  var i: int := 0;
  var a: int := 0;
  var b: int := 1;
  while i < n
   invariant 0 <= a
   invariant 0 <= i <= n
   invariant a == fibonacci(i)
   invariant b == fibonacci(i + 1)
   invariant 0 <= b
   decreases n - i
  {
    var c := a + b;
    a := b;
    b := c;
    i := i + 1;
  }
  result := a;
}



ghost function FibNonNegative(n: int): bool
{
  forall k :: k >= 0 ==> fibonacci(k) >= 0
}



ghost predicate IsFibonacci(x: int)
{
  exists n :: n >= 0 && fibonacci(n) == x
}

lemma FibIsNonNegative(n: int)
   requires n >= 0
   ensures fibonacci(n) >= 0
{
  if n <= 1 {

  } else {

    FibIsNonNegative(n-1);
    FibIsNonNegative(n-2);

  }
}
"""
        parsed_chunks = atomize_dafny(content)
        
        result = {
            'spec': [{'content': chunk['content'], 'order': chunk['order']} 
                    for chunk in parsed_chunks if chunk['type'] == 'spec'],
            'code': [{'content': chunk['content'], 'order': chunk['order']}
                    for chunk in parsed_chunks if chunk['type'] == 'code'],
            'proof': [{'content': chunk['content'], 'order': chunk['order']}
                    for chunk in parsed_chunks if chunk['type'] == 'proof']
        }
        print(result)
        return result
    except Exception as e:
        raise Exception(f"Error analyzing Dafny content: {str(e)}")

if __name__ == "__main__":
    main()