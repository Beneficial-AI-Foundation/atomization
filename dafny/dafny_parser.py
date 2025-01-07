# dafny_parser.py
import sys
import json
from typing import List, Dict

def parse_dafny(content: str) -> List[Dict[str, str]]:
    lines = content.split('\n')
    chunks = []
    current_chunk = ''
    brace_count = 0
    chunk_order = 0
    i = 0
    
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
            
        # Ghost functions/predicates or lemmas
        if line.startswith(('ghost', 'lemma')):
            if current_chunk:
                chunks.append({
                    'content': current_chunk.strip(),
                    'type': 'code' if 'method' in current_chunk else 'spec',
                    'order': chunk_order
                })
                chunk_order += 1
                current_chunk = ''
                
            current_chunk = line
            brace_count = line.count('{')
            i += 1
            
            while i < len(lines) and (brace_count > 0 or '{' not in current_chunk):
                line = lines[i].strip()
                if line:
                    current_chunk += ' ' + line
                    brace_count += line.count('{')
                    brace_count -= line.count('}')
                i += 1
                
            chunks.append({
                'content': current_chunk.strip(),
                'type': 'spec' if line.startswith('ghost') else 'proof',
                'order': chunk_order
            })
            chunk_order += 1
            current_chunk = ''
            continue

        # Methods
        if line.startswith('method'):
            current_chunk = line
            i += 1
            
            # Collect method signature and specs
            while i < len(lines) and '{' not in line:
                line = lines[i].strip()
                if line:
                    current_chunk += ' ' + line
                i += 1
            
            chunks.append({
                'content': current_chunk.strip(),
                'type': 'spec',
                'order': chunk_order
            })
            chunk_order += 1
            
            if not line:
                continue
                
            # Start collecting method body
            current_chunk = line
            brace_count = 1
            
            while i < len(lines) and brace_count > 0:
                line = lines[i].strip()
                if line:
                    if 'invariant' in line or 'decreases' in line:
                        if current_chunk.strip():
                            chunks.append({
                                'content': current_chunk.strip(),
                                'type': 'code',
                                'order': chunk_order
                            })
                            chunk_order += 1
                        current_chunk = line
                        while i + 1 < len(lines) and ('invariant' in lines[i+1].strip() or 'decreases' in lines[i+1].strip()):
                            i += 1
                            current_chunk += ' ' + lines[i].strip()
                        chunks.append({
                            'content': current_chunk.strip(),
                            'type': 'proof',
                            'order': chunk_order
                        })
                        chunk_order += 1
                        current_chunk = ''
                    else:
                        current_chunk += ' ' + line
                        brace_count += line.count('{')
                        brace_count -= line.count('}')
                i += 1
            
            if current_chunk.strip():
                chunks.append({
                    'content': current_chunk.strip(),
                    'type': 'code',
                    'order': chunk_order
                })
                chunk_order += 1
            current_chunk = ''
            continue
            
        i += 1
    
    if current_chunk:
        chunks.append({
            'content': current_chunk.strip(),
            'type': 'code' if 'method' in current_chunk else 'spec',
            'order': chunk_order
        })
    
    return chunks
