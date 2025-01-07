import sys
import json
from typing import List, Dict

def collect_until_closing_brace(lines: List[str], start_idx: int) -> tuple[str, int]:
    brace_count = 0
    chunk = []
    i = start_idx
    
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
            
        chunk.append(line)
        brace_count += line.count('{')
        brace_count -= line.count('}')
        
        if brace_count == 0 and '{' in ''.join(chunk):
            return ' '.join(chunk), i + 1
        i += 1
    return ' '.join(chunk), i

def parse_dafny(content: str) -> List[Dict[str, str]]:
    lines = content.split('\n')
    chunks = []
    chunk_order = 0
    i = 0
    
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue

        if line.startswith(('ghost', 'lemma')):
            chunk, i = collect_until_closing_brace(lines, i)
            chunks.append({
                'content': chunk,
                'type': 'proof' if line.startswith('lemma') else 'spec',
                'order': chunk_order
            })
            chunk_order += 1
            continue

        if line.startswith('method'):
            # Collect method signature and specs
            spec = []
            while i < len(lines):
                line = lines[i].strip()
                if not line:
                    i += 1
                    continue
                if '{' in line:
                    spec.append(line[:line.index('{')])
                    break
                spec.append(line)
                i += 1
                
            chunks.append({
                'content': ' '.join(spec),
                'type': 'spec',
                'order': chunk_order
            })
            chunk_order += 1
            
            if not line or '{' not in line:
                continue
                
            # Process method body
            current_chunk = line[line.index('{'):]
            brace_count = current_chunk.count('{')
            method_chunks = []
            
            while i < len(lines) and brace_count > 0:
                i += 1
                if i >= len(lines):
                    break
                    
                line = lines[i].strip()
                if not line:
                    continue
                    
                if 'invariant' in line or 'decreases' in line:
                    if current_chunk.strip():
                        method_chunks.append(('code', current_chunk.strip()))
                    
                    proof_lines = [line]
                    while i + 1 < len(lines):
                        next_line = lines[i + 1].strip()
                        if not ('invariant' in next_line or 'decreases' in next_line):
                            break
                        proof_lines.append(next_line)
                        i += 1
                    
                    method_chunks.append(('proof', ' '.join(proof_lines)))
                    current_chunk = ''
                    continue
                
                current_chunk += ' ' + line
                brace_count += line.count('{')
                brace_count -= line.count('}')
                
                if brace_count == 0:
                    if current_chunk.strip():
                        method_chunks.append(('code', current_chunk.strip()))
            
            for chunk_type, chunk_content in method_chunks:
                chunks.append({
                    'content': chunk_content,
                    'type': chunk_type,
                    'order': chunk_order
                })
                chunk_order += 1
            continue
            
        i += 1
        
    return chunks