import os
import re
import json
from datetime import datetime

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALL_FILES_PATH = os.path.join(ROOT_DIR, "all_files.txt")
DEPS_PATH = os.path.join(ROOT_DIR, "deps.txt")
OUT_JSON_PATH = os.path.join(ROOT_DIR, "dashboard", "data.json")

# Recursively strip Coq comments (* ... *)
def strip_comments(text):
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if i + 1 < n and text[i] == '(' and text[i+1] == '*':
            depth += 1
            i += 2
        elif i + 1 < n and depth > 0 and text[i] == '*' and text[i+1] == ')':
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)

# Parse dependency graph from deps.txt
def parse_dependencies():
    imports_map = {}
    if not os.path.exists(DEPS_PATH):
        return imports_map
        
    with open(DEPS_PATH, "r", encoding="utf-8") as f:
        for line in f:
            if ":" not in line:
                continue
            lhs, rhs = line.split(":", 1)
            # Check if this line is for a normal target .vo file
            if not any(t.endswith(".vo") for t in lhs.split()):
                continue
                
            tokens = rhs.strip().split()
            if not tokens:
                continue
                
            # Find the source file ending in .v
            src_file = None
            dep_files = []
            for token in tokens:
                token_clean = token.lstrip("./")
                if token_clean.endswith(".v"):
                    src_file = token_clean
                elif token_clean.endswith(".vo"):
                    # Map .vo back to .v path
                    dep_v = token_clean[:-2] + "v"
                    dep_files.append(dep_v)
            
            if src_file:
                imports_map[src_file] = dep_files
                
    return imports_map

def get_group(path):
    parts = path.split('/')
    if len(parts) > 1 and parts[0] == 'theories':
        if parts[1] == 'Main' and len(parts) > 2:
            return f"Main/{parts[2]}"
        if parts[1] == 'Algebraic' and len(parts) > 2 and parts[2] == 'Counter_models' and len(parts) > 3:
            return f"Algebraic/{parts[3]}"
        return parts[1]
    return "Other"

def main():
    if not os.path.exists(ALL_FILES_PATH):
        print(f"Error: {ALL_FILES_PATH} not found.")
        return
        
    with open(ALL_FILES_PATH, "r", encoding="utf-8") as f:
        all_files = [line.strip() for line in f if line.strip()]
        
    imports_map = parse_dependencies()
    
    # Pre-populate files dict
    files_data = {}
    
    decl_pattern = re.compile(
        r'\b(Lemma|Theorem|Definition|Axiom|Parameter|Ltac|Fact|Corollary|Proposition|Remark|Fixpoint|Inductive|Record|Structure)\s+([a-zA-Z0-9_\'\"]+)',
        re.MULTILINE
    )
    
    global_decl_counts = {}
    total_lines = 0
    total_bytes = 0
    
    for rel_path in all_files:
        full_path = os.path.join(ROOT_DIR, rel_path)
        if not os.path.exists(full_path):
            print(f"Warning: File {rel_path} does not exist. Skipping.")
            continue
            
        # Get file stats
        size_bytes = os.path.getsize(full_path)
        total_bytes += size_bytes
        
        with open(full_path, "r", encoding="utf-8", errors="ignore") as f:
            content = f.read()
            
        lines = content.splitlines()
        lines_count = len(lines)
        total_lines += lines_count
        
        # Strip comments to avoid matching inside comments
        clean_content = strip_comments(content)
        
        # Find declarations
        decls = []
        for match in decl_pattern.finditer(clean_content):
            decl_type = match.group(1)
            decl_name = match.group(2)
            decls.append({
                "type": decl_type,
                "name": decl_name
            })
            global_decl_counts[decl_type] = global_decl_counts.get(decl_type, 0) + 1
            
        # Imports for this file
        imports = imports_map.get(rel_path, [])
        # Only keep imports that are in our all_files list (internal to GeoCoq)
        imports = [imp for imp in imports if imp in all_files]
        
        files_data[rel_path] = {
            "path": rel_path,
            "group": get_group(rel_path),
            "size_bytes": size_bytes,
            "lines_count": lines_count,
            "declarations": decls,
            "imports": imports,
            "dependents": [] # Will compute below
        }
        
    # Compute dependents
    for file_path, data in files_data.items():
        for imp in data["imports"]:
            if imp in files_data:
                files_data[imp]["dependents"].append(file_path)
                
    # Sort dependents and imports for consistency
    for data in files_data.values():
        data["imports"].sort()
        data["dependents"].sort()
        
    # Group stats
    group_counts = {}
    for data in files_data.values():
        group_counts[data["group"]] = group_counts.get(data["group"], 0) + 1
        
    output_data = {
        "generated_at": datetime.now().isoformat(),
        "stats": {
            "total_files": len(files_data),
            "total_lines": total_lines,
            "total_bytes": total_bytes,
            "declarations": global_decl_counts,
            "group_counts": group_counts
        },
        "files": files_data
    }
    
    os.makedirs(os.path.dirname(OUT_JSON_PATH), exist_ok=True)
    with open(OUT_JSON_PATH, "w", encoding="utf-8") as f:
        json.dump(output_data, f, indent=2)
        
    print(f"Data generation complete! Wrote metadata for {len(files_data)} files to {OUT_JSON_PATH}")

if __name__ == "__main__":
    main()
