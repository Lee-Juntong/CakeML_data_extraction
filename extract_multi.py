import os
import re
import sys
import json
from typing import List, Dict

THEOREM_START_RE = re.compile(
    r"^\s*Theorem\s+(?P<name>[A-Za-z0-9_']+)(?:\[[^\]]+\])?\s*:\s*(?P<after>.*)$"
)
PROOF_LINE_RE = re.compile(r"^\s*Proof\b")

DEF_START_RE = re.compile(
    r"^\s*Definition\s+(?P<name>[A-Za-z0-9_']+)(?:\[[^\]]+\])?\s*:\s*(?P<after>.*)$"
)
DEF_END_RE   = re.compile(r"^\s*End\b")

# Regex for Datatype block
DATATYPE_START_RE = re.compile(r"^\s*Datatype\s*:\s*$")
DATATYPE_INLINE_RE = re.compile(r"^\s*Datatype\s*:\s*(?P<body>.+)$")
END_RE = re.compile(r"^\s*End\b")

# Regex for Type declaration
TYPE_DECL_RE = re.compile(
    r"^\s*Type\s+(?P<name>[A-Za-z0-9_']+)\s*=\s*(?P<after>.*)$"
)

# Regex for Theory and Ancestors
THEORY_RE = re.compile(r"^\s*Theory\s+(?P<name>[A-Za-z0-9_']+)\s*$")
ANCESTORS_RE = re.compile(r"^\s*Ancestors\[(?P<ancestors>[^\]]+)\]\s*$")

# Regex for Overload
OVERLOAD_RE = re.compile(r'Overload\s+(?P<name>[A-Za-z0-9_\']+)(?:\[local\])?\s*=\s*["\u201c](?P<value>[^"\u201d]+)["\u201d]')

def extract_theorems_from_lines(lines: List[str]) -> List[Dict]:
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = THEOREM_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        after = m.group("after").rstrip("\n")
        stmt_lines = [after] if after else []
        j = i + 1
        while j < n and not PROOF_LINE_RE.match(lines[j]):
            stmt_lines.append(lines[j].rstrip("\n"))
            j += 1
        statement = "\n".join(stmt_lines).strip()
        out.append({
            "kind": "Theorem",
            "name": name,
            "statement": statement
        })
        i = j + 1
    return out

def extract_definitions_from_lines(lines: List[str]) -> List[Dict]:
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = DEF_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        after = m.group("after").rstrip("\n")
        body_lines = [after] if after else []
        j = i + 1
        while j < n and not DEF_END_RE.match(lines[j]):
            body_lines.append(lines[j].rstrip("\n"))
            j += 1
        statement = "\n".join(body_lines).strip()
        out.append({
            "kind": "Definition",
            "name": name,
            "statement": statement
        })
        i = j + 1
    return out

def extract_datatypes_from_lines(lines: List[str]) -> List[Dict]:
    """
    Extract Datatype blocks from HOL4/CakeML scripts.
    
    Format:
    Datatype:
      typename = Constructor1 type1 type2
               | Constructor2 type3
               | ...
    End
    
    The datatype name is extracted from the first line of the body.
    """
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = DATATYPE_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        
        # Found a Datatype block
        body_lines = []
        j = i + 1
        while j < n and not END_RE.match(lines[j]):
            body_lines.append(lines[j].rstrip("\n"))
            j += 1
        
        body = "\n".join(body_lines).strip()
        
        # Try to extract the datatype name from the body
        # Format is typically: "name = Constructor1 | Constructor2 ..."
        name = "unnamed"
        if body:
            # Match the pattern: typename = ...
            name_match = re.match(r"^\s*([A-Za-z0-9_']+)\s*=", body)
            if name_match:
                name = name_match.group(1)
        
        out.append({
            "kind": "Datatype",
            "name": name,
            "statement": body
        })
        i = j + 1
    return out

def extract_types_from_lines(lines: List[str]) -> List[Dict]:
    """
    Extract Type declarations from HOL4/CakeML scripts.
    
    Format:
    Type typename = ``: type_definition``
    """
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = TYPE_DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        
        name = m.group("name")
        after = m.group("after").rstrip("\n")
        
        # Type declarations are typically single-line or may span multiple lines
        # We'll read until we find a complete statement (ends with ``)
        stmt_lines = [after] if after else []
        j = i + 1
        
        # Continue reading if the line doesn't end with `` or if it's incomplete
        while j < n and not after.rstrip().endswith("``"):
            stmt_lines.append(lines[j].rstrip("\n"))
            after = lines[j].rstrip("\n")
            j += 1
        
        statement = "\n".join(stmt_lines).strip()
        
        out.append({
            "kind": "Type",
            "name": name,
            "statement": statement
        })
        i = j
    return out

def extract_theory_and_ancestors(lines: List[str]) -> tuple:
    """
    Extract Theory name and Ancestors from HOL4/CakeML scripts.
    
    Format:
    Theory theory_name
    Ancestors
      ancestor1 ancestor2[qualified]
      ancestor3
    or
    Ancestors[qualified]
      ancestor1
    
    Note: [qualified] is a modifier/attribute, not an ancestor name.
    """
    theory_name = None
    ancestors = []
    
    i, n = 0, len(lines)
    while i < n:
        # Check for Theory declaration
        theory_match = THEORY_RE.match(lines[i])
        if theory_match:
            theory_name = theory_match.group("name")
            i += 1
            continue
        
        # Check for Ancestors declaration
        # Match both "Ancestors" and "Ancestors[...]" where [...] is ignored
        if re.match(r"^\s*Ancestors(\[[^\]]+\])?\s*$", lines[i]):
            # Continue reading indented lines as ancestors
            j = i + 1
            while j < n:
                line = lines[j]
                # Check if line is indented (starts with whitespace) and non-empty
                if line and line[0].isspace() and line.strip():
                    # Parse ancestor names from the line
                    # Remove [qualified] or other [...] modifiers
                    cleaned_line = re.sub(r'\[qualified\]', '', line)
                    # Split by whitespace and filter out empty strings
                    ancestor_names = [name.strip() for name in cleaned_line.split() if name.strip()]
                    ancestors.extend(ancestor_names)
                    j += 1
                elif not line.strip():  # Empty line
                    j += 1
                else:  # Non-indented line, end of ancestors
                    break
            i = j
            continue
        
        i += 1
    
    return theory_name, ancestors

def extract_overloads(lines: List[str]) -> Dict[str, str]:
    """
    Extract Overload declarations to build a replacement map.
    
    Format:
    Overload name[local] = "actual_value"
    """
    overloads = {}
    for line in lines:
        # Use finditer to handle multiple Overload statements on the same line
        for match in OVERLOAD_RE.finditer(line):
            name = match.group("name")
            value = match.group("value")
            overloads[name] = value
    return overloads

def apply_overload_replacements(statement: str, overloads: Dict[str, str]) -> str:
    """
    Replace overloaded names with their actual values in a statement.
    """
    result = statement
    for name, value in overloads.items():
        # Replace whole word occurrences only (using word boundaries)
        result = re.sub(r'\b' + re.escape(name) + r'\b', value, result)
    return result

def extract_all_items_in_order(lines: List[str], overloads: Dict[str, str]) -> List[Dict]:
    """
    Extract all items (Types, Datatypes, Definitions, Theorems) in their original order.
    Applies overload replacements to statements.
    """
    items = []
    i, n = 0, len(lines)
    
    while i < n:
        # Check for Type declaration
        type_match = TYPE_DECL_RE.match(lines[i])
        if type_match:
            name = type_match.group("name")
            after = type_match.group("after").rstrip("\n")
            stmt_lines = [after] if after else []
            j = i + 1
            
            # Continue reading if the line doesn't end with ``
            while j < n and not after.rstrip().endswith("``"):
                stmt_lines.append(lines[j].rstrip("\n"))
                after = lines[j].rstrip("\n")
                j += 1
            
            statement = "\n".join(stmt_lines).strip()
            statement = apply_overload_replacements(statement, overloads)
            items.append({
                "kind": "Type",
                "name": name,
                "statement": statement
            })
            i = j
            continue
        
        # Check for Datatype block - multiline format
        if DATATYPE_START_RE.match(lines[i]):
            body_lines = []
            j = i + 1
            while j < n and not END_RE.match(lines[j]):
                body_lines.append(lines[j].rstrip("\n"))
                j += 1
            
            body = "\n".join(body_lines).strip()
            name = "unnamed"
            if body:
                name_match = re.match(r"^\s*([A-Za-z0-9_']+)\s*=", body)
                if name_match:
                    name = name_match.group(1)
            
            body = apply_overload_replacements(body, overloads)
            items.append({
                "kind": "Datatype",
                "name": name,
                "statement": body
            })
            i = j + 1
            continue
        
        # Check for Datatype block - inline format (all on one line)
        inline_datatype_match = DATATYPE_INLINE_RE.match(lines[i])
        if inline_datatype_match:
            body = inline_datatype_match.group("body").rstrip("\n").strip()
            name = "unnamed"
            if body:
                name_match = re.match(r"^\s*([A-Za-z0-9_']+)\s*=", body)
                if name_match:
                    name = name_match.group(1)
            
            body = apply_overload_replacements(body, overloads)
            items.append({
                "kind": "Datatype",
                "name": name,
                "statement": body
            })
            # Skip past the End line
            j = i + 1
            while j < n and not END_RE.match(lines[j]):
                j += 1
            i = j + 1
            continue
        
        # Check for Definition
        def_match = DEF_START_RE.match(lines[i])
        if def_match:
            name = def_match.group("name")
            after = def_match.group("after").rstrip("\n")
            body_lines = [after] if after else []
            j = i + 1
            while j < n and not DEF_END_RE.match(lines[j]):
                body_lines.append(lines[j].rstrip("\n"))
                j += 1
            statement = "\n".join(body_lines).strip()
            statement = apply_overload_replacements(statement, overloads)
            items.append({
                "kind": "Definition",
                "name": name,
                "statement": statement
            })
            i = j + 1
            continue
        
        # Check for Theorem
        thm_match = THEOREM_START_RE.match(lines[i])
        if thm_match:
            name = thm_match.group("name")
            after = thm_match.group("after").rstrip("\n")
            stmt_lines = [after] if after else []
            j = i + 1
            while j < n and not PROOF_LINE_RE.match(lines[j]):
                stmt_lines.append(lines[j].rstrip("\n"))
                j += 1
            statement = "\n".join(stmt_lines).strip()
            statement = apply_overload_replacements(statement, overloads)
            items.append({
                "kind": "Theorem",
                "name": name,
                "statement": statement
            })
            i = j + 1
            continue
        
        # No match, move to next line
        i += 1
    
    return items

def extract_from_file(filepath: str) -> List[Dict]:
    try:
        with open(filepath, encoding="utf-8") as f:
            lines = f.read().splitlines()
    except Exception as e:
        print(f"Warning: failed to read {filepath}: {e}", file=sys.stderr)
        return []
    
    # Extract theory and ancestors metadata
    theory_name, ancestors = extract_theory_and_ancestors(lines)
    
    # Extract overload mappings
    overloads = extract_overloads(lines)
    
    # Extract all items in their original order with overload replacements
    items = extract_all_items_in_order(lines, overloads)
    
    # Add metadata to each item
    for it in items:
        it["theory"] = theory_name
        it["ancestors"] = ancestors
    
    return items

def extract_from_dir(input_dir: str, output_dir: str) -> Dict:
    """Extract items from all .sml files and save each to its own JSON file."""
    stats = {
        'files_processed': 0,
        'total_items': 0,
        'types': 0,
        'datatypes': 0,
        'definitions': 0,
        'theorems': 0
    }
    
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    for root, dirs, files in os.walk(input_dir):
        for fname in files:
            if fname.lower().endswith(".sml"):
                full = os.path.join(root, fname)
                items = extract_from_file(full)
                
                if items:
                    # Create output filename: replace .sml with .json
                    output_fname = fname[:-4] + ".json"
                    output_path = os.path.join(output_dir, output_fname)
                    
                    # Write items to JSON file
                    with open(output_path, "w", encoding="utf-8") as outf:
                        json.dump(items, outf, ensure_ascii=False, indent=2)
                    
                    # Update statistics
                    stats['files_processed'] += 1
                    stats['total_items'] += len(items)
                    stats['types'] += sum(1 for x in items if x['kind'] == 'Type')
                    stats['datatypes'] += sum(1 for x in items if x['kind'] == 'Datatype')
                    stats['definitions'] += sum(1 for x in items if x['kind'] == 'Definition')
                    stats['theorems'] += sum(1 for x in items if x['kind'] == 'Theorem')
                    
                    print(f"Extracted {len(items)} items from {fname} -> {output_fname}")
    
    return stats

def main():
    if len(sys.argv) != 3:
        print("Usage: python extract_multi.py input_directory output_directory", file=sys.stderr)
        sys.exit(1)
    input_dir = sys.argv[1]
    output_dir = sys.argv[2]
    stats = extract_from_dir(input_dir, output_dir)
    
    print(f"\nProcessing complete!")
    print(f"  Files processed: {stats['files_processed']}")
    print(f"  Total items: {stats['total_items']}")
    print(f"    Types: {stats['types']}")
    print(f"    Datatypes: {stats['datatypes']}")
    print(f"    Definitions: {stats['definitions']}")
    print(f"    Theorems: {stats['theorems']}")

if __name__ == "__main__":
    main()