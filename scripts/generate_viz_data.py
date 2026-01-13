#!/usr/bin/env python3
"""
Generate UMAP visualization data with edges for the Unified System paper pack.
Extracts declarations from Lean files and builds k-NN edges from feature vectors.
"""

import json
import os
import re
import sys
from pathlib import Path

def parse_declarations(text, filepath):
    """Extract declarations from Lean source."""
    decls = []
    lines = text.split('\n')

    # Patterns for declarations
    decl_re = re.compile(
        r'^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)?'
        r'(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+'
        r'([^\s:(\[{]+)'
    )

    # Track namespace
    ns_stack = []

    for i, line in enumerate(lines):
        # Namespace tracking
        ns_match = re.match(r'^\s*namespace\s+([A-Za-z0-9_.]+)', line)
        if ns_match:
            ns_stack.append(ns_match.group(1))
            continue

        end_match = re.match(r'^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$', line)
        if end_match and ns_stack:
            ns_stack.pop()
            continue

        # Declaration matching
        decl_match = decl_re.match(line)
        if decl_match:
            kind = decl_match.group(1)
            name = decl_match.group(2)

            # Build full name
            prefix = '.'.join(ns_stack)
            full_name = f"{prefix}.{name}" if prefix else name

            # Extract snippet (next few lines)
            snippet_lines = lines[i:min(i+5, len(lines))]
            snippet = '\n'.join(snippet_lines)[:300]

            decls.append({
                'name': full_name,
                'kind': kind,
                'line': i + 1,
                'path': filepath,
                'snippet': snippet
            })

    return decls

def compute_features(decl):
    """Compute feature vector for a declaration."""
    snippet = decl.get('snippet', '')

    features = {
        'implies': len(re.findall(r'→|->', snippet)),
        'forall': len(re.findall(r'∀', snippet)),
        'exists': len(re.findall(r'∃', snippet)),
        'eq': len(re.findall(r'=', snippet)),
        'tactics': len(re.findall(r'\b(simp|rw|intro|apply|cases|exact|have)\b', snippet)),
        'length': len(snippet),
        'name_depth': decl['name'].count('.')
    }
    return features

def family_from_path(path):
    """Determine family/layer from file path."""
    if 'Bridge' in path:
        return 'Bridge'
    elif 'TensorLogic' in path:
        return 'TensorLogic'
    elif 'Combinators/Topos' in path:
        return 'Topos'
    elif 'Combinators' in path:
        return 'Combinator'
    elif 'LoFPrimary' in path:
        return 'LoFKernel'
    elif 'LoF' in path:
        return 'LoF'
    elif 'CLI' in path:
        return 'CLI'
    elif 'Tests' in path:
        return 'Test'
    else:
        return 'Other'

def knn_edges(items, k=5):
    """Build k-NN edges from feature vectors."""
    n = len(items)
    if n == 0:
        return []

    # Extract feature vectors
    all_features = [list(it['features'].values()) for it in items]

    # L1 distance
    def l1_dist(a, b):
        return sum(abs(x - y) for x, y in zip(a, b))

    edges = []
    for i in range(n):
        # Compute distances to all other nodes
        distances = []
        for j in range(n):
            if i != j:
                d = l1_dist(all_features[i], all_features[j])
                distances.append((j, d))

        # Sort and take top k
        distances.sort(key=lambda x: x[1])
        for j, _ in distances[:k]:
            if i < j:  # Avoid duplicates
                edges.append([i, j])

    return edges

def simple_umap_2d(items, seed=42):
    """Simple 2D layout based on features (fallback if UMAP not available)."""
    import random
    random.seed(seed)

    for it in items:
        features = it['features']
        # Simple projection based on features
        x = (features.get('implies', 0) * 0.1 +
             features.get('name_depth', 0) * 0.2 +
             random.random() * 0.3)
        y = (features.get('tactics', 0) * 0.1 +
             features.get('length', 0) * 0.0001 +
             random.random() * 0.3)

        # Normalize to [0, 1]
        it['pos'] = {'x': min(1, max(0, x)), 'y': min(1, max(0, y))}

    return items

def simple_umap_3d(items, seed=42):
    """Simple 3D layout based on features."""
    import random
    random.seed(seed)

    for it in items:
        features = it['features']
        x = (features.get('implies', 0) * 0.1 + random.random() * 0.3)
        y = (features.get('tactics', 0) * 0.1 + random.random() * 0.3)
        z = (features.get('name_depth', 0) * 0.2 + random.random() * 0.3)

        it['pos3'] = {
            'x': min(1, max(0, x)),
            'y': min(1, max(0, y)),
            'z': min(1, max(0, z))
        }

    return items

def main():
    script_dir = Path(__file__).parent
    root_dir = script_dir.parent
    src_dir = root_dir / 'HeytingLean'
    out_dir = root_dir / 'artifacts' / 'visuals'

    out_dir.mkdir(parents=True, exist_ok=True)

    # Find all Lean files
    lean_files = list(src_dir.rglob('*.lean'))
    print(f"Found {len(lean_files)} Lean files")

    # Extract declarations
    items = []
    for filepath in lean_files:
        rel_path = str(filepath.relative_to(root_dir))
        text = filepath.read_text(encoding='utf-8', errors='ignore')
        decls = parse_declarations(text, rel_path)

        for decl in decls:
            decl['family'] = family_from_path(rel_path)
            decl['features'] = compute_features(decl)
            items.append(decl)

    print(f"Extracted {len(items)} declarations")

    if not items:
        print("No declarations found, exiting")
        return

    # Generate positions
    items = simple_umap_2d(items)
    items = simple_umap_3d(items)

    # Build edges
    edges = knn_edges(items, k=5)
    print(f"Generated {len(edges)} k-NN edges")

    # Output data
    data = {
        'items': items,
        'edges': edges
    }

    out_file = out_dir / 'unified_proofs_data.js'
    with open(out_file, 'w') as f:
        f.write('window.UNIFIED_PROOFS = ')
        json.dump(data, f, indent=2)

    print(f"Wrote {out_file}")

    # Also write JSON
    json_file = out_dir / 'unified_proofs_data.json'
    with open(json_file, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"Wrote {json_file}")

if __name__ == '__main__':
    main()
