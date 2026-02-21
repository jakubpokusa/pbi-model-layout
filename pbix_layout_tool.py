"""
pbix_layout_tool.py  v1.1
--------------------------
Automatically arranges fact and dimension tables in a Power BI .pbix
model diagram view into a clean, relationship-aware layout.

Usage:
    # Step 1 — extract relationships from your .pbit
    python pbix_layout_tool.py --extract-relations model.pbit

    # Step 2 — apply the layout
    python pbix_layout_tool.py model.pbix --relations relations.json

Options:
    --output FILE           Output .pbix path (default: input_arranged.pbix)
    --relations FILE        Path to a JSON file declaring relationships
                            (see below). If omitted, falls back to a simple
                            radial layout with no snowflake awareness.
    --fact-prefixes P1,P2   Comma-separated prefixes marking fact tables
                            (default: fct_,fact_,FCT_,FACT_,Fact_,Fct_)
    --dim-prefixes P1,P2    Comma-separated prefixes marking dim tables
                            (default: dim_,DIM_,Dim_,d_,D_)
    --radius N              Base radius for star layout (default: 520)
    --table-width N         Fallback card width if not in DiagramLayout (default: 250)
    --table-height N        Fallback card height if not in DiagramLayout (default: 200)
    --create-tabs           Generate focused diagram tabs (one per fact table)
    --dry-run               Print the layout plan without writing anything
    --extract-relations     Extract relationships from a .pbit and write relations.json
    --generate-relations    Print a relations.json template based on tables in the .pbix
    --help                  Show this message

How to get the .pbit (needed for --extract-relations):
    In Power BI Desktop:  File → Save As → Power BI Template (.pbit)
    The .pbit is a ZIP that contains a human-readable DataModelSchema
    with all relationships. The extractor reads that automatically.

Relationships JSON format (relations.json):
    [
        { "from": "fct_Orders",     "to": "dim_Customer" },
        { "from": "fct_Orders",     "to": "dim_Product" },
        { "from": "dim_Product",    "to": "dim_Category" }
    ]
    Each entry is one relationship. "from" is the many-side (fact or parent dim),
    "to" is the one-side (dim or child dim). Direction doesn't matter for layout —
    the tool infers roles from the prefixes.

Layout modes:
    The tool picks a layout automatically based on your model:

    SINGLE FACT → Star layout
        The fact table sits at the centre. Dimension tables are placed in a
        ring around it at the configured radius. Snowflake children (dims
        linked to other dims rather than directly to the fact) are pushed
        outward behind their parent dim.

    MULTIPLE FACTS → Grid layout
        Facts stack vertically on the left. All dimension tables line up in
        a single horizontal row below, offset to the right to create a clear
        gap. Dims that have snowflake children are pushed to the end of the
        row, with their children placed immediately after them.

    In both modes the tool reads each table's real card size from the
    DiagramLayout (Power BI sets these based on column count), so nothing
    overlaps.
"""

import argparse
import json
import math
import os
import sys
import zipfile
from collections import defaultdict
from copy import deepcopy


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DIAGRAM_LAYOUT_PATH = "DiagramLayout"

DEFAULT_FACT_PREFIXES = ["fct_", "fact_", "FCT_", "FACT_", "Fact_", "Fct_"]
DEFAULT_DIM_PREFIXES  = ["dim_", "DIM_", "Dim_", "d_", "D_"]

DEFAULT_RADIUS       = 520
DEFAULT_TABLE_WIDTH  = 250
DEFAULT_TABLE_HEIGHT = 200
SNOWFLAKE_PUSH       = 320   # extra px to push snowflake dims behind parent
FACT_GAP             = 50    # vertical gap between stacked fact tables
OTHER_RING_RADIUS    = 900


# ---------------------------------------------------------------------------
# Classification & relationship parsing
# ---------------------------------------------------------------------------

def classify_tables(table_names, fact_prefixes, dim_prefixes):
    """
    Classify tables into facts, dims, or other based on naming conventions.
    
    Returns: (fact_tables, dim_tables, other_tables) — each a list of table names
    """
    fact, dim, other = [], [], []
    for name in table_names:
        if any(name.startswith(p) for p in fact_prefixes):
            fact.append(name)
        elif any(name.startswith(p) for p in dim_prefixes):
            dim.append(name)
        else:
            other.append(name)
    return fact, dim, other


def parse_relations(relations_path):
    """
    Load and return list of {from, to} dicts from the JSON sidecar.
    
    Each relationship must have 'from' and 'to' keys.
    """
    with open(relations_path, 'r') as f:
        rels = json.load(f)
    for r in rels:
        if "from" not in r or "to" not in r:
            raise ValueError(f"Each relationship needs 'from' and 'to' keys. Got: {r}")
    return rels


def build_adjacency(relations, fact_tables, dim_tables):
    """
    From the flat relationship list, build structured graph:
        fact_to_dims  : { fact_name: [dim_name, ...] }   — direct fact→dim links
        snowflake     : { parent_dim: [child_dim, ...] } — snowflake links (dim→dim)
        orphan_dims   : set of dims not reachable from any fact

    Logic: if one side is a fact, it's a star link.
           if both sides are dims, it's a snowflake link.
    """
    fact_set = set(fact_tables)
    dim_set  = set(dim_tables)

    fact_to_dims  = defaultdict(list)
    dim_links     = []          # raw dim-dim pairs, resolved after
    linked_dims   = set()

    # Classify each relationship
    for r in relations:
        a, b = r["from"], r["to"]

        if a in fact_set and b in dim_set:
            fact_to_dims[a].append(b)
            linked_dims.add(b)
        elif b in fact_set and a in dim_set:
            fact_to_dims[b].append(a)
            linked_dims.add(a)
        elif a in dim_set and b in dim_set:
            dim_links.append((a, b))
            linked_dims.add(a)
            linked_dims.add(b)

    # Resolve snowflake direction: parent is the dim directly linked to a fact
    all_direct_dims = set()
    for dims in fact_to_dims.values():
        all_direct_dims.update(dims)

    snowflake = defaultdict(list)
    for a, b in dim_links:
        # Parent = the one directly connected to a fact
        if a in all_direct_dims and b not in all_direct_dims:
            snowflake[a].append(b)
        elif b in all_direct_dims and a not in all_direct_dims:
            snowflake[b].append(a)
        # If both or neither are direct dims, treat as parent=first mentioned
        elif a in all_direct_dims and b in all_direct_dims:
            snowflake[a].append(b)
        else:
            snowflake[a].append(b)

    orphan_dims = dim_set - linked_dims

    return dict(fact_to_dims), dict(snowflake), orphan_dims


# ---------------------------------------------------------------------------
# Layout computation
# ---------------------------------------------------------------------------

def extract_node_sizes(layout):
    """
    Pull the real width/height PBI assigned each table.
    
    Power BI sets card heights based on column count, so we read these
    from the DiagramLayout to avoid overlaps.
    
    Returns: { table_name: (width, height) }
    """
    sizes = {}
    nodes = layout.get("diagrams", [{}])[0].get("nodes", [])
    for n in nodes:
        sizes[n["nodeIndex"]] = (n["size"]["width"], n["size"]["height"])
    return sizes


def compute_layout(fact_tables, dim_tables, other_tables,
                   fact_to_dims, snowflake, orphan_dims,
                   radius, table_width, table_height, node_sizes=None):
    """
    Core layout engine with two modes:

    SINGLE FACT  → classic star: fact in center, dims in a ring around it.
    MULTIPLE FACTS → grid layout:
        - Facts stack vertically on the left
        - All dims line up in a horizontal row below, offset to the right
        - Dims with snowflake children go at the end of the row

    node_sizes: { name: (w, h) } read from the real DiagramLayout so we
                use PBI's actual card heights (which vary by column count).
    
    Returns: { table_name: (x, y) } — positions for all tables
    """
    positions = {}
    COL_GAP  = 60   # horizontal gap between columns
    ROW_GAP  = 40   # vertical gap between rows

    # Helper functions to get node dimensions (use real sizes or fallback)
    def w(name):
        if node_sizes and name in node_sizes:
            return node_sizes[name][0]
        return table_width

    def h(name):
        if node_sizes and name in node_sizes:
            return node_sizes[name][1]
        return table_height

    # Collect all snowflake children for filtering
    all_snowflake_children = set()
    for children in snowflake.values():
        all_snowflake_children.update(children)

    # Sort facts by relationship count (most connections first)
    fact_tables_sorted = sorted(fact_tables,
                                key=lambda f: len(fact_to_dims.get(f, [])),
                                reverse=True)

    # ---------------------------------------------------------------
    # SINGLE FACT → star layout
    # ---------------------------------------------------------------
    if len(fact_tables_sorted) == 1:
        fact = fact_tables_sorted[0]
        positions[fact] = (0, 0)  # Fact at center

        dims = fact_to_dims.get(fact, [])
        # Remove snowflake children from ring — they go behind parents
        ring_dims = [d for d in dims if d not in all_snowflake_children]
        n = len(ring_dims)

        # Place dims in a ring around the fact
        for i, dim_name in enumerate(ring_dims):
            angle = math.radians(-90 + (360 * i / max(n, 1)))
            x = radius * math.cos(angle) - w(dim_name) / 2
            y = radius * math.sin(angle) - h(dim_name) / 2
            positions[dim_name] = (x, y)

            # Place snowflake children behind their parent dim
            for j, child in enumerate(snowflake.get(dim_name, [])):
                push = SNOWFLAKE_PUSH * (j + 1)
                cx = (radius + push) * math.cos(angle) - w(child) / 2
                cy = (radius + push) * math.sin(angle) - h(child) / 2
                positions[child] = (cx, cy)

        # Place orphans in outer ring
        unplaced = [d for d in dim_tables if d not in positions]
        for i, d in enumerate(unplaced):
            angle = math.radians(-90 + (360 * i / max(len(unplaced), 1)))
            positions[d] = (
                OTHER_RING_RADIUS * math.cos(angle) - w(d) / 2,
                OTHER_RING_RADIUS * math.sin(angle) - h(d) / 2
            )

        return positions

    # ---------------------------------------------------------------
    # MULTIPLE FACTS → grid layout
    #
    #   [fact_A]
    #   [fact_B]
    #   [fact_C]
    #   [dim_1] [dim_2] [dim_3] ... [parent_dim] [child_dim]
    #
    #   Facts stacked vertically on the left.
    #   All dims in one straight horizontal line below the facts.
    #   Snowflake parents + children at the end of that line.
    # ---------------------------------------------------------------

    # Calculate fact column width (widest fact card)
    fact_col_w = max(w(f) for f in fact_tables_sorted)

    # Stack facts vertically starting at (0, 0)
    y_cursor = 0
    for f in fact_tables_sorted:
        positions[f] = (0, y_cursor)
        y_cursor += h(f) + ROW_GAP

    # Bottom of the fact block (where dim row starts)
    fact_block_bottom = y_cursor

    # Build dim row order: plain dims first, then snowflake groups
    snowflake_parents = set(snowflake.keys())  # dims that HAVE children

    # Plain dims = dims with no snowflake relationship at all
    plain_dims = [d for d in dim_tables
                  if d not in all_snowflake_children and d not in snowflake_parents]

    # Snowflake groups = parent immediately followed by its children
    tail = []
    for d in dim_tables:
        if d in snowflake_parents:
            tail.append(d)
            tail.extend(snowflake.get(d, []))

    dim_row = plain_dims + tail

    # Place dims in a horizontal row below all facts
    # Start x at fact_col_w + gap to create visual separation
    x_cursor = fact_col_w + COL_GAP
    for name in dim_row:
        positions[name] = (x_cursor, fact_block_bottom)
        x_cursor += w(name) + COL_GAP

    # Place "other" tables (non-fact, non-dim) below everything
    if other_tables:
        max_y = max(y for x, y in positions.values()) if positions else 0
        max_bottom = max_y + max((h(n) for n in positions), default=table_height)
        ox = 0
        for name in other_tables:
            positions[name] = (ox, max_bottom + ROW_GAP)
            ox += w(name) + COL_GAP

    return positions


# ---------------------------------------------------------------------------
# .pbix read / write
# ---------------------------------------------------------------------------

def read_diagram_layout(pbix_path):
    """
    Read and parse the DiagramLayout file from a .pbix.
    
    Handles both UTF-16-LE (real PBI Desktop) and UTF-8 encodings.
    Returns the parsed JSON structure, or None if not found.
    """
    with zipfile.ZipFile(pbix_path, 'r') as zf:
        if DIAGRAM_LAYOUT_PATH not in zf.namelist():
            return None
        raw = zf.read(DIAGRAM_LAYOUT_PATH)

    # Try UTF-16-LE first (what real PBI Desktop produces), then UTF-8
    for enc in ('utf-16-le', 'utf-8'):
        try:
            text = raw.decode(enc)
            brace = text.find('{')
            if brace != -1:
                return json.loads(text[brace:])
        except (UnicodeDecodeError, json.JSONDecodeError):
            continue

    raise ValueError("Could not decode DiagramLayout.")


def extract_table_names(layout):
    """
    Extract table names from DiagramLayout structure.
    
    Real PBI DiagramLayout structure:
        { "diagrams": [ { "nodes": [ { "nodeIndex": "table_name", ... }, ... ] } ] }
    
    Returns: list of table names
    """
    if layout is None:
        return []
    nodes = layout.get("diagrams", [{}])[0].get("nodes", [])
    return [n["nodeIndex"] for n in nodes if "nodeIndex" in n]


def apply_positions(layout, positions, table_width, table_height):
    """
    Update node positions in the DiagramLayout structure.
    
    Preserves each node's existing size (PBI sets these based on column count)
    and all other fields (lineageTag, zIndex, etc).
    Only overwrites location.x and location.y.

    PBI Model View doesn't render negative coordinates, so we shift the
    entire layout so the top-left-most table lands at (50, 50).
    
    Returns: modified layout dict
    """
    if not positions:
        return layout

    # Calculate offset to shift all positions to positive space
    min_x = min(x for x, y in positions.values())
    min_y = min(y for x, y in positions.values())
    offset_x = 50 - min_x
    offset_y = 50 - min_y

    # Apply positions to master diagram (index 0)
    nodes = layout.get("diagrams", [{}])[0].get("nodes", [])
    for node in nodes:
        name = node.get("nodeIndex")
        if name in positions:
            x, y = positions[name]
            node["location"]["x"] = round(x + offset_x, 2)
            node["location"]["y"] = round(y + offset_y, 2)
    return layout


def create_diagram_tabs(layout, fact_tables, fact_to_dims, snowflake, 
                        radius, table_width, table_height, node_sizes=None):
    """
    Generate focused diagram views: one master (all tables), then one tab per fact.
    
    Each fact tab shows only that fact + its connected dims + snowflake children
    arranged in a star layout.
    
    Returns: modified layout with multiple entries in diagrams[] array.
    Each diagram entry has:
        - id: unique identifier
        - name: display name for the tab
        - nodes: list of table nodes in this view
    """
    if not layout or "diagrams" not in layout:
        return layout
    
    # Keep the master diagram (index 0) as-is — already positioned
    master_diagram = layout["diagrams"][0]
    
    # Build a lookup: table name → full node object from master
    all_nodes = {n["nodeIndex"]: deepcopy(n) for n in master_diagram["nodes"]}
    
    # Collect snowflake children
    all_snowflake_children = set()
    for children in snowflake.values():
        all_snowflake_children.update(children)
    
    # Create one diagram per fact
    new_diagrams = [master_diagram]  # diagram[0] = master view
    
    for fact in fact_tables:
        # Build set of tables to include in this focused view
        visible_tables = {fact}
        
        # Add all dims connected to this fact
        for dim in fact_to_dims.get(fact, []):
            visible_tables.add(dim)
            # Add snowflake children of this dim
            if dim in snowflake:
                visible_tables.update(snowflake[dim])
        
        # Filter nodes to only visible tables
        focused_nodes = [deepcopy(all_nodes[t]) for t in visible_tables if t in all_nodes]
        
        # Compute a star layout for this focused view
        direct_dims = [d for d in fact_to_dims.get(fact, []) 
                       if d not in all_snowflake_children]
        
        positions_focused = {}
        
        # Place fact at center
        positions_focused[fact] = (0, 0)
        
        # Place dims in a ring around the fact
        n = len(direct_dims)
        for i, dim in enumerate(direct_dims):
            angle = math.radians(-90 + (360 * i / max(n, 1)))
            w = node_sizes.get(dim, (table_width, 0))[0] if node_sizes else table_width
            h = node_sizes.get(dim, (0, table_height))[1] if node_sizes else table_height
            x = radius * math.cos(angle) - w / 2
            y = radius * math.sin(angle) - h / 2
            positions_focused[dim] = (x, y)
            
            # Place snowflake children behind this dim
            for j, child in enumerate(snowflake.get(dim, [])):
                push = SNOWFLAKE_PUSH * (j + 1)
                cw = node_sizes.get(child, (table_width, 0))[0] if node_sizes else table_width
                ch = node_sizes.get(child, (0, table_height))[1] if node_sizes else table_height
                cx = (radius + push) * math.cos(angle) - cw / 2
                cy = (radius + push) * math.sin(angle) - ch / 2
                positions_focused[child] = (cx, cy)
        
        # Apply positions with offset to positive space
        if positions_focused:
            min_x = min(x for x, y in positions_focused.values())
            min_y = min(y for x, y in positions_focused.values())
            offset_x = 50 - min_x
            offset_y = 50 - min_y
            
            for node in focused_nodes:
                name = node["nodeIndex"]
                if name in positions_focused:
                    x, y = positions_focused[name]
                    node["location"]["x"] = round(x + offset_x, 2)
                    node["location"]["y"] = round(y + offset_y, 2)
        
        # Create diagram entry for this fact
        diagram_entry = {
            "id": f"diagram_{len(new_diagrams)}",  # simple sequential ID
            "name": fact,  # Tab will show the fact table name
            "nodes": focused_nodes
        }
        
        new_diagrams.append(diagram_entry)
    
    # Replace diagrams array with master + all focused views
    layout["diagrams"] = new_diagrams
    return layout


def repack_pbix(original_path, output_path, modified_files):
    """
    Repack the .pbix ZIP file with modified DiagramLayout.
    
    Args:
        original_path: path to input .pbix
        output_path: path to write output .pbix
        modified_files: { filename: bytes } dict of files to replace
    """
    with zipfile.ZipFile(original_path, 'r') as zin:
        with zipfile.ZipFile(output_path, 'w') as zout:
            # Copy all files, replacing any that are in modified_files
            for item in zin.infolist():
                compress = zipfile.ZIP_STORED if item.filename == "[Content_Types].xml" \
                           else zipfile.ZIP_DEFLATED
                data = modified_files.get(item.filename, zin.read(item.filename))
                zout.writestr(item, data, compress_type=compress)

            # Add any new files that weren't in the original
            for path, data in modified_files.items():
                if path not in zin.namelist():
                    zout.writestr(path, data, compress_type=zipfile.ZIP_DEFLATED)


# ---------------------------------------------------------------------------
# .pbit relationship extractor
# ---------------------------------------------------------------------------

def extract_relations_from_pbit(pbit_path, output_path="relations.json", debug=False):
    """
    Extract relationships from a .pbit file and write to relations.json.
    
    Opens a .pbit, finds DataModelSchema, strips binary prefix,
    parses the JSON, pulls out all relationships, and writes relations.json.

    Real Power BI .pbit files encode DataModelSchema as UTF-16-LE with
    a BOM prefix. We try multiple encoding strategies to handle all PBI versions.
    """
    with zipfile.ZipFile(pbit_path, 'r') as zf:
        schema_file = None
        for name in zf.namelist():
            if "DataModelSchema" in name:
                schema_file = name
                break
        if schema_file is None:
            raise FileNotFoundError(
                "No DataModelSchema found in this .pbit.\n"
                "Make sure you saved as Power BI Template (.pbit) in PBI Desktop."
            )
        raw = zf.read(schema_file)

    # Debug output if requested
    if debug:
        print(f"\n[DEBUG] File inside .pbit: {schema_file}")
        print(f"\n[DEBUG] Raw size: {len(raw)} bytes")
        print(f"[DEBUG] First 100 bytes (hex): {raw[:100].hex()}")
        print(f"[DEBUG] First 100 bytes (repr): {repr(raw[:100])}\n")

    schema = None

    # Try multiple encoding strategies to handle different PBI versions
    
    # Strategy 1: UTF-16-LE (what real PBI Desktop produces)
    try:
        text = raw.decode('utf-16-le')
        brace = text.find('{')
        if brace != -1:
            schema = json.loads(text[brace:])
            if debug:
                print("[DEBUG] Decoded as UTF-16-LE")
    except (UnicodeDecodeError, json.JSONDecodeError):
        pass

    # Strategy 2: UTF-16-LE with BOM stripped first
    if schema is None:
        try:
            if raw[:2] == b'\xff\xfe':
                text = raw[2:].decode('utf-16-le')
            else:
                text = raw.decode('utf-16-le', errors='ignore')
            brace = text.find('{')
            if brace != -1:
                schema = json.loads(text[brace:])
                if debug:
                    print("[DEBUG] Decoded as UTF-16-LE (BOM stripped)")
        except (UnicodeDecodeError, json.JSONDecodeError):
            pass

    # Strategy 3: UTF-8, skip binary prefix before first '{'
    if schema is None:
        try:
            brace = raw.find(b'{')
            if brace != -1:
                schema = json.loads(raw[brace:].decode('utf-8'))
                if debug:
                    print("[DEBUG] Decoded as UTF-8 (binary prefix skipped)")
        except (UnicodeDecodeError, json.JSONDecodeError):
            pass

    # Strategy 4: UTF-8 with BOM
    if schema is None:
        try:
            start = 3 if raw[:3] == b'\xef\xbb\xbf' else 0
            text = raw[start:].decode('utf-8', errors='ignore')
            brace = text.find('{')
            if brace != -1:
                schema = json.loads(text[brace:])
                if debug:
                    print("[DEBUG] Decoded as UTF-8 (errors ignored)")
        except (UnicodeDecodeError, json.JSONDecodeError):
            pass

    if schema is None:
        print("[ERROR] Could not parse DataModelSchema.")
        print("        Run with --debug-pbit to see the raw bytes for diagnosis.")
        sys.exit(1)

    # Extract relationships from schema
    # Real PBI uses lowercase keys; older files may use uppercase
    model = schema.get("model", schema.get("Model", {}))
    raw_rels = model.get("relationships", model.get("Relationships", []))

    if not raw_rels:
        print("[!] DataModelSchema contains no relationships.")
        print("    Make sure your model has relationships created in Power BI Desktop.")
        return

    # Build clean relations list and print summary table
    relations = []
    print(f"\n[*] Found {len(raw_rels)} relationship(s):\n")
    print(f"    {'From':<25} {'To':<25} {'Join columns'}")
    print(f"    {'-'*25} {'-'*25} {'-'*35}")

    for r in raw_rels:
        # Handle both old and new field name formats
        src_tbl  = r.get("fromTable",  r.get("SourceTable", "?"))
        ref_tbl  = r.get("toTable",    r.get("ReferencedTable", "?"))
        src_col  = r.get("fromColumn", r.get("SourceColumn", "?"))
        ref_col  = r.get("toColumn",   r.get("ReferencedColumn", "?"))
        relations.append({"from": src_tbl, "to": ref_tbl})
        print(f"    {src_tbl:<25} {ref_tbl:<25} {src_col} → {ref_col}")

    # Write relations.json
    with open(output_path, 'w') as f:
        json.dump(relations, f, indent=4)

    print(f"\n[✓] Written {output_path}  ({len(relations)} relationships)")
    print(f"    You can now run:\n")
    print(f"      python pbix_layout_tool.py your_model.pbix --relations {output_path}\n")


# ---------------------------------------------------------------------------
# Template generator
# ---------------------------------------------------------------------------

def generate_relations_template(table_names, fact_prefixes, dim_prefixes):
    """
    Print a relations.json template with all possible fact→dim combinations.
    
    User should remove non-existent relationships and add any dim→dim snowflake links.
    """
    fact, dim, _ = classify_tables(table_names, fact_prefixes, dim_prefixes)
    print("\n// relations.json — fill in the actual relationships from your model.")
    print("// Remove any lines that don't apply. Add dim→dim lines for snowflakes.\n")
    print("[")
    lines = []
    for f in fact:
        for d in dim:
            lines.append(f'    {{ "from": "{f}", "to": "{d}" }}')
    print(",\n".join(lines))
    print("]")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Auto-arrange Power BI model diagram into a clean layout.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("input", nargs="?", default=None,
                        help="Path to your .pbix file")
    parser.add_argument("--output", default=None)
    parser.add_argument("--relations", default=None,
                        help="Path to relations.json")
    parser.add_argument("--fact-prefixes", default=None)
    parser.add_argument("--dim-prefixes", default=None)
    parser.add_argument("--radius", type=int, default=DEFAULT_RADIUS)
    parser.add_argument("--table-width", type=int, default=DEFAULT_TABLE_WIDTH)
    parser.add_argument("--table-height", type=int, default=DEFAULT_TABLE_HEIGHT)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--create-tabs", action="store_true",
                        help="Generate focused diagram tabs (one per fact table)")
    parser.add_argument("--generate-relations", action="store_true",
                        help="Print a relations.json template")
    parser.add_argument("--extract-relations", default=None, metavar="PBIT",
                        help="Extract relationships from a .pbit file and write relations.json")
    parser.add_argument("--debug-pbit", action="store_true",
                        help="Show raw bytes of DataModelSchema for troubleshooting")
    args = parser.parse_args()

    # Parse prefix lists
    fact_prefixes = args.fact_prefixes.split(",") if args.fact_prefixes else DEFAULT_FACT_PREFIXES
    dim_prefixes  = args.dim_prefixes.split(",")  if args.dim_prefixes  else DEFAULT_DIM_PREFIXES

    # --- Extract relations mode (standalone — doesn't need the .pbix input) ---
    if args.extract_relations:
        pbit_path = args.extract_relations
        if not os.path.isfile(pbit_path):
            print(f"[ERROR] .pbit file not found: {pbit_path}")
            sys.exit(1)
        print(f"[*] Extracting relationships from: {pbit_path}")
        extract_relations_from_pbit(pbit_path, debug=args.debug_pbit)
        sys.exit(0)

    # --- From here on we need the .pbix ---
    if args.input is None:
        parser.print_help()
        sys.exit(1)
    if not os.path.isfile(args.input):
        print(f"[ERROR] File not found: {args.input}")
        sys.exit(1)

    # --- Read DiagramLayout from .pbix ---
    print(f"[*] Reading DiagramLayout from: {args.input}")
    layout = read_diagram_layout(args.input)
    if layout is None:
        print("[!] No DiagramLayout found. Open in Power BI Desktop first, then re-run.")
        sys.exit(0)

    table_names = extract_table_names(layout)
    if not table_names:
        print("[!] No tables found. Nothing to arrange.")
        sys.exit(0)

    # Classify tables by prefix
    fact_tables, dim_tables, other_tables = classify_tables(
        table_names, fact_prefixes, dim_prefixes
    )

    # --- Generate template mode ---
    if args.generate_relations:
        generate_relations_template(table_names, fact_prefixes, dim_prefixes)
        sys.exit(0)

    # --- Print classification summary ---
    print(f"\n[*] Found {len(table_names)} table(s):\n")
    print(f"    FACT  ({len(fact_tables):>2}): {', '.join(fact_tables) if fact_tables else '(none)'}")
    print(f"    DIM   ({len(dim_tables):>2}): {', '.join(dim_tables) if dim_tables else '(none)'}")
    print(f"    OTHER ({len(other_tables):>2}): {', '.join(other_tables) if other_tables else '(none)'}")

    # --- Load relationships ---
    fact_to_dims = {}
    snowflake    = {}
    orphan_dims  = set(dim_tables)

    if args.relations:
        if not os.path.isfile(args.relations):
            print(f"[ERROR] Relations file not found: {args.relations}")
            sys.exit(1)
        relations = parse_relations(args.relations)
        fact_to_dims, snowflake, orphan_dims = build_adjacency(
            relations, fact_tables, dim_tables
        )
        print(f"\n[*] Loaded {len(relations)} relationship(s) from {args.relations}")
        print(f"    Direct fact→dim links  : {sum(len(v) for v in fact_to_dims.values())}")
        print(f"    Snowflake dim→dim links: {sum(len(v) for v in snowflake.values())}")
        if orphan_dims:
            print(f"    Orphan dims (no link)  : {', '.join(orphan_dims)}")
    else:
        print("\n[!] No --relations file provided. Using simple radial layout.")
        print("    Run with --generate-relations to get a template you can fill in.")

    # --- Compute master layout ---
    node_sizes = extract_node_sizes(layout)
    positions = compute_layout(
        fact_tables, dim_tables, other_tables,
        fact_to_dims, snowflake, orphan_dims,
        radius=args.radius,
        table_width=args.table_width,
        table_height=args.table_height,
        node_sizes=node_sizes
    )

    # --- Print layout plan ---
    all_snowflake_children = set()
    for children in snowflake.values():
        all_snowflake_children.update(children)

    print(f"\n[*] Layout plan:\n")
    print(f"    {'Table':<28} {'Role':<12} {'X':>8}  {'Y':>8}")
    print(f"    {'-'*28} {'-'*12} {'-'*8}  {'-'*8}")
    for name in table_names:
        x, y = positions.get(name, (0, 0))
        if name in fact_tables:
            role = "FACT"
        elif name in all_snowflake_children:
            role = "SNOWFLAKE"
        elif name in dim_tables:
            role = "DIM"
        else:
            role = "OTHER"
        print(f"    {name:<28} {role:<12} {x:>8.1f}  {y:>8.1f}")

    # --- Dry run check ---
    if args.dry_run:
        print("\n[*] Dry run — no changes written.")
        sys.exit(0)

    # --- Determine output path ---
    if args.output:
        output_path = args.output
    else:
        base, ext = os.path.splitext(args.input)
        output_path = f"{base}_arranged{ext}"

    # --- Apply master layout ---
    modified_layout = apply_positions(
        deepcopy(layout), positions, args.table_width, args.table_height
    )
    
    # --- Generate focused tabs if requested ---
    if args.create_tabs:
        print(f"\n[*] Generating diagram tabs (one per fact table)...")
        modified_layout = create_diagram_tabs(
            modified_layout, fact_tables, fact_to_dims, snowflake,
            radius=args.radius,
            table_width=args.table_width,
            table_height=args.table_height,
            node_sizes=node_sizes
        )
        print(f"    Created {len(modified_layout['diagrams'])} diagrams:")
        print(f"      - diagrams[0]: All tables (master view)")
        for i, fact in enumerate(fact_tables, start=1):
            print(f"      - diagrams[{i}]: {fact}")
    
    # --- Encode modified layout ---
    new_json_bytes = json.dumps(modified_layout, indent=2, ensure_ascii=False).encode("utf-16-le")

    # --- Write output file ---
    print(f"\n[*] Repacking → {output_path}")
    repack_pbix(args.input, output_path, {DIAGRAM_LAYOUT_PATH: new_json_bytes})

    print("[✓] Done. Open the new .pbix in Power BI Desktop.\n")
    print("    Tip: if something looks off, delete 'DiagramLayout' from the .pbix ZIP")
    print("    (rename → .zip, delete file, rename back) and let PBI reset it.")


if __name__ == "__main__":
    main()