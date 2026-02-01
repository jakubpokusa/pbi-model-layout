"""
pbix_layout_tool.py  v1.0
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
    """Load and return list of {from, to} dicts from the JSON sidecar."""
    with open(relations_path, 'r') as f:
        rels = json.load(f)
    for r in rels:
        if "from" not in r or "to" not in r:
            raise ValueError(f"Each relationship needs 'from' and 'to' keys. Got: {r}")
    return rels


def build_adjacency(relations, fact_tables, dim_tables):
    """
    From the flat relationship list, build:
        fact_to_dims  : { fact_name: [dim_name, ...] }   — direct fact->dim links
        snowflake     : { parent_dim: [child_dim, ...] } — snowflake links (dim->dim)
        orphan_dims   : dims not reachable from any fact

    Logic: if one side is a fact, it's a star link.
           if both sides are dims, it's a snowflake link.
    """
    fact_set = set(fact_tables)
    dim_set  = set(dim_tables)

    fact_to_dims  = defaultdict(list)
    dim_links     = []          # raw dim-dim pairs, resolved after
    linked_dims   = set()

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
    Layout engine with two modes:

    SINGLE FACT  → classic star: fact in center, dims in a ring around it.
    MULTIPLE FACTS → grid layout:
        - Facts lined up horizontally across the top row.
        - Each fact's dims stacked vertically in a column below it.
        - Shared dims (linked to multiple facts) go in a leftmost column.
        - Snowflake children go directly below their parent dim.

    node_sizes: { name: (w, h) } read from the real DiagramLayout so we
                use PBI's actual card heights (which vary by column count).
    """
    positions = {}
    COL_GAP  = 60   # horizontal gap between columns
    ROW_GAP  = 40   # vertical gap between rows

    def w(name):
        if node_sizes and name in node_sizes:
            return node_sizes[name][0]
        return table_width

    def h(name):
        if node_sizes and name in node_sizes:
            return node_sizes[name][1]
        return table_height

    # Collect snowflake children
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
        positions[fact] = (0, 0)

        dims = fact_to_dims.get(fact, [])
        # Remove snowflake children from ring — they go behind parents
        ring_dims = [d for d in dims if d not in all_snowflake_children]
        n = len(ring_dims)

        for i, dim_name in enumerate(ring_dims):
            angle = math.radians(-90 + (360 * i / max(n, 1)))
            x = radius * math.cos(angle) - w(dim_name) / 2
            y = radius * math.sin(angle) - h(dim_name) / 2
            positions[dim_name] = (x, y)

            # Snowflake children behind parent
            for j, child in enumerate(snowflake.get(dim_name, [])):
                push = SNOWFLAKE_PUSH * (j + 1)
                cx = (radius + push) * math.cos(angle) - w(child) / 2
                cy = (radius + push) * math.sin(angle) - h(child) / 2
                positions[child] = (cx, cy)

        # Orphans in outer ring
        unplaced = [d for d in dim_tables if d not in positions]
        for i, d in enumerate(unplaced):
            angle = math.radians(-90 + (360 * i / max(len(unplaced), 1)))
            positions[d] = (
                OTHER_RING_RADIUS * math.cos(angle) - w(d) / 2,
                OTHER_RING_RADIUS * math.sin(angle) - h(d) / 2
            )

        return positions

    # ---------------------------------------------------------------
    # MULTIPLE FACTS →
    #
    #   [fact_A]
    #   [fact_B]
    #   [fact_C]
    #   [dim_1] [dim_2] [dim_3] ... [snowflake_1] [snowflake_2]
    #
    #   Facts stacked vertically on the left.
    #   All dims in one straight horizontal line below the facts.
    #   Snowflake dims at the end of that line.
    # ---------------------------------------------------------------

    # Fact column width = widest fact card
    fact_col_w = max(w(f) for f in fact_tables_sorted)

    # --- Stack facts vertically ---
    y_cursor = 0
    for f in fact_tables_sorted:
        positions[f] = (0, y_cursor)
        y_cursor += h(f) + ROW_GAP

    # Bottom of the fact block (y_cursor already points there after last gap)
    fact_block_bottom = y_cursor   # includes the last ROW_GAP — that's our spacing

    # --- Build dim row order ---
    # Plain dims first (no snowflake relationship at all).
    # Then snowflake parents, each immediately followed by their children.
    snowflake_parents = set(snowflake.keys())   # dims that HAVE children

    plain_dims = [d for d in dim_tables
                  if d not in all_snowflake_children and d not in snowflake_parents]

    tail = []   # parent + children groups, appended at the end
    for d in dim_tables:
        if d in snowflake_parents:
            tail.append(d)
            tail.extend(snowflake.get(d, []))

    dim_row = plain_dims + tail

    # --- Place dims in a straight horizontal line below all facts ---
    # Start x at fact_col_w + gap so there's clear space from the fact column
    x_cursor = fact_col_w + COL_GAP
    for name in dim_row:
        positions[name] = (x_cursor, fact_block_bottom)
        x_cursor += w(name) + COL_GAP

    # --- "Other" tables → below everything ---
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
    Real PBI DiagramLayout structure:
        { "diagrams": [ { "nodes": [ { "nodeIndex": "table_name", ... }, ... ] } ] }
    """
    if layout is None:
        return []
    nodes = layout.get("diagrams", [{}])[0].get("nodes", [])
    return [n["nodeIndex"] for n in nodes if "nodeIndex" in n]


def apply_positions(layout, positions, table_width, table_height):
    """
    Update node positions in the real PBI structure.
    Preserves each node's existing size (PBI sets these based on column count)
    and all other fields (lineageTag, zIndex, etc).
    Only overwrites location.x and location.y.

    PBI Model View doesn't render negative coordinates, so we shift the
    entire layout so the top-left-most table lands at (50, 50).
    """
    if not positions:
        return layout

    # Shift so minimum x and y both land at 50
    min_x = min(x for x, y in positions.values())
    min_y = min(y for x, y in positions.values())
    offset_x = 50 - min_x
    offset_y = 50 - min_y

    nodes = layout.get("diagrams", [{}])[0].get("nodes", [])
    for node in nodes:
        name = node.get("nodeIndex")
        if name in positions:
            x, y = positions[name]
            node["location"]["x"] = round(x + offset_x, 2)
            node["location"]["y"] = round(y + offset_y, 2)
    return layout


def repack_pbix(original_path, output_path, modified_files):
    with zipfile.ZipFile(original_path, 'r') as zin:
        with zipfile.ZipFile(output_path, 'w') as zout:
            for item in zin.infolist():
                compress = zipfile.ZIP_STORED if item.filename == "[Content_Types].xml" \
                           else zipfile.ZIP_DEFLATED
                data = modified_files.get(item.filename, zin.read(item.filename))
                zout.writestr(item, data, compress_type=compress)

            for path, data in modified_files.items():
                if path not in zin.namelist():
                    zout.writestr(path, data, compress_type=zipfile.ZIP_DEFLATED)


# ---------------------------------------------------------------------------
# .pbit relationship extractor
# ---------------------------------------------------------------------------

def extract_relations_from_pbit(pbit_path, output_path="relations.json", debug=False):
    """
    Open a .pbit, find DataModelSchema, strip the binary prefix,
    parse the JSON, pull out all relationships, and write relations.json.

    Real Power BI .pbit files encode DataModelSchema as UTF-16-LE with
    a BOM prefix.  We try UTF-16-LE first, then fall back to UTF-8
    variants so it works regardless of PBI version.
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

    if debug:
        print(f"\n[DEBUG] File inside .pbit: {schema_file}")
        print(f"[DEBUG] Raw size: {len(raw)} bytes")
        print(f"[DEBUG] First 100 bytes (hex): {raw[:100].hex()}")
        print(f"[DEBUG] First 100 bytes (repr): {repr(raw[:100])}\n")

    schema = None

    # Strategy 1: UTF-16-LE (what real PBI Desktop actually produces)
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

    # Strategy 3: UTF-8, skip any binary prefix before first '{'
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

    # Real PBI uses lowercase "model" and "relationships";
    # older/synthetic files may use "Model" and "Relationships".
    # Key names inside each relationship differ too:
    #   Real PBI:  fromTable / toTable / fromColumn / toColumn
    #   Older:     SourceTable / ReferencedTable / SourceColumn / ReferencedColumn
    model = schema.get("model", schema.get("Model", {}))
    raw_rels = model.get("relationships", model.get("Relationships", []))

    if not raw_rels:
        print("[!] DataModelSchema contains no relationships.")
        print("    Make sure your model has relationships created in Power BI Desktop.")
        return

    # Build the clean relations list + a verbose table for the user
    relations = []
    print(f"\n[*] Found {len(raw_rels)} relationship(s):\n")
    print(f"    {'From':<25} {'To':<25} {'Join columns'}")
    print(f"    {'-'*25} {'-'*25} {'-'*35}")

    for r in raw_rels:
        src_tbl  = r.get("fromTable",  r.get("SourceTable", "?"))
        ref_tbl  = r.get("toTable",    r.get("ReferencedTable", "?"))
        src_col  = r.get("fromColumn", r.get("SourceColumn", "?"))
        ref_col  = r.get("toColumn",   r.get("ReferencedColumn", "?"))
        relations.append({"from": src_tbl, "to": ref_tbl})
        print(f"    {src_tbl:<25} {ref_tbl:<25} {src_col} → {ref_col}")

    # Write output
    with open(output_path, 'w') as f:
        json.dump(relations, f, indent=4)

    print(f"\n[✓] Written {output_path}  ({len(relations)} relationships)")
    print(f"    You can now run:\n")
    print(f"      python pbix_layout_tool.py your_model.pbix --relations {output_path}\n")


# ---------------------------------------------------------------------------
# Template generator
# ---------------------------------------------------------------------------

def generate_relations_template(table_names, fact_prefixes, dim_prefixes):
    fact, dim, _ = classify_tables(table_names, fact_prefixes, dim_prefixes)
    print("\n// relations.json — fill in the actual relationships from your model.")
    print("// Remove any lines that don't apply. Add dim->dim lines for snowflakes.\n")
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
        description="Auto-arrange Power BI model diagram into a star layout (v2).",
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
    parser.add_argument("--generate-relations", action="store_true",
                        help="Print a relations.json template")
    parser.add_argument("--extract-relations", default=None, metavar="PBIT",
                        help="Extract relationships from a .pbit file and write relations.json")
    parser.add_argument("--debug-pbit", action="store_true",
                        help="Show raw bytes of DataModelSchema for troubleshooting")
    args = parser.parse_args()

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

    # --- Read layout ---
    print(f"[*] Reading DiagramLayout from: {args.input}")
    layout = read_diagram_layout(args.input)
    if layout is None:
        print("[!] No DiagramLayout found. Open in Power BI Desktop first, then re-run.")
        sys.exit(0)

    table_names = extract_table_names(layout)
    if not table_names:
        print("[!] No tables found. Nothing to arrange.")
        sys.exit(0)

    fact_tables, dim_tables, other_tables = classify_tables(
        table_names, fact_prefixes, dim_prefixes
    )

    # --- Generate template mode ---
    if args.generate_relations:
        generate_relations_template(table_names, fact_prefixes, dim_prefixes)
        sys.exit(0)

    # --- Print classification ---
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

    # --- Compute layout ---
    node_sizes = extract_node_sizes(layout)
    positions = compute_layout(
        fact_tables, dim_tables, other_tables,
        fact_to_dims, snowflake, orphan_dims,
        radius=args.radius,
        table_width=args.table_width,
        table_height=args.table_height,
        node_sizes=node_sizes
    )

    # --- Print plan ---
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

    if args.dry_run:
        print("\n[*] Dry run — no changes written.")
        sys.exit(0)

    # --- Output path ---
    if args.output:
        output_path = args.output
    else:
        base, ext = os.path.splitext(args.input)
        output_path = f"{base}_arranged{ext}"

    # --- Apply & repack ---
    modified_layout = apply_positions(
        deepcopy(layout), positions, args.table_width, args.table_height
    )
    new_json_bytes = json.dumps(modified_layout, indent=2, ensure_ascii=False).encode("utf-16-le")

    print(f"\n[*] Repacking → {output_path}")
    repack_pbix(args.input, output_path, {DIAGRAM_LAYOUT_PATH: new_json_bytes})

    print("[✓] Done. Open the new .pbix in Power BI Desktop.\n")
    print("    Tip: if something looks off, delete 'DiagramLayout' from the .pbix ZIP")
    print("    (rename → .zip, delete file, rename back) and let PBI reset it.")


if __name__ == "__main__":
    main()
