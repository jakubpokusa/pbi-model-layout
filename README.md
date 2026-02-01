# pbi-model-layout

Automatically arranges Power BI model diagram views into clean, relationship-aware layouts. Detects fact and dimension tables by prefix, reads real node sizes from the `.pbix`, and writes positions back — no manual dragging required.

## Requirements

- Python 3.9+
- No external packages (stdlib only)

## Quick start

```bash
# 1. Extract relationships from your model
python pbix_layout_tool.py --extract-relations your_model.pbit

# 2. Apply the layout
python pbix_layout_tool.py your_model.pbix --relations relations.json
```

Open the generated `your_model_arranged.pbix` in Power BI Desktop.

## How to get the `.pbit`

In Power BI Desktop: **File → Save As → Power BI Template (.pbit)**

The `.pbit` is a ZIP containing a human-readable `DataModelSchema` with all table relationships. The extractor reads that file to build `relations.json`.

## Layout modes

The tool picks a layout automatically based on your model structure:

**Single fact → Star layout**
The fact table sits at the centre, dimension tables are placed in a ring around it. Snowflake children (dims connected to other dims) are pushed outward behind their parent.

**Multiple facts → Grid layout**
```
fct_Orders
fct_Inventory          dim_A  dim_B  dim_C  ...  dim_Parent  dim_Child
fct_WebSessions
```
- Facts stack vertically on the left.
- All dims line up in a single horizontal row below, offset to the right.
- Dims that have snowflake children are pushed to the end of the row, with their children immediately after them.

The tool uses each table's real card height (set by Power BI based on column count) so nothing overlaps.

## Options

| Flag | Default | Description |
|---|---|---|
| `--output FILE` | `input_arranged.pbix` | Output path |
| `--relations FILE` | — | Path to `relations.json` |
| `--fact-prefixes` | `fct_,fact_,FCT_,FACT_` | Comma-separated fact table prefixes |
| `--dim-prefixes` | `dim_,DIM_,Dim_,d_,D_` | Comma-separated dim table prefixes |
| `--radius N` | `520` | Star layout: radius from fact to dim ring |
| `--dry-run` | — | Print layout plan without writing |
| `--extract-relations` | — | Extract relationships from a `.pbit` |
| `--generate-relations` | — | Print a blank `relations.json` template |

## `relations.json` format

```json
[
    { "from": "fct_Orders",  "to": "dim_Customer" },
    { "from": "fct_Orders",  "to": "dim_Product" },
    { "from": "dim_Product", "to": "dim_Category" }
]
```

Each entry is one relationship. `"from"` is the many-side (fact or parent dim), `"to"` is the one-side (dim or child dim). The tool infers which is which from the prefixes, so the direction here is just for readability.

## License

MIT
