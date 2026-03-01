# pbi-model-layout

Automatically arranges Power BI model diagram views into clean, relationship-aware layouts. Detects fact and dimension tables by prefix, reads real node sizes from the `.pbix`, and writes positions back - no manual dragging required.

Available as both a **command-line tool** and a **graphical interface**.

## Requirements

- Python 3.9+
- No external packages (stdlib only)

## Quick Start

### Option 1: Graphical Interface (Recommended)

```bash
python pbi_layout_gui.py
```

The GUI provides:

- Visual preview of layouts before applying
- Multiple layout modes (auto, grid, horizontal, star, vertical stack)
- Interactive drag-and-drop to fine-tune positions
- Zoom and scroll for large models
- Real-time layout switching

### Option 2: Command Line

```bash
# 1. Extract relationships from your model
python pbix_layout_tool.py --extract-relations your_model.pbit

# 2. Apply the layout
python pbix_layout_tool.py your_model.pbix --relations relations.json
```

Open the generated `your_model_arranged.pbix` in Power BI Desktop.

![Before and after](before_and_after.png)

## GUI Features

### Interactive Preview

- **Auto-fit**: Opens with entire model visible
- **Zoom**: Mouse wheel to zoom 20%-300%
- **Drag tables**: Click and drag any table to reposition
- **Scrollbars**: Navigate large diagrams
- **Save Layout**: Explicitly save manual adjustments before applying

### Layout Modes

Switch between different layout strategies in real-time:

- **auto** - Smart layout based on model structure (star for 1 fact, grid for multiple)
- **grid** - Facts vertical left, dims horizontal below
- **horizontal** - Facts horizontal top, dims in columns below each
- **star** - Radial layout with facts at center, dims in rings
- **vertical_stack** - Facts left, dims inline to the right

### Preview Controls

- **Layout dropdown**: Switch layout modes
- **Radius control**: Adjust spacing in star layouts (100-1000px)
- **Zoom display**: Current zoom percentage
- **Refresh**: Recompute layout with new settings
- **Save Layout**: Save current positions (closes preview)
- **Quit without Save**: Discard changes and close
- **Apply This Layout**: Write to `.pbix` file

### Visual Features

- **Color-coded tables**:
  - Blue = Fact tables
  - Red = Dimensions
  - Green = Snowflake dimensions
- **Relationship info boxes**: Shows connections below each dim/snowflake

## How to get the `.pbit`

In Power BI Desktop: **File → Save As → Power BI Template (.pbit)**

The `.pbit` is a ZIP containing a human-readable `DataModelSchema` with all table relationships. The extractor reads that file to build `relations.json`.

## Layout Modes Explained

### Auto Mode

Automatically picks the best layout:

- **Single fact** → Star layout (fact center, dims in ring)
- **Multiple facts** → Grid layout (facts left, dims below)

### Grid Layout

```
fct_Orders
fct_Inventory          dim_A  dim_B  dim_C  ...  dim_Parent  dim_Child
fct_WebSessions
```

Facts stack vertically on the left, all dims line up horizontally below with generous spacing.

### Horizontal Layout

Facts arranged horizontally across the top, each with its dims in a column below.

### Star Layout

Facts at center with dimensions radiating outward in a ring. For multiple facts, creates multiple star clusters.

### Vertical Stack

Facts in left column, dimensions inline to the right (same row), snowflakes below their parent dims.

## Diagram Tabs

Add `--create-tabs` (CLI) or check the option in GUI to generate focused views - one tab per fact table:

```bash
python pbix_layout_tool.py model.pbix --relations relations.json --create-tabs
```

This creates:

- **Diagram 0** (master): All tables in chosen layout
- **Diagram 1-N**: One tab per fact, showing only that fact + connected dims in star layout

Switch between tabs using the diagram selector in Power BI Desktop's Model View (bottom left).

![Tabs feature](tabs_feature.png)

## Command-Line Options

| Flag                   | Default                 | Description                                        |
| ---------------------- | ----------------------- | -------------------------------------------------- |
| `--output FILE`        | `input_arranged.pbix`   | Output path                                        |
| `--relations FILE`     | —                       | Path to `relations.json`                           |
| `--fact-prefixes`      | `fct_,fact_,FCT_,FACT_` | Comma-separated fact table prefixes                |
| `--dim-prefixes`       | `dim_,DIM_,Dim_,d_,D_`  | Comma-separated dim table prefixes                 |
| `--radius N`           | `520`                   | Star layout: radius from fact to dim ring          |
| `--create-tabs`        | —                       | Generate focused diagram tabs (one per fact table) |
| `--extract-relations`  | —                       | Extract relationships from a `.pbit`               |
| `--generate-relations` | —                       | Print a blank `relations.json` template            |

## `relations.json` Format

```json
[
  { "from": "fct_Orders", "to": "dim_Customer" },
  { "from": "fct_Orders", "to": "dim_Product" },
  { "from": "dim_Product", "to": "dim_Category" }
]
```

Each entry is one relationship. `"from"` is the many-side (fact or parent dim), `"to"` is the one-side (dim or child dim). The tool infers which is which from the prefixes, so the direction here is just for readability.

## Workflow Example

1. **Extract relationships**:
   - Open GUI or run `--extract-relations` on your `.pbit`
   - Generates `relations.json`

2. **Preview and adjust**:
   - Open GUI, select your `.pbix` and `relations.json`
   - Click "Preview Layout"
   - Try different layout modes
   - Drag tables to fine-tune positions
   - Click "Save Layout" when satisfied

3. **Apply**:
   - Click "Apply Layout" in main window
   - Output written to `*_arranged.pbix`
   - Open in Power BI Desktop

## Files

- `pbix_layout_tool.py` - Core layout engine (CLI)
- `pbi_layout_gui.py` - Graphical interface
- `relations.json` - Extracted relationships
- `before_and_after.png` - Example screenshot
- `tabs_feature.png` - Tabs feature screenshot

## License

MIT
